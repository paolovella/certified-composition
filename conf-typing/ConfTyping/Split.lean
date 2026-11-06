/-
  **Expression splitting: the one-to-many pass** (F4; the user's decisions of 2026-10-30 and
  2026-11-01). Not Ring 0.

  `x := (a + b) + c` becomes `x := a + b` then `x := x + c`, accumulated in place along the
  whole left spine, whenever the right operand does not read `x`. One source step becomes up to
  `L` target steps (`mlen`), the cost of an assignment grows with its expression, and a partial
  target run can stop in the middle of a chain: the three things that broke `PassCert`'s old
  single equation. No temporaries: at every source-step boundary the target's state is the
  source's.

  The pass's six obligations, about the pass and the language, not about any certificate:
  - `behind`: at every fuel the target's events are a prefix of the source's, its cost at most
    `L` times, and what it finishes the source has finished alike (events, cost, reflection);
  - `ahead`: after `L * n` steps the target has caught up with `n` source steps (progress,
    catch-up);
  - `det_split`: what any observer sees of the target is fixed by what it sees of the source. It rests on two facts about
    `ucmdLangS`, proved here once: a step splits off an observation (`atomS_split`,
    `tickS_split`), and equal observations stay equal at less fuel (`eq_mono`).
  `split_carries`: a `bcheck`-accepted program's four guarantees hold of its split version, by
  the kernel's transfer theorems alone. Witnesses: `exProg_expands` (cost 2 becomes 4),
  `no_naive_pass` (splitting without the guard reads a different resource, so no certified pass
  can compile to it).
-/
import ConfTyping.UStep
import ConfTyping.P1

namespace ConfTyping.Split

/-- `x := e`, its left-nested sum accumulated in place: `x := (a + b) + c` becomes `x := a + b`
    then `x := x + c`, whenever `c` does not read `x` (otherwise that level is left whole). -/
def splitX (x : String) : Expr → UCmd
  | .add (.add a b) c =>
      if x ∈ evars c then .assign x (.add (.add a b) c)
      else .seq (splitX x (.add a b)) (.assign x (.add (.var x) c))
  | e => .assign x e

/-- **Expression splitting**: every assignment, its expression accumulated in place. -/
def split : UCmd → UCmd
  | .assign x e  => splitX x e
  | .seq a b     => .seq (split a) (split b)
  | .ite e a b   => .ite e (split a) (split b)
  | .loop e b    => .loop e (split b)
  | c            => c

/-- The target frames for source frames. -/
def tF : List UFrame → List UFrame
  | []          => []
  | (c, p) :: k => push (split c) p (tF k)

theorem tF_push : ∀ (c : UCmd) (p : List Nat) (k : List UFrame),
    tF (push c p k) = push (split c) p (tF k)
  | .seq a b, p, k => by
    simp only [push, split]
    rw [tF_push a, tF_push b]
  | .skip, _, _ | .assign _ _, _, _ | .check _, _, _ | .access _, _, _ | .memop _ _, _, _
  | .sop _ _ _, _, _ | .hop _ _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ => by
    simp [push, tF]

theorem evalE_upd_other : ∀ (e : Expr) {x : String} (v : Int) (σ : Store), x ∉ evars e →
    evalE e (upd σ x v) = evalE e σ
  | .num _, _, _, _, _ => rfl
  | .var y, x, v, σ, h => by
    have : y ≠ x := fun h' => h (by simp [evars, h'])
    simp [evalE, upd, this]
  | .add a b, x, v, σ, h => by
    simp only [evars, List.mem_append, not_or] at h
    simp only [evalE, evalE_upd_other a v σ h.1, evalE_upd_other b v σ h.2]

/-! ## The chain an assignment becomes -/

/-- How many steps `x := e` takes after splitting. -/
def len (x : String) : Expr → Nat
  | .add (.add a b) c => if x ∈ evars c then 1 else len x (.add a b) + 1
  | _ => 1

/-- The final assignment of a chain level, as one step. -/
theorem assign_step (π : MedPolicy) (x : String) (e : Expr) (q : List Nat) (K : List UFrame)
    (n : Nat) (t : UState) (hd : t.dead = false) :
    (urunS π (n + 1) ((.assign x e, q) :: K) t).st =
      (urunS π n K { t with store := upd t.store x (evalE e t.store) }).st ∧
    (urunS π (n + 1) ((.assign x e, q) :: K) t).cost =
      1 + (urunS π n K { t with store := upd t.store x (evalE e t.store) }).cost ∧
    (urunS π (n + 1) ((.assign x e, q) :: K) t).ev =
      (urunS π n K { t with store := upd t.store x (evalE e t.store) }).ev ∧
    (urunS π (n + 1) ((.assign x e, q) :: K) t).out =
      (urunS π n K { t with store := upd t.store x (evalE e t.store) }).out ∧
    (urunS π (n + 1) ((.assign x e, q) :: K) t).lk =
      stepMk q :: (urunS π n K { t with store := upd t.store x (evalE e t.store) }).lk := by
  rw [runS_atomic rfl q n π K hd]
  simp only [TRun.atomS, stepT, uexec, hd, Bool.false_eq_true, ↓reduceIte, uaddrs,
    Option.getD_some, List.map_nil, stepEv, List.nil_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- The markers a chain leaves: one per step, at its position. -/
def marks (x : String) : Expr → List Nat → List LCore.Lk
  | .add (.add a b) c, q =>
      if x ∈ evars c then [stepMk q] else marks x (.add a b) (q ++ [0]) ++ [stepMk (q ++ [1])]
  | _, q => [stepMk q]

theorem upd_upd (σ : Store) (x : String) (v w : Int) : upd (upd σ x v) x w = upd σ x w := by
  funext y; simp only [upd]; split <;> rfl

/-- **The chain does what the assignment does.** From a live state, `len x e` steps of the split
    assignment show no events, cost `len x e`, and end in exactly the state the source's one
    assignment ends in; then the frames `K` run from there. -/
theorem chain_full (π : MedPolicy) (x : String) : ∀ (e : Expr) (q : List Nat) (K : List UFrame)
    (n : Nat) (t : UState), t.dead = false →
    let R := urunS π (len x e + n) (push (splitX x e) q K) t
    let K' := urunS π n K { t with store := upd t.store x (evalE e t.store) }
    R.st = K'.st ∧ R.cost = len x e + K'.cost ∧ R.ev = K'.ev ∧ R.out = K'.out ∧
      R.lk = marks x e q ++ K'.lk
  | .add (.add a b) c, q, K, n, t, hd => by
    by_cases hx : x ∈ evars c
    · simp only [splitX, len, marks, hx, ↓reduceIte, push]
      rw [Nat.add_comm 1 n]
      exact assign_step π x _ q K n t hd
    · simp only [splitX, len, marks, hx, ↓reduceIte, push]
      have h₁ := chain_full π x (.add a b) (q ++ [0]) ((.assign x (.add (.var x) c), q ++ [1]) :: K)
        (n + 1) t hd
      have h₂ := assign_step π x (.add (.var x) c) (q ++ [1]) K n
        { t with store := upd t.store x (evalE (.add a b) t.store) } hd
      have hv : evalE (.add (.var x) c) (upd t.store x (evalE (.add a b) t.store))
          = evalE (.add (.add a b) c) t.store := by
        simp only [evalE, evalE_upd_other c _ _ hx]; simp [upd]
      simp only [hv, upd_upd] at h₂
      obtain ⟨a1, a2, a3, a4, a5⟩ := h₁
      obtain ⟨b1, b2, b3, b4, b5⟩ := h₂
      have hf : len x (.add a b) + 1 + n = len x (.add a b) + (n + 1) := by omega
      rw [hf]
      exact ⟨a1.trans b1, by rw [a2, b2]; omega, a3.trans b3, a4.trans b4,
        by rw [a5, b5, List.append_assoc]; rfl⟩
  | .num v, q, K, n, t, hd => by
    simp only [splitX, len, marks, push]; rw [Nat.add_comm 1 n]; exact assign_step π x _ q K n t hd
  | .var y, q, K, n, t, hd => by
    simp only [splitX, len, marks, push]; rw [Nat.add_comm 1 n]; exact assign_step π x _ q K n t hd
  | .add (.num v) c, q, K, n, t, hd => by
    simp only [splitX, len, marks, push]; rw [Nat.add_comm 1 n]; exact assign_step π x _ q K n t hd
  | .add (.var y) c, q, K, n, t, hd => by
    simp only [splitX, len, marks, push]; rw [Nat.add_comm 1 n]; exact assign_step π x _ q K n t hd

/-- An observation, without the state. -/
def obs (r : TRun) : List LCore.Ev × List LCore.Lk × Nat × LCore.Outcome := (r.ev, r.lk, r.cost, r.out)

/-- What one observer sees of a run (`LCore.Beh.view`). -/
def obsV (f : LCore.Observer) (r : TRun) : List LCore.Ev × List LCore.Lk × Nat × LCore.Outcome :=
  (r.ev.filter (fun e => f e.chan), r.lk, r.cost, r.out)

theorem obsV_of_obs {f : LCore.Observer} {a b : TRun} (h : obs a = obs b) : obsV f a = obsV f b := by
  simp only [obs, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [obsV, h1, h2, h3, h4]

/-- One assignment step stopped by the fuel. -/
theorem assign_fuel0 (π : MedPolicy) (x : String) (e : Expr) (q : List Nat) (K : List UFrame)
    (t : UState) : obs (urunS π 0 ((.assign x e, q) :: K) t) = ([], [], 0, .fuel) := rfl

/-- **A chain stopped by the fuel**: no events, out of fuel, cost the fuel spent, and leakage
    that depends only on the chain and the fuel, not on the state. -/
theorem chain_partial (π : MedPolicy) (x : String) : ∀ (e : Expr) (q : List Nat) (K : List UFrame)
    (m : Nat) (t t' : UState), t.dead = false → t'.dead = false → m < len x e →
    obs (urunS π m (push (splitX x e) q K) t) = obs (urunS π m (push (splitX x e) q K) t') ∧
    (urunS π m (push (splitX x e) q K) t).ev = [] ∧
    (urunS π m (push (splitX x e) q K) t).out = .fuel ∧
    (urunS π m (push (splitX x e) q K) t).cost = m
  | .add (.add a b) c, q, K, m, t, t', hd, hd', hm => by
    by_cases hx : x ∈ evars c
    · simp only [len, hx, ↓reduceIte] at hm
      obtain rfl : m = 0 := by omega
      simp only [splitX, hx, ↓reduceIte, push]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [len, hx, ↓reduceIte] at hm
      simp only [splitX, hx, ↓reduceIte, push]
      by_cases hlt : m < len x (.add a b)
      · exact chain_partial π x (.add a b) (q ++ [0]) _ m t t' hd hd' hlt
      · obtain rfl : m = len x (.add a b) := by omega
        have h₁ := chain_full π x (.add a b) (q ++ [0]) ((.assign x (.add (.var x) c), q ++ [1]) :: K)
          0 t hd
        have h₁' := chain_full π x (.add a b) (q ++ [0]) ((.assign x (.add (.var x) c), q ++ [1]) :: K)
          0 t' hd'
        simp only [Nat.add_zero] at h₁ h₁'
        obtain ⟨_, a2, a3, a4, a5⟩ := h₁
        obtain ⟨_, b2, b3, b4, b5⟩ := h₁'
        simp only [urunS] at a2 a3 a4 a5 b2 b3 b4 b5
        refine ⟨?_, a3, a4, by rw [a2, Nat.add_zero]⟩
        simp only [obs]; rw [a2, a3, a4, a5, b2, b3, b4, b5]
  | .num v, q, K, m, t, t', _, _, hm => by
    simp only [len] at hm; obtain rfl : m = 0 := by omega
    exact ⟨rfl, rfl, rfl, rfl⟩
  | .var y, q, K, m, t, t', _, _, hm => by
    simp only [len] at hm; obtain rfl : m = 0 := by omega
    exact ⟨rfl, rfl, rfl, rfl⟩
  | .add (.num v) c, q, K, m, t, t', _, _, hm => by
    simp only [len] at hm; obtain rfl : m = 0 := by omega
    exact ⟨rfl, rfl, rfl, rfl⟩
  | .add (.var y) c, q, K, m, t, t', _, _, hm => by
    simp only [len] at hm; obtain rfl : m = 0 := by omega
    exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The target is behind the source -/

/-- The longest chain in a command. -/
def mlen : UCmd → Nat
  | .assign x e => len x e
  | .seq a b    => max (mlen a) (mlen b)
  | .ite _ a b  => max (mlen a) (mlen b)
  | .loop _ b   => mlen b
  | _           => 1

/-- Every frame's chains are at most `L` long. -/
def FB (L : Nat) (k : List UFrame) : Prop := ∀ f ∈ k, mlen f.1 ≤ L

theorem push_fb {L : Nat} : ∀ (c : UCmd) (p : List Nat) (k : List UFrame), mlen c ≤ L → FB L k →
    FB L (push c p k)
  | .seq a b, p, k, hc, hk => by
    simp only [mlen, Nat.max_le] at hc
    exact push_fb a _ _ hc.1 (push_fb b _ k hc.2 hk)
  | .skip, _, k, hc, hk | .assign _ _, _, k, hc, hk | .check _, _, k, hc, hk
  | .access _, _, k, hc, hk | .memop _ _, _, k, hc, hk | .sop _ _ _, _, k, hc, hk
  | .hop _ _ _, _, k, hc, hk | .ite _ _ _, _, k, hc, hk | .loop _ _, _, k, hc, hk => by
    intro f hf; simp only [push, List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hc
    · exact hk f hf

theorem push_ne_nil : ∀ (c : UCmd) (p : List Nat) (k : List UFrame), push c p k ≠ []
  | .seq a b, p, k => push_ne_nil a _ _
  | .skip, _, _ | .assign _ _, _, _ | .check _, _, _ | .access _, _, _ | .memop _ _, _, _
  | .sop _ _ _, _, _ | .hop _ _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ => by simp [push]

theorem urunS_nonempty_zero (π : MedPolicy) {k : List UFrame} (hk : k ≠ []) (s : UState) :
    urunS π 0 k s = ⟨s, 0, [], [], .fuel⟩ := by
  cases k with
  | nil => exact absurd rfl hk
  | cons f k => rfl

theorem urunS_nonempty_dead (π : MedPolicy) {k : List UFrame} (hk : k ≠ []) (n : Nat) {s : UState}
    (hd : s.dead = true) : urunS π (n + 1) k s = ⟨s, 0, [], [], .abort⟩ := by
  cases k with
  | nil => exact absurd rfl hk
  | cons f k => obtain ⟨c, p⟩ := f; simp [urunS, hd]

theorem len_pos (x : String) : ∀ e, 1 ≤ len x e
  | .add (.add a b) c => by simp only [len]; split <;> omega
  | .num _ | .var _ | .add (.num _) _ | .add (.var _) _ => by simp [len]

/-- What "behind" means at one fuel: the target's events are a prefix of the source's, its cost
    at most `L` times the source's, and what it finishes the source has finished alike. -/
def Behind (L : Nat) (T S : TRun) : Prop :=
  T.ev <+: S.ev ∧ T.cost ≤ L * S.cost ∧ (T.out ≠ .fuel → S.out = T.out ∧ S.ev = T.ev)

theorem Behind.tickS {L : Nat} {T S : TRun} (hL : 1 ≤ L) (l : LCore.Lk) (p : List Nat)
    (h : Behind L T S) : Behind L (T.tickS l p) (S.tickS l p) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, ?_, fun hf => h3 hf⟩
  simp only [TRun.tickS, Nat.mul_add, Nat.mul_one]; omega

theorem Behind.atomS {L : Nat} (hL : 1 ≤ L) (a : TRun) (p : List Nat) {K K' : UState → TRun}
    (h : a.out = .done → Behind L (K a.st) (K' a.st)) : Behind L (a.atomS p K) (a.atomS p K') := by
  unfold TRun.atomS
  by_cases ha : a.out = .done
  · obtain ⟨h1, h2, h3⟩ := h ha
    simp only [ha, ↓reduceIte]
    refine ⟨prefix_append_both _ h1, ?_, fun hf => ?_⟩
    · have : a.cost ≤ L * a.cost := Nat.le_mul_of_pos_left _ (by omega)
      show a.cost + (K a.st).cost ≤ L * (a.cost + (K' a.st).cost)
      rw [Nat.mul_add]; omega
    · obtain ⟨r1, r2⟩ := h3 hf; exact ⟨r1, by rw [r2]⟩
  · simp only [ha, ↓reduceIte]
    refine ⟨LCore.prefix_refl' _, Nat.le_mul_of_pos_left _ (by omega), fun _ => ⟨rfl, rfl⟩⟩

/-- **The split program is behind the source program at every fuel.** -/
theorem behind (π : MedPolicy) (L : Nat) (hL : 1 ≤ L) : ∀ (m : Nat) (k : List UFrame)
    (s : UState), NoSeq k → FB L k → Behind L (urunS π m (tF k) s) (urunS π m k s) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro k s hk hb
  cases k with
  | nil => exact ⟨LCore.prefix_refl' _, by cases m <;> simp [tF, urunS], fun _ => ⟨rfl, rfl⟩⟩
  | cons f k' =>
    obtain ⟨c, p⟩ := f
    have hne : tF ((c, p) :: k') ≠ [] := push_ne_nil _ _ _
    have hk' : NoSeq k' := fun x hx => hk x (List.mem_cons_of_mem _ hx)
    have hb' : FB L k' := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hc : mlen c ≤ L := hb _ List.mem_cons_self
    cases m with
    | zero =>
      rw [urunS_nonempty_zero π hne]
      exact ⟨List.nil_prefix, Nat.zero_le _, fun h => absurd rfl h⟩
    | succ m =>
      by_cases hd : s.dead = true
      · rw [urunS_nonempty_dead π hne m hd]
        simp only [urunS, hd, ↓reduceIte]
        exact ⟨List.nil_prefix, Nat.zero_le _, fun _ => ⟨rfl, rfl⟩⟩
      have hd0 : s.dead = false := by simpa using hd
      cases c with
      | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
      | assign x e =>
        obtain ⟨_, a2, a3, a4, _⟩ := assign_step π x e p k' m s hd0
        simp only [tF, split]
        have hlenL : len x e ≤ L := hc
        by_cases hlen : len x e ≤ m + 1
        · obtain ⟨j, hj⟩ : ∃ j, m + 1 = len x e + j := ⟨m + 1 - len x e, by omega⟩
          have hT := chain_full π x e p (tF k') j s hd0
          rw [← hj] at hT
          obtain ⟨_, t2, t3, t4, _⟩ := hT
          have hI := ih j (by have := len_pos x e; omega) k'
            { s with store := upd s.store x (evalE e s.store) } hk' hb'
          obtain ⟨i1, i2, i3⟩ := hI
          have hx := runS_ext π j m k' { s with store := upd s.store x (evalE e s.store) }
            (by have := len_pos x e; omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [t3, a3]; exact LCore.prefix_trans' i1 hx.2.1
          · rw [t2, a2, Nat.mul_add, Nat.mul_one]
            have := hx.2.2.2
            have : L * (urunS π j k' { s with store := upd s.store x (evalE e s.store) }).cost
                ≤ L * (urunS π m k' { s with store := upd s.store x (evalE e s.store) }).cost :=
              Nat.mul_le_mul_left _ this
            omega
          · intro hf
            rw [t4] at hf
            obtain ⟨r1, r2⟩ := i3 hf
            have hfin : (urunS π j k' { s with store := upd s.store x (evalE e s.store) }).out ≠ .fuel := by
              rw [r1]; exact hf
            have hs := hx.1 hfin
            rw [a4, a3, t4, t3, ← hs, r1, r2]
            exact ⟨rfl, rfl⟩
        · have hp := chain_partial π x e p (tF k') (m + 1) s s hd0 hd0 (by omega)
          obtain ⟨_, p2, p3, p4⟩ := hp
          refine ⟨by rw [p2]; exact List.nil_prefix, ?_, fun h => absurd p3 h⟩
          rw [p4, a2]
          have : L ≤ L * (1 + (urunS π m k' { s with store := upd s.store x (evalE e s.store) }).cost) :=
            Nat.le_mul_of_pos_right _ (by omega)
          omega
      | ite e a b =>
        have hab : mlen a ≤ L ∧ mlen b ≤ L := by simpa [mlen, Nat.max_le] using hc
        simp only [tF, split, push, urunS, hd0, Bool.false_eq_true, ↓reduceIte]
        apply Behind.tickS hL
        by_cases hg : evalE e s.store ≠ 0
        · simp only [ite_eq_left hg]
          rw [← tF_push]
          exact ih m (by omega) _ s (push_noSeq _ _ _ hk') (push_fb _ _ _ hab.1 hb')
        · simp only [ite_eq_right hg]
          rw [← tF_push]
          exact ih m (by omega) _ s (push_noSeq _ _ _ hk') (push_fb _ _ _ hab.2 hb')
      | loop e b =>
        have hbL : mlen b ≤ L := hc
        simp only [tF, split, push, urunS, hd0, Bool.false_eq_true, ↓reduceIte]
        split
        · apply Behind.tickS hL
          have hfr : push (split b) (p ++ [0]) ((UCmd.loop e (split b), p) :: tF k')
              = tF (push b (p ++ [0]) ((UCmd.loop e b, p) :: k')) := by
            rw [tF_push]; rfl
          rw [hfr]
          have hk2 : NoSeq ((UCmd.loop e b, p) :: k') := by
            intro x hx a' b'; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · exact hk' x hx a' b'
          have hb2 : FB L ((UCmd.loop e b, p) :: k') := by
            intro x hx; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hc
            · exact hb' x hx
          exact ih m (by omega) _ s (push_noSeq _ _ _ hk2) (push_fb _ _ _ hbL hb2)
        · exact Behind.tickS hL _ _ (ih m (by omega) k' s hk' hb')
      | _ =>
        simp only [tF, split, push]
        rw [runS_atomic rfl p m π _ hd0, runS_atomic rfl p m π _ hd0]
        exact Behind.atomS hL _ p (fun _ => ih m (by omega) k' _ hk' hb')

/-! ## The target catches up -/

/-- What "ahead" means: the target has reached the source's events, and whatever the source
    finished, the target has finished alike. -/
def Ahead (S T : TRun) : Prop := S.ev <+: T.ev ∧ (S.out ≠ .fuel → T.out = S.out ∧ T.ev = S.ev)

/-- More fuel keeps a run ahead. -/
theorem Ahead.mono {S T T' : TRun} (h : Ahead S T) (hx : T.Ext T') : Ahead S T' := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨LCore.prefix_trans' h1 hx.2.1, fun hf => ?_⟩
  obtain ⟨r1, r2⟩ := h2 hf
  have := hx.1 (by rw [r1]; exact hf)
  rw [← this]; exact ⟨r1, r2⟩

/-- **After `L * n` steps the split program has caught up with `n` source steps.** -/
theorem ahead (π : MedPolicy) (L : Nat) (hL : 1 ≤ L) : ∀ (n : Nat) (k : List UFrame)
    (s : UState), NoSeq k → FB L k → Ahead (urunS π n k s) (urunS π (L * n) (tF k) s) := by
  intro n
  induction n with
  | zero =>
    intro k s _ _
    cases k with
    | nil => exact ⟨LCore.prefix_refl' _, fun _ => ⟨rfl, rfl⟩⟩
    | cons f k => exact ⟨List.nil_prefix, fun h => absurd rfl h⟩
  | succ n ih =>
    intro k s hk hb
    cases k with
    | nil => simp only [tF]; cases L * (n + 1) <;> exact ⟨LCore.prefix_refl' _, fun _ => ⟨rfl, rfl⟩⟩
    | cons f k' =>
      obtain ⟨c, p⟩ := f
      have hne : tF ((c, p) :: k') ≠ [] := push_ne_nil _ _ _
      have hk' : NoSeq k' := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      have hb' : FB L k' := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      have hc : mlen c ≤ L := hb _ List.mem_cons_self
      have hfuel : L * (n + 1) = (L * n + (L - 1)) + 1 := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      by_cases hd : s.dead = true
      · rw [hfuel, urunS_nonempty_dead π hne _ hd]
        simp only [urunS, hd, ↓reduceIte]
        exact ⟨LCore.prefix_refl' _, fun _ => ⟨rfl, rfl⟩⟩
      have hd0 : s.dead = false := by simpa using hd
      have hmono : ∀ (K : List UFrame) (t : UState), (urunS π (L * n) K t).Ext
          (urunS π (L * n + (L - 1)) K t) := fun K t => runS_ext π _ _ K t (by omega)
      cases c with
      | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
      | assign x e =>
        obtain ⟨_, _, a3, a4, _⟩ := assign_step π x e p k' n s hd0
        simp only [tF, split]
        have hlenL : len x e ≤ L := hc
        obtain ⟨j, hj⟩ : ∃ j, L * (n + 1) = len x e + j := ⟨L * (n + 1) - len x e, by
          rw [Nat.mul_add, Nat.mul_one]; omega⟩
        have hT := chain_full π x e p (tF k') j s hd0
        rw [← hj] at hT
        obtain ⟨_, _, t3, t4, _⟩ := hT
        have hI := (ih k' { s with store := upd s.store x (evalE e s.store) } hk' hb').mono
          (runS_ext π (L * n) j _ _ (by rw [Nat.mul_add, Nat.mul_one] at hj; omega))
        obtain ⟨i1, i2⟩ := hI
        refine ⟨by rw [a3, t3]; exact i1, fun hf => ?_⟩
        rw [a4] at hf
        obtain ⟨r1, r2⟩ := i2 hf
        exact ⟨by rw [t4, r1, a4], by rw [t3, r2, a3]⟩
      | ite e a b =>
        have hab : mlen a ≤ L ∧ mlen b ≤ L := by simpa [mlen, Nat.max_le] using hc
        rw [hfuel]
        simp only [tF, split, push, urunS, hd0, Bool.false_eq_true, ↓reduceIte]
        by_cases hg : evalE e s.store ≠ 0
        · simp only [ite_eq_left hg]
          rw [← tF_push]
          obtain ⟨i1, i2⟩ := (ih _ s (push_noSeq _ _ _ hk') (push_fb _ _ _ hab.1 hb')).mono (hmono _ _)
          exact ⟨i1, fun hf => i2 hf⟩
        · simp only [ite_eq_right hg]
          rw [← tF_push]
          obtain ⟨i1, i2⟩ := (ih _ s (push_noSeq _ _ _ hk') (push_fb _ _ _ hab.2 hb')).mono (hmono _ _)
          exact ⟨i1, fun hf => i2 hf⟩
      | loop e b =>
        have hbL : mlen b ≤ L := hc
        rw [hfuel]
        simp only [tF, split, push, urunS, hd0, Bool.false_eq_true, ↓reduceIte]
        split
        · have hfr : push (split b) (p ++ [0]) ((UCmd.loop e (split b), p) :: tF k')
              = tF (push b (p ++ [0]) ((UCmd.loop e b, p) :: k')) := by
            rw [tF_push]; rfl
          rw [hfr]
          have hk2 : NoSeq ((UCmd.loop e b, p) :: k') := by
            intro x hx a' b'; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · exact hk' x hx a' b'
          have hb2 : FB L ((UCmd.loop e b, p) :: k') := by
            intro x hx; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact hc
            · exact hb' x hx
          obtain ⟨i1, i2⟩ := (ih _ s (push_noSeq _ _ _ hk2) (push_fb _ _ _ hbL hb2)).mono (hmono _ _)
          exact ⟨i1, fun hf => i2 hf⟩
        · obtain ⟨i1, i2⟩ := (ih k' s hk' hb').mono (hmono _ _)
          exact ⟨i1, fun hf => i2 hf⟩
      | _ =>
        rw [hfuel]
        simp only [tF, split, push]
        rw [runS_atomic rfl p n π _ hd0, runS_atomic rfl p _ π _ hd0]
        unfold TRun.atomS
        split
        · obtain ⟨i1, i2⟩ := (ih k' _ hk' hb').mono (hmono _ _)
          exact ⟨prefix_append_both _ i1, fun hf => by obtain ⟨r1, r2⟩ := i2 hf; exact ⟨r1, by dsimp only; rw [r2]⟩⟩
        · exact ⟨LCore.prefix_refl' _, fun _ => ⟨rfl, rfl⟩⟩

/-! ## Splitting a step off an observation (facts about `ucmdLangS`, not about the pass) -/

/-- How many addresses an atomic command leaks. -/
def addrCount : UCmd → Nat
  | .memop _ _ | .hop _ _ _ => 1
  | _ => 0

/-- How many events an atomic command shows when it does not fault. -/
def evCount : UCmd → Nat
  | .check _ | .access _ => 1
  | .sop .emit _ _ => 1
  | _ => 0

set_option hygiene false in
local macro "cnt_tac" : tactic =>
  `(tactic| (simp only [stepT, uexec, uaddrs, stepEv, hd, Bool.false_eq_true, ↓reduceIte] at * <;>
     (repeat (split at *)) <;> simp_all [addrCount, evCount]))

theorem stepT_lk_len {c : UCmd} (hc : atomic c = true) (π : MedPolicy) {s : UState}
    (hd : s.dead = false) : (stepT c π s).lk.length = addrCount c := by
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> cnt_tac
  | hop op x y => cases op <;> cnt_tac
  | sop op x e => cases op <;> cnt_tac
  | _ => cnt_tac

theorem stepT_ev_len {c : UCmd} (hc : atomic c = true) (π : MedPolicy) {s : UState}
    (hd : s.dead = false) (hdone : (stepT c π s).out = .done) :
    (stepT c π s).ev.length = evCount c := by
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> cnt_tac
  | hop op x y => cases op <;> cnt_tac
  | sop op x e => cases op <;> cnt_tac
  | _ => cnt_tac

/-- The channels an atomic command's events are on: a function of the command alone. -/
def cmdChans : UCmd → List LCore.Chan
  | .check r => [.check r]
  | .access r => [.read r]
  | .sop .emit x _ => [.emit x]
  | _ => []

/-- **A finished step's channels are fixed by its command**, so an observer sees the same number
    of its events from any two states. This is why an observer that chooses channels, not
    payloads, can be carried through a one-to-many pass. -/
theorem stepT_view_len (f : LCore.Observer) {c : UCmd} (hc : atomic c = true) (π : MedPolicy)
    {s : UState} (hd : s.dead = false) (hdone : (stepT c π s).out = .done) :
    ((stepT c π s).ev.filter (fun e => f e.chan)).length = ((cmdChans c).filter f).length := by
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> cnt_tac <;> simp [cmdChans]
  | hop op x y => cases op <;> cnt_tac <;> simp [cmdChans]
  | sop op x e =>
    cases op <;> cnt_tac <;> all_goals
      (simp [cmdChans, LCore.Ev.chan, List.filter]; try (split <;> rfl))
  | _ =>
    cnt_tac <;> all_goals
      (simp [cmdChans, LCore.Ev.chan, List.filter]; try (split <;> rfl))

theorem stepT_done_alive {c : UCmd} {π : MedPolicy} {s : UState}
    (h : (stepT c π s).out = .done) : (stepT c π s).st.dead = false := by
  unfold stepT at *; split at h
  · rename_i r _; by_cases hr : r.1.dead = true
    · simp [hr] at h
    · simpa using hr
  · cases h

/-- A run's first step leaves its marker. -/
theorem first_lk (π : MedPolicy) {c : UCmd} {p : List Nat} {k : List UFrame} {s : UState}
    (hk : NoSeq ((c, p) :: k)) (hd : s.dead = false) (n : Nat) :
    (urunS π (n + 1) ((c, p) :: k) s).lk ≠ [] := by
  cases c with
  | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
  | ite e a b => simp [urunS, hd, TRun.tickS]
  | loop e b => simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]; split <;> simp [TRun.tickS]
  | _ =>
    rw [runS_atomic rfl p n π k hd]; unfold TRun.atomS; split <;> simp

/-- A live run that aborts has left a marker. -/
theorem abort_lk (π : MedPolicy) : ∀ (n : Nat) (k : List UFrame) (s : UState), NoSeq k →
    s.dead = false → (urunS π n k s).out = .abort → (urunS π n k s).lk ≠ []
  | 0, [], _, _, _, h => by simp [urunS] at h
  | 0, _ :: _, _, _, _, h => by simp [urunS] at h
  | _ + 1, [], _, _, _, h => by simp [urunS] at h
  | n + 1, (c, p) :: k, s, hk, hd, _ => first_lk π hk hd n

/-- An observation without the state. -/
theorem obs_eq {a b : TRun} : obs a = obs b ↔ a.ev = b.ev ∧ a.lk = b.lk ∧ a.cost = b.cost ∧ a.out = b.out := by
  simp [obs]

theorem append_split {α} {a a' b b' : List α} (h : a ++ b = a' ++ b') (hl : a.length = a'.length) :
    a = a' ∧ b = b' := List.append_inj h hl

variable {f : LCore.Observer}

/-- **Splitting a branch step off.** -/
theorem tickS_split {l l' : LCore.Lk} {p : List Nat} {R R' : TRun}
    (h : obsV f (R.tickS l p) = obsV f (R'.tickS l' p)) : l = l' ∧ obsV f R = obsV f R' := by
  simp only [obsV, TRun.tickS, Prod.mk.injEq, List.cons.injEq, Nat.add_left_cancel_iff] at h
  obtain ⟨he, ⟨_, hl, hlk⟩, hc, ho⟩ := h
  exact ⟨hl, by simp [obsV, he, hlk, hc, ho]⟩

theorem uexec1_some {c : UCmd} (hc : atomic c = true) (π : MedPolicy) (t : UState) :
    uexec 1 c π t ≠ none := by
  cases c <;> simp_all [atomic, uexec]

theorem stepT_out_cases {c : UCmd} (hc : atomic c = true) (π : MedPolicy) (t : UState) :
    (stepT c π t).out = .done ∨ (stepT c π t).out = .abort := by
  have := stepT_ne (uexec1_some hc π t)
  cases h : (stepT c π t).out <;> simp_all

/-- **Splitting an atomic step off.** Two runs of the same atomic command from live states,
    whose whole observations agree, agree on the step and, if it finished, on what followed. -/
theorem atomS_split {c : UCmd} (hc : atomic c = true) {π : MedPolicy} {s s' : UState}
    (hd : s.dead = false) (hd' : s'.dead = false) {p : List Nat} {K K' : UState → TRun}
    (hK : ∀ t, t.dead = false → (K t).out = .abort → (K t).lk ≠ [])
    (hK' : ∀ t, t.dead = false → (K' t).out = .abort → (K' t).lk ≠ [])
    (h : obsV f ((stepT c π s).atomS p K) = obsV f ((stepT c π s').atomS p K')) :
    obsV f (stepT c π s) = obsV f (stepT c π s') ∧
    ((stepT c π s).out = .done → obsV f (K (stepT c π s).st) = obsV f (K' (stepT c π s').st)) := by
  have hl := (stepT_lk_len hc π hd).trans (stepT_lk_len hc π hd').symm
  have hc1 := (stepT_cost_one c hc π s).trans (stepT_cost_one c hc π s').symm
  unfold TRun.atomS at h
  rcases stepT_out_cases hc π s with ha | ha <;> rcases stepT_out_cases hc π s' with ha' | ha'
  · simp only [ha, ha', ↓reduceIte, obsV, Prod.mk.injEq, List.cons_append, List.cons.injEq,
      true_and, List.filter_append] at h
    obtain ⟨he, hlk, hcost, ho⟩ := h
    have hev := (stepT_view_len f hc π hd ha).trans (stepT_view_len f hc π hd' ha').symm
    obtain ⟨e1, e2⟩ := append_split he hev
    obtain ⟨l1, l2⟩ := append_split hlk hl
    refine ⟨by simp [obsV, e1, l1, hc1, ha, ha'], fun _ => ?_⟩
    simp only [obsV, e2, l2, ho, Prod.mk.injEq, and_true, true_and]
    rw [hc1] at hcost; omega
  · exfalso
    simp [ha, ha', obsV] at h
    obtain ⟨_, hlk, _, ho⟩ := h
    have hlen := congrArg List.length hlk
    simp only [List.length_append] at hlen
    have : (K (stepT c π s).st).lk = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact hK _ (stepT_done_alive ha) ho this
  · exfalso
    simp [ha, ha', obsV] at h
    obtain ⟨_, hlk, _, ho⟩ := h
    have hlen := congrArg List.length hlk
    simp only [List.length_append] at hlen
    have : (K' (stepT c π s').st).lk = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact hK' _ (stepT_done_alive ha') ho.symm this
  · simp [ha, ha', obsV] at h
    obtain ⟨he, hlk, hcost⟩ := h
    exact ⟨by simp [obsV, he, hlk, hcost, ha, ha'], fun hd => by rw [ha] at hd; cases hd⟩

theorem tickS_obs {l : LCore.Lk} {p : List Nat} {R R' : TRun} (h : obsV f R = obsV f R') :
    obsV f (R.tickS l p) = obsV f (R'.tickS l p) := by
  simp only [obsV, Prod.mk.injEq] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp [TRun.tickS, h1, h2, h3, h4]

theorem atomS_obs {a a' : TRun} {p : List Nat} {K K' : UState → TRun} (h : obsV f a = obsV f a')
    (hk : a.out = .done → obsV f (K a.st) = obsV f (K' a'.st)) :
    obsV f (a.atomS p K) = obsV f (a'.atomS p K') := by
  simp only [obsV, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold TRun.atomS
  by_cases ha : a.out = .done
  · have ha' : a'.out = .done := h4 ▸ ha
    have := hk ha
    simp only [obsV, Prod.mk.injEq] at this
    obtain ⟨k1, k2, k3, k4⟩ := this
    simp [ha, ha', obsV, h1, h2, h3, k1, k2, k3, k4]
  · have ha' : ¬ a'.out = .done := h4 ▸ ha
    simp [ha', obsV, h1, h2, h3, h4]

/-- Equal observations at one fuel mean equally dead or alive at the start. -/
theorem dead_agree (π : MedPolicy) {c : UCmd} {p : List Nat} {k : List UFrame} {s s' : UState}
    (hk : NoSeq ((c, p) :: k)) (n : Nat)
    (h : obsV f (urunS π (n + 1) ((c, p) :: k) s) = obsV f (urunS π (n + 1) ((c, p) :: k) s')) :
    s.dead = s'.dead := by
  by_cases hd : s.dead = true <;> by_cases hd' : s'.dead = true
  · rw [hd, hd']
  · exfalso
    have hl := first_lk π hk (by simpa using hd') n
    simp only [obsV, Prod.mk.injEq] at h
    rw [← h.2.1] at hl
    simp [urunS, hd] at hl
  · exfalso
    have hl := first_lk π hk (by simpa using hd) n
    simp only [obsV, Prod.mk.injEq] at h
    rw [h.2.1] at hl
    simp [urunS, hd'] at hl
  · simp_all

/-- **Equality at less fuel.** Two runs of the same frames whose observations agree at fuel `m`
    agree at every smaller fuel. A fact about `ucmdLangS`, used by every pass's determinacy. -/
theorem eq_mono (π : MedPolicy) : ∀ (m' m : Nat) (k : List UFrame) (s s' : UState), NoSeq k →
    m' ≤ m → obsV f (urunS π m k s) = obsV f (urunS π m k s') →
    obsV f (urunS π m' k s) = obsV f (urunS π m' k s') := by
  intro m'
  induction m' with
  | zero => intro m k s s' _ _ _; cases k <;> rfl
  | succ m' ih =>
    intro m k s s' hk hle h
    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
    cases k with
    | nil => rfl
    | cons f k' =>
      obtain ⟨c, p⟩ := f
      have hk' : NoSeq k' := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      have hdd := dead_agree π hk m0 h
      by_cases hd : s.dead = true
      · have hd' : s'.dead = true := hdd ▸ hd
        simp [urunS, hd, hd', obsV]
      have hd0 : s.dead = false := by simpa using hd
      have hd0' : s'.dead = false := hdd ▸ hd0
      cases c with
      | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
      | ite e a b =>
        simp only [urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨hb, hr⟩ := tickS_split h
        simp only [LCore.Lk.branch.injEq, decide_eq_decide] at hb
        rw [show decide (evalE e s.store ≠ 0) = decide (evalE e s'.store ≠ 0) from
          decide_eq_decide.mpr hb]
        by_cases hg : evalE e s.store ≠ 0
        · have hg' : evalE e s'.store ≠ 0 := hb.mp hg
          simp only [ite_eq_left hg, ite_eq_left hg'] at hr ⊢
          exact tickS_obs (ih m0 _ s s' (push_noSeq _ _ _ hk') (by omega) hr)
        · have hg' : ¬ evalE e s'.store ≠ 0 := fun h' => hg (hb.mpr h')
          simp only [ite_eq_right hg, ite_eq_right hg'] at hr ⊢
          exact tickS_obs (ih m0 _ s s' (push_noSeq _ _ _ hk') (by omega) hr)
      | loop e b =>
        have hk2 : NoSeq ((UCmd.loop e b, p) :: k') := by
          intro x hx a' b'; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · exact hk' x hx a' b'
        simp only [urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases hg : evalE e s.store ≠ 0 <;> by_cases hg' : evalE e s'.store ≠ 0
        · simp only [ite_eq_left hg, ite_eq_left hg'] at h ⊢
          exact tickS_obs (ih m0 _ s s' (push_noSeq _ _ _ hk2) (by omega) (tickS_split h).2)
        · simp only [ite_eq_left hg, ite_eq_right hg'] at h
          exact absurd (tickS_split h).1 (by simp)
        · simp only [ite_eq_right hg, ite_eq_left hg'] at h
          exact absurd (tickS_split h).1 (by simp)
        · simp only [ite_eq_right hg, ite_eq_right hg'] at h ⊢
          exact tickS_obs (ih m0 _ s s' hk' (by omega) (tickS_split h).2)
      | _ =>
        rw [runS_atomic rfl p m0 π k' hd0, runS_atomic rfl p m0 π k' hd0'] at h
        rw [runS_atomic rfl p m' π k' hd0, runS_atomic rfl p m' π k' hd0']
        obtain ⟨h1, h2⟩ := atomS_split rfl hd0 hd0'
          (fun t ht => abort_lk π m0 k' t hk' ht) (fun t ht => abort_lk π m0 k' t hk' ht) h
        exact atomS_obs h1 (fun hdone => ih m0 k' _ _ hk' (by omega) (h2 hdone))

/-! ## Determinacy -/

/-- **The split program's observation is fixed by the source's.** Two source runs with equal
    observations at fuel `m` give split runs with equal observations at fuel `m`. -/
theorem det_split (π : MedPolicy) (L : Nat) : ∀ (m : Nat) (k : List UFrame) (s s' : UState),
    NoSeq k → FB L k → obsV f (urunS π m k s) = obsV f (urunS π m k s') →
    obsV f (urunS π m (tF k) s) = obsV f (urunS π m (tF k) s') := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro k s s' hk hb h
  cases k with
  | nil => simp only [tF]; cases m <;> rfl
  | cons f k' =>
    obtain ⟨c, p⟩ := f
    have hne : tF ((c, p) :: k') ≠ [] := push_ne_nil _ _ _
    have hk' : NoSeq k' := fun x hx => hk x (List.mem_cons_of_mem _ hx)
    have hb' : FB L k' := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hc : mlen c ≤ L := hb _ List.mem_cons_self
    cases m with
    | zero => rw [urunS_nonempty_zero π hne, urunS_nonempty_zero π hne]; rfl
    | succ m =>
      have hdd := dead_agree π hk m h
      by_cases hd : s.dead = true
      · have hd' : s'.dead = true := hdd ▸ hd
        rw [urunS_nonempty_dead π hne m hd, urunS_nonempty_dead π hne m hd']; rfl
      have hd0 : s.dead = false := by simpa using hd
      have hd0' : s'.dead = false := hdd ▸ hd0
      cases c with
      | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
      | assign x e =>
        obtain ⟨_, a2, a3, a4, a5⟩ := assign_step π x e p k' m s hd0
        obtain ⟨_, b2, b3, b4, b5⟩ := assign_step π x e p k' m s' hd0'
        have hrest : obsV f (urunS π m k' { s with store := upd s.store x (evalE e s.store) }) =
            obsV f (urunS π m k' { s' with store := upd s'.store x (evalE e s'.store) }) := by
          simp only [obsV, Prod.mk.injEq] at h ⊢
          obtain ⟨h1, h2, h3, h4⟩ := h
          refine ⟨by rw [← a3, ← b3, h1], ?_, by rw [a2, b2] at h3; omega, by rw [← a4, ← b4, h4]⟩
          rw [a5, b5] at h2; exact (List.cons.inj h2).2
        simp only [tF, split]
        by_cases hlen : len x e ≤ m + 1
        · obtain ⟨j, hj⟩ : ∃ j, m + 1 = len x e + j := ⟨m + 1 - len x e, by omega⟩
          have hT := chain_full π x e p (tF k') j s hd0
          have hT' := chain_full π x e p (tF k') j s' hd0'
          rw [← hj] at hT hT'
          obtain ⟨_, t2, t3, t4, t5⟩ := hT
          obtain ⟨_, u2, u3, u4, u5⟩ := hT'
          have hI := ih j (by have := len_pos x e; omega) k' _ _ hk' hb'
            (eq_mono π j m k' _ _ hk' (by have := len_pos x e; omega) hrest)
          simp only [obsV, Prod.mk.injEq] at hI ⊢
          obtain ⟨i1, i2, i3, i4⟩ := hI
          exact ⟨by rw [t3, u3, i1], by rw [t5, u5, i2], by rw [t2, u2, i3], by rw [t4, u4, i4]⟩
        · exact obsV_of_obs (chain_partial π x e p (tF k') (m + 1) s s' hd0 hd0' (by omega)).1
      | ite e a b =>
        have hab : mlen a ≤ L ∧ mlen b ≤ L := by simpa [mlen, Nat.max_le] using hc
        simp only [urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte] at h
        simp only [tF, split, push, urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte]
        obtain ⟨hbit, hr⟩ := tickS_split h
        simp only [LCore.Lk.branch.injEq, decide_eq_decide] at hbit
        rw [show decide (evalE e s.store ≠ 0) = decide (evalE e s'.store ≠ 0) from
          decide_eq_decide.mpr hbit]
        by_cases hg : evalE e s.store ≠ 0
        · have hg' : evalE e s'.store ≠ 0 := hbit.mp hg
          simp only [ite_eq_left hg, ite_eq_left hg'] at hr ⊢
          rw [← tF_push]
          exact tickS_obs (ih m (by omega) _ s s' (push_noSeq _ _ _ hk') (push_fb _ _ _ hab.1 hb') hr)
        · have hg' : ¬ evalE e s'.store ≠ 0 := fun h' => hg (hbit.mpr h')
          simp only [ite_eq_right hg, ite_eq_right hg'] at hr ⊢
          rw [← tF_push]
          exact tickS_obs (ih m (by omega) _ s s' (push_noSeq _ _ _ hk') (push_fb _ _ _ hab.2 hb') hr)
      | loop e b =>
        have hbL : mlen b ≤ L := hc
        have hk2 : NoSeq ((UCmd.loop e b, p) :: k') := by
          intro x hx a' b'; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · exact hk' x hx a' b'
        have hb2 : FB L ((UCmd.loop e b, p) :: k') := by
          intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact hc
          · exact hb' x hx
        have hfr : push (split b) (p ++ [0]) ((UCmd.loop e (split b), p) :: tF k')
            = tF (push b (p ++ [0]) ((UCmd.loop e b, p) :: k')) := by
          rw [tF_push]; rfl
        simp only [urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte] at h
        simp only [tF, split, push, urunS, hd0, hd0', Bool.false_eq_true, ↓reduceIte]
        by_cases hg : evalE e s.store ≠ 0 <;> by_cases hg' : evalE e s'.store ≠ 0
        · simp only [ite_eq_left hg, ite_eq_left hg'] at h ⊢
          rw [hfr]
          exact tickS_obs (ih m (by omega) _ s s' (push_noSeq _ _ _ hk2) (push_fb _ _ _ hbL hb2)
            (tickS_split h).2)
        · simp only [ite_eq_left hg, ite_eq_right hg'] at h
          exact absurd (tickS_split h).1 (by simp)
        · simp only [ite_eq_right hg, ite_eq_left hg'] at h
          exact absurd (tickS_split h).1 (by simp)
        · simp only [ite_eq_right hg, ite_eq_right hg'] at h ⊢
          exact tickS_obs (ih m (by omega) k' s s' hk' hb' (tickS_split h).2)
      | _ =>
        rw [runS_atomic rfl p m π k' hd0, runS_atomic rfl p m π k' hd0'] at h
        simp only [tF, split, push]
        rw [runS_atomic rfl p m π _ hd0, runS_atomic rfl p m π _ hd0']
        obtain ⟨h1, h2⟩ := atomS_split rfl hd0 hd0'
          (fun t ht => abort_lk π m k' t hk' ht) (fun t ht => abort_lk π m k' t hk' ht) h
        exact atomS_obs h1 (fun hdone => ih m (by omega) k' _ _ hk' hb' (h2 hdone))

/-! ## The certified pass -/

/-- The cost transformer: at most `L` target steps per source step. -/
def scale (L : Nat) : LCore.Xform where
  lk l := l
  cost c := L * c
  fuel m := m
  costMono _ _ h := Nat.mul_le_mul_left _ h

theorem tF_start (c : UCmd) : tF (push c [] []) = push (split c) [] [] := by
  rw [tF_push]; rfl

theorem start_ok (c : UCmd) : NoSeq (push c [] []) ∧ FB (max 1 (mlen c)) (push c [] []) :=
  ⟨push_noSeq c [] [] (by simp [NoSeq]),
   push_fb c [] [] (Nat.le_max_right _ _) (by simp [FB])⟩

section obligations
variable (π : MedPolicy) (c : UCmd) (σ σ' : Store)

abbrev Lc : Nat := max 1 (mlen c)

theorem split_ev (m : Nat) : (urunS π m (push (split c) [] []) (initU σ)).ev <+:
    (urunS π m (push c [] []) (initU σ)).ev := by
  have := (behind π (Lc c) (Nat.le_max_left _ _) m _ (initU σ) (start_ok c).1 (start_ok c).2).1
  rwa [tF_start] at this

theorem split_cost (m : Nat) : (urunS π m (push (split c) [] []) (initU σ)).cost ≤
    Lc c * (urunS π m (push c [] []) (initU σ)).cost := by
  have := (behind π (Lc c) (Nat.le_max_left _ _) m _ (initU σ) (start_ok c).1 (start_ok c).2).2.1
  rwa [tF_start] at this

theorem split_det (m : Nat)
    (h : obsV f (urunS π m (push c [] []) (initU σ)) = obsV f (urunS π m (push c [] []) (initU σ'))) :
    obsV f (urunS π m (push (split c) [] []) (initU σ)) =
      obsV f (urunS π m (push (split c) [] []) (initU σ')) := by
  have := det_split π (Lc c) m _ _ _ (start_ok c).1 (start_ok c).2 h
  rwa [tF_start] at this

theorem split_ahead (n : Nat) : Ahead (urunS π n (push c [] []) (initU σ))
    (urunS π (Lc c * n) (push (split c) [] []) (initU σ)) := by
  have := ahead π (Lc c) (Nat.le_max_left _ _) n _ (initU σ) (start_ok c).1 (start_ok c).2
  rwa [tF_start] at this

theorem split_reflect (m : Nat) (hf : (urunS π m (push (split c) [] []) (initU σ)).out ≠ .fuel) :
    (urunS π m (push c [] []) (initU σ)).out = (urunS π m (push (split c) [] []) (initU σ)).out ∧
    (urunS π m (push c [] []) (initU σ)).ev = (urunS π m (push (split c) [] []) (initU σ)).ev := by
  have := (behind π (Lc c) (Nat.le_max_left _ _) m _ (initU σ) (start_ok c).1 (start_ok c).2).2.2
  rw [tF_start] at this; exact this hf

end obligations

/-- **Expression splitting, certified**: a `PassCert` from `ucmdLangS` to itself in which one
    source step becomes up to `L` target steps. Its six obligations are `behind` (events, cost,
    reflection), `det_split` (determinacy), and `ahead` (progress, catch-up). -/
def splitPass (P : Partition) (π : MedPolicy) : LCore.PassCert (ucmdLangS P π) (ucmdLangS P π) where
  comp c := .ok (split c, scale (Lc c))
  enc σ := σ
  enc_adm _ _ := trivial
  cover u _ := ⟨u, trivial, rfl⟩
  low_cover u u' _ _ h := ⟨u, u', trivial, trivial, h, rfl, rfl⟩
  ev_sim c p' t h m σ _ := by cases h; exact split_ev π c σ m
  cost_sim c p' t h m σ _ := by cases h; exact split_cost π c σ m
  det c p' t h f m σ σ' _ _ he := by
    cases h
    have hs : obsV f (urunS π m (push c [] []) (initU σ)) = obsV f (urunS π m (push c [] []) (initU σ')) := by
      simp only [ucmdLangS, LCore.Beh.view, LCore.Beh.mk.injEq] at he
      obtain ⟨h1, h2, h3, h4⟩ := he
      simp only [obsV, scale] at h1 h2 h3 h4 ⊢
      rw [h1, h2, h3, h4]
    have := split_det π c σ σ' m hs
    simp only [obsV, Prod.mk.injEq] at this
    simp only [ucmdLangS, LCore.Beh.view, LCore.Beh.mk.injEq]
    exact this
  progress c p' t h n σ _ hf := by
    cases h
    obtain ⟨_, h2⟩ := split_ahead π c σ n
    exact ⟨_, (h2 hf).1, (h2 hf).2⟩
  catch_up c p' t h n σ _ := by
    cases h; exact ⟨_, (split_ahead π c σ n).1⟩
  reflect c p' t h m σ _ hf := by
    cases h
    obtain ⟨r1, r2⟩ := split_reflect π c σ m hf
    exact ⟨m, r1, r2⟩

/-! ## The payoff: certificates through a one-to-many pass, by the transfers alone -/

/-- **`split_carries`.** A program `bcheck` accepts keeps its budget (scaled by the longest chain),
    its mediation, its memory safety and its noninterference after expression splitting, by the
    kernel's transfer theorems alone: no proof here about any certificate and the pass together. -/
theorem split_carries {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS P π) (Lc c * k) (split c)
  ∧ LCore.Cert.trace (ucmdLangS P π) (mediated π) (split c)
  ∧ LCore.Cert.trace (ucmdLangS P π) (fun evs => faultEv ∉ evs) (split c)
  ∧ LCore.Cert.rel (ucmdLangS P π) (split c) := by
  obtain ⟨hb, hm, hf, hr⟩ := bcheck_lcoreS h π
  exact ⟨(splitPass P π).bound_transfer rfl hb,
         (splitPass P π).trace_transfer rfl (mediated_prefixClosed π) hm,
         (splitPass P π).trace_transfer rfl faultFree_prefixClosed hf,
         (splitPass P π).rel_transfer rfl hr⟩

/-! ## Witnesses -/

/-- `x := ((a + 1) + 2) + 3`, then `skip`. -/
def exProg : UCmd :=
  .seq (.assign "x" (.add (.add (.add (.var "a") (.num 1)) (.num 2)) (.num 3))) .skip

/-- **The pass really is one-to-many**: the assignment becomes three steps, so the split program
    costs 4 where the source costs 2, and it finishes. -/
theorem exProg_expands :
    ((ucmdLangS Psec (fun _ => true)).run 20 exProg (fun _ => 0)).cost = 2
  ∧ ((ucmdLangS Psec (fun _ => true)).run 20 (split exProg) (fun _ => 0)).cost = 4
  ∧ ((ucmdLangS Psec (fun _ => true)).run 20 (split exProg) (fun _ => 0)).out = .done := by
  decide

theorem exProg_checks : (bcheck Psec [] [] exProg).isSome = true := by decide

/-- Splitting without the guard: `x := (b + c)` level by level even when `c` reads `x`. -/
def naiveX (x : String) : Expr → UCmd
  | .add (.add a b) c => .seq (naiveX x (.add a b)) (.assign x (.add (.var x) c))
  | e => .assign x e

/-- `x := (x + 1) + x`, then read `a` if `x ≠ 3` and `b` otherwise. -/
def badProg : UCmd :=
  .seq (.assign "x" (.add (.add (.var "x") (.num 1)) (.var "x")))
    (.ite (.add (.var "x") (.num (-3))) (.access "a") (.access "b"))

def badSplit : UCmd :=
  .seq (naiveX "x" (.add (.add (.var "x") (.num 1)) (.var "x")))
    (.ite (.add (.var "x") (.num (-3))) (.access "a") (.access "b"))

/-- From `x = 1` the source computes `x = 3` and reads `b`; the naive split computes `x = 4` and
    reads `a`. Its events are not a prefix of the source's. -/
theorem badSplit_diverges :
    ¬ ((ucmdLangS Psec (fun _ => true)).run 20 badSplit (fun v => if v = "x" then 1 else 0)).ev <+:
      ((ucmdLangS Psec (fun _ => true)).run 20 badProg (fun v => if v = "x" then 1 else 0)).ev := by
  decide

/-- **The guard is load-bearing**: no certified pass compiles `badProg` to its naive split. -/
theorem no_naive_pass (pc : LCore.PassCert (ucmdLangS Psec (fun _ => true)) (ucmdLangS Psec (fun _ => true)))
    {t : LCore.Xform} (h : pc.comp badProg = .ok (badSplit, t)) (he : pc.enc = id) (hf : t.fuel = id) :
    False := by
  have := pc.ev_sim badProg badSplit t h 20 (fun v => if v = "x" then 1 else 0) trivial
  rw [he, hf] at this
  exact badSplit_diverges this

end ConfTyping.Split
