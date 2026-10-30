/-
  **UCmd on step fuel** (F4, the user's decision of 2026-10-30). Not Ring 0.

  `uexecT`'s fuel bounds nesting depth, so for a pass where one source step becomes several
  target steps, where a target run is at fuel `m` depends on program structure and path, and the
  pass's determinacy would need a replay proof every time. Here fuel counts steps of a frame
  machine (`urunS`): each atomic command, branch or loop test is one step and costs 1, and
  unfolding a `seq` (`push`) is free. Every step leaves a marker (`stepMk`) in the leakage, so a
  run's position is visible in its observation. Events, branch bits, addresses, faults and
  halting abort are `uexecT`'s, in the same order.

  - `ucmdLangS_lawful`: the kernel's laws, with divergence constant 0 (a run out of fuel at `n`
    has cost `n`).
  - `runS_agree`: the step machine replays every finished `uexecT` run exactly (markers aside).
  - Budget, mediation and memory safety by reduction: a `bcheck`-accepted program's `uexecT`
    run finishes, every step run is a prefix of it, and the certificates are prefix-closed.
  - Noninterference in lockstep over typed frame stacks (`runS_same`), reusing port 4's
    `stepT_same` and `jrel_done`.
  - `bcheck_lcoreS`: the four guarantees on `ucmdLangS`, over every run.
-/
import ConfTyping.NiT

namespace ConfTyping

/-- The marker every step leaves in the leakage: where the step boundaries are. -/
def stepMk : LCore.Lk := .ext "step" 0

/-- Push a command onto the frame stack, flattening sequences: a `seq` is never a frame, and
    unfolding one costs no step. -/
def push : UCmd → List UCmd → List UCmd
  | .seq a b, k => push a (push b k)
  | c,        k => c :: k

/-- One counted step that shows a marker and a branch bit, in front of `r`. -/
def TRun.tickS (l : LCore.Lk) (r : TRun) : TRun :=
  ⟨r.st, 1 + r.cost, r.ev, stepMk :: l :: r.lk, r.out⟩

/-- An atomic step, then (if it finished) `r` from where it stopped. -/
def TRun.atomS (a : TRun) (k : UState → TRun) : TRun :=
  if a.out = .done then
    let b := k a.st
    ⟨b.st, a.cost + b.cost, a.ev ++ b.ev, stepMk :: a.lk ++ b.lk, b.out⟩
  else ⟨a.st, a.cost, a.ev, stepMk :: a.lk, a.out⟩

/-- **Small-step UCmd** with halting abort: `n` steps of the frame machine. Each step is one
    atomic command, branch or loop test, and costs 1. -/
def urunS (π : MedPolicy) : Nat → List UCmd → UState → TRun
  | _,     [],     s => ⟨s, 0, [], [], .done⟩
  | 0,     _ :: _, s => ⟨s, 0, [], [], .fuel⟩
  | n + 1, c :: k, s =>
    if s.dead then ⟨s, 0, [], [], .abort⟩ else
    match c with
    | .seq a b => urunS π n (push a (push b k)) s
    | .ite e a b =>
        TRun.tickS (.branch (decide (evalE e s.store ≠ 0)))
          (urunS π n (push (if evalE e s.store ≠ 0 then a else b) k) s)
    | .loop e b =>
        if evalE e s.store ≠ 0 then
          TRun.tickS (.branch true) (urunS π n (push b (.loop e b :: k)) s)
        else TRun.tickS (.branch false) (urunS π n k s)
    | c => (stepT c π s).atomS (fun t => urunS π n k t)

/-- **UCmd on step fuel** as an L `Lang`. -/
def ucmdLangS (P : Partition) (π : MedPolicy) : LCore.Lang where
  Prog  := UCmd
  In    := Store
  lowIn := lowEq P
  run n c σ :=
    let r := urunS π n (push c []) (initU σ)
    { ev := r.ev, lk := r.lk, cost := r.cost, out := r.out }

/-! ## Lawful -/

theorem TRun.tickS_ext {a a' : TRun} (l : LCore.Lk) (h : a.Ext a') : (a.tickS l).Ext (a'.tickS l) := by
  refine ⟨fun hf => ?_, h.2.1, ?_, Nat.add_le_add_left h.2.2.2 _⟩
  · rw [h.1 hf]
  · obtain ⟨t, ht⟩ := h.2.2.1
    exact ⟨t, by simp only [TRun.tickS, List.cons_append, ht]⟩

theorem TRun.atomS_ext (a : TRun) {k k' : UState → TRun}
    (hk : a.out = .done → (k a.st).Ext (k' a.st)) : (a.atomS k).Ext (a.atomS k') := by
  unfold TRun.atomS
  by_cases ha : a.out = .done
  · obtain ⟨h1, h2, h3, h4⟩ := hk ha
    simp only [ha, ↓reduceIte]
    refine ⟨fun hf => ?_, prefix_append_both _ h2, ?_, Nat.add_le_add_left h4 _⟩
    · rw [h1 hf]
    · simpa only [List.cons_append] using
        (show stepMk :: (a.lk ++ (k a.st).lk) <+: stepMk :: (a.lk ++ (k' a.st).lk) from by
          obtain ⟨t, ht⟩ := prefix_append_both a.lk h3
          exact ⟨t, by simp only [List.cons_append, ht]⟩)
  · simp only [ha, ↓reduceIte]; exact TRun.Ext.refl _

/-- **More fuel only extends a step run.** -/
theorem runS_ext (π : MedPolicy) : ∀ (n n' : Nat) (k : List UCmd) (s : UState), n ≤ n' →
    (urunS π n k s).Ext (urunS π n' k s) := by
  intro n
  induction n with
  | zero =>
    intro n' k s _
    cases k with
    | nil => cases n' <;> exact TRun.Ext.refl _
    | cons c k => exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' k s hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | nil => exact TRun.Ext.refl _
    | cons c k =>
      by_cases hd : s.dead = true
      · simp only [urunS, hd, ↓reduceIte]; exact TRun.Ext.refl _
      cases c with
      | seq a b => simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]; exact ih m' _ s hm
      | ite e a b =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]; exact TRun.tickS_ext _ (ih m' _ s hm)
      | loop e b =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]
        split
        · exact TRun.tickS_ext _ (ih m' _ s hm)
        · exact TRun.tickS_ext _ (ih m' _ s hm)
      | _ =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte]
        exact TRun.atomS_ext _ (fun _ => ih m' _ _ hm)

/-- No frame is a `seq`. -/
def NoSeq (k : List UCmd) : Prop := ∀ c ∈ k, ∀ a b, c ≠ .seq a b

theorem push_noSeq : ∀ (c : UCmd) (k : List UCmd), NoSeq k → NoSeq (push c k)
  | .seq a b, k, h => push_noSeq a _ (push_noSeq b k h)
  | .skip, k, h | .assign _ _, k, h | .check _, k, h | .access _, k, h | .memop _ _, k, h
  | .sop _ _ _, k, h | .hop _ _ _, k, h | .ite _ _ _, k, h | .loop _ _, k, h => by
    intro c hc a b; simp only [push, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp
    · exact h c hc a b

set_option hygiene false in
local macro "one_tac" : tactic =>
  `(tactic| (simp only [stepT, uexec] <;> (repeat (split)) <;> simp_all))

/-- An atomic step costs exactly 1. -/
theorem stepT_cost_one (c : UCmd) (hc : atomic c = true) (π : MedPolicy) (s : UState) :
    (stepT c π s).cost = 1 := by
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> one_tac
  | hop op x y => cases op <;> one_tac
  | sop op x e => cases op <;> one_tac
  | _ => one_tac

/-- **A step run out of fuel at `n` has cost `n`.** -/
theorem runS_diverge (π : MedPolicy) : ∀ (n : Nat) (k : List UCmd) (s : UState), NoSeq k →
    (urunS π n k s).out = .fuel → n ≤ (urunS π n k s).cost := by
  intro n
  induction n with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro k s hk hf
    cases k with
    | nil => simp [urunS] at hf
    | cons c k =>
      have hk' : NoSeq k := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      by_cases hd : s.dead = true
      · simp [urunS, hd] at hf
      cases c with
      | seq a b => exact absurd rfl (hk _ (List.mem_cons_self) a b)
      | ite e a b =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte, TRun.tickS] at hf ⊢
        have := ih _ s (push_noSeq _ _ hk') hf; omega
      | loop e b =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte] at hf ⊢
        split at hf
        · rename_i hg; rw [ite_eq_left hg]; simp only [TRun.tickS] at hf ⊢
          have hk2 : NoSeq (UCmd.loop e b :: k) := by
            intro x hx a' b'; simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · simp
            · exact hk' x hx a' b'
          have := ih _ s (push_noSeq _ _ hk2) hf
          omega
        · rename_i hg; rw [ite_eq_right hg]; simp only [TRun.tickS] at hf ⊢
          have := ih _ s hk' hf; omega
      | _ =>
        simp only [urunS, hd, Bool.false_eq_true, ↓reduceIte, TRun.atomS] at hf ⊢
        split at hf
        · rename_i hdone; simp only [hdone, ↓reduceIte] at hf ⊢
          have := ih _ _ hk' hf
          rw [stepT_cost_one _ rfl]; omega
        · rename_i hdone; simp only [hdone, ↓reduceIte] at hf ⊢
          exact absurd hf (stepT_ne (by simp [uexec]))

theorem ucmdLangS_lawful (P : Partition) (π : MedPolicy) : (ucmdLangS P π).Lawful where
  ev_mono c σ n n' h := (runS_ext π n n' _ _ h).2.1
  lk_mono c σ n n' h := (runS_ext π n n' _ _ h).2.2.1
  cost_mono c σ n n' h := (runS_ext π n n' _ _ h).2.2.2
  stable c σ n n' h hf := by
    have := (runS_ext π n n' (push c []) (initU σ) h).1 hf
    show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
    rw [this]
  diverge c := ⟨0, fun n σ h =>
    runS_diverge π n (push c []) (initU σ) (push_noSeq c [] (by simp [NoSeq])) h⟩

/-! ## Agreement with `uexecT` -/

/-- The leakage without the step markers. -/
def stripMk (l : List LCore.Lk) : List LCore.Lk := l.filter (· != stepMk)

theorem stripMk_cons_mk (l : List LCore.Lk) : stripMk (stepMk :: l) = stripMk l := by
  simp [stripMk]

theorem stripMk_cons_branch (b : Bool) (l : List LCore.Lk) :
    stripMk (.branch b :: l) = .branch b :: stripMk l := by
  simp [stripMk, stepMk]

theorem stripMk_append (a b : List LCore.Lk) : stripMk (a ++ b) = stripMk a ++ stripMk b := by
  simp [stripMk, List.filter_append]

theorem stripMk_addrs (l : List Int) : stripMk (l.map LCore.Lk.addr) = l.map LCore.Lk.addr := by
  induction l with
  | nil => rfl
  | cons a l _ => simp [stripMk, stepMk]

/-- An atomic step's leakage is addresses only, so the markers' removal leaves it alone. -/
theorem stripMk_stepT (c : UCmd) (π : MedPolicy) (s : UState) :
    stripMk (stepT c π s).lk = (stepT c π s).lk := by
  unfold stepT; split
  · exact stripMk_addrs _
  · rfl

/-- `R` is the record `r` followed by `K`, with the step markers removed from `R`'s leakage. -/
def Agree (R r K : TRun) : Prop :=
  R.st = K.st ∧ R.cost = r.cost + K.cost ∧ R.ev = r.ev ++ K.ev ∧
  stripMk R.lk = r.lk ++ stripMk K.lk ∧ R.out = K.out

/-- What follows a finished record: the rest of the frames if it finished normally, nothing if
    it aborted. -/
def tailS (π : MedPolicy) (n : Nat) (k : List UCmd) (r : TRun) : TRun :=
  if r.out = .done then urunS π n k r.st else ⟨r.st, 0, [], [], r.out⟩

theorem agree_tick {R r K : TRun} (b : Bool) (h : Agree R r K) :
    Agree (R.tickS (.branch b)) (r.tick (.branch b)) K := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, ?_, h3, ?_, h5⟩
  · simp only [TRun.tickS, TRun.tick, h2]; omega
  · simp only [TRun.tickS, TRun.tick, stripMk_cons_mk, stripMk_cons_branch, h4, List.cons_append]

theorem agree_seq {R R' r₁ r₂ K : TRun} (h₁ : Agree R r₁ R') (h₂ : Agree R' r₂ K) :
    Agree R ⟨r₂.st, r₁.cost + r₂.cost, r₁.ev ++ r₂.ev, r₁.lk ++ r₂.lk, r₂.out⟩ K := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h₁
  obtain ⟨b1, b2, b3, b4, b5⟩ := h₂
  refine ⟨a1.trans b1, ?_, ?_, ?_, a5.trans b5⟩
  · simp only; rw [a2, b2]; omega
  · simp only; rw [a3, b3, List.append_assoc]
  · simp only; rw [a4, b4, List.append_assoc]

theorem uexecT_done_alive : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState),
    (uexecT n c π s).out = .done → (uexecT n c π s).st.dead = false := by
  intro n
  induction n with
  | zero => intro _ _ _ h; cases h
  | succ m ih =>
    intro c π s h
    cases c with
    | seq c₁ c₂ =>
      simp only [uexecT] at h ⊢; split at h
      · cases h
      · rename_i hd; simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        obtain ⟨_, hb, he⟩ := TRun.seqT_done h
        rw [he]; exact ih _ _ _ hb
    | ite e c₁ c₂ =>
      simp only [uexecT] at h ⊢; split at h
      · cases h
      · rename_i hd; simp only [hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at h ⊢
        exact ih _ _ _ h
    | loop e b =>
      simp only [uexecT] at h ⊢; split at h
      · cases h
      · rename_i hd; simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        split at h
        · rename_i hg; rw [ite_eq_left hg]; simp only [TRun.tick] at h ⊢
          obtain ⟨_, hb, he⟩ := TRun.seqT_done h
          rw [he]; exact ih _ _ _ hb
        · rename_i hg; rw [ite_eq_right hg]; simpa using hd
    | _ =>
      simp only [uexecT] at h ⊢; split at h
      · cases h
      · rename_i hd; simp only [hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
        unfold stepT at h ⊢; split at h
        · rename_i r _; simp only at h ⊢
          by_cases hr : r.1.dead = true
          · simp [hr] at h
          · simpa using hr
        · cases h

/-- An atomic command at fuel `n + 1`, from a live state, is its one step. -/
theorem uexecT_atomic {c : UCmd} (hc : atomic c = true) (n : Nat) (π : MedPolicy) {s : UState}
    (hs : s.dead = false) : uexecT (n + 1) c π s = stepT c π s := by
  cases c <;> simp_all [atomic, uexecT]

theorem push_atomic {c : UCmd} (hc : atomic c = true) (k : List UCmd) : push c k = c :: k := by
  cases c <;> simp_all [atomic, push]

theorem runS_atomic {c : UCmd} (hc : atomic c = true) (n : Nat) (π : MedPolicy) (k : List UCmd)
    {s : UState} (hs : s.dead = false) :
    urunS π (n + 1) (c :: k) s = (stepT c π s).atomS (fun t => urunS π n k t) := by
  cases c <;> simp_all [atomic, urunS]

theorem tailS_abort {π : MedPolicy} {n : Nat} {k k' : List UCmd} {r : TRun}
    (h : r.out ≠ .done) : tailS π n k r = tailS π n k' r := by
  simp [tailS, h]

theorem seqT_done_eq {a : TRun} {k : UState → TRun} (h : a.out = .done) :
    a.seqT k = ⟨(k a.st).st, a.cost + (k a.st).cost, a.ev ++ (k a.st).ev, a.lk ++ (k a.st).lk,
                (k a.st).out⟩ := by
  simp only [TRun.seqT, h, ↓reduceIte]

theorem seqT_not_done_eq {a : TRun} {k : UState → TRun} (h : a.out ≠ .done) : a.seqT k = a := by
  simp only [TRun.seqT, h, ↓reduceIte]

/-- **The step machine replays a finished `uexecT` run.** From a live state, if `uexecT` finishes
    `c` (done or aborted), then running the frames `push c k` for the run's cost plus `n` more
    steps is that record followed by `n` steps of `k` (or by nothing, if it aborted), with the
    same state, cost, events and outcome, and the same leakage once the markers are removed. -/
theorem runS_agree (π : MedPolicy) : ∀ (f : Nat) (c : UCmd) (s : UState), s.dead = false →
    (uexecT f c π s).out ≠ .fuel → ∀ (k : List UCmd) (n : Nat),
      Agree (urunS π ((uexecT f c π s).cost + n) (push c k) s) (uexecT f c π s)
        (tailS π n k (uexecT f c π s)) := by
  intro f
  induction f with
  | zero => intro c s _ hf; exact absurd rfl hf
  | succ m ih =>
    intro c s hs hf k n
    by_cases hat : atomic c = true
    · rw [uexecT_atomic hat m π hs] at hf ⊢
      rw [stepT_cost_one c hat π s, Nat.add_comm 1 n, push_atomic hat, runS_atomic hat n π k hs]
      unfold TRun.atomS
      by_cases ha : (stepT c π s).out = .done
      · simp only [ha, ↓reduceIte, tailS]
        refine ⟨rfl, by rw [stepT_cost_one c hat π s], rfl, ?_, rfl⟩
        simp only [stripMk_cons_mk, stripMk_append, stripMk_stepT]
      · simp only [ha, ↓reduceIte, tailS]
        refine ⟨rfl, by rw [stepT_cost_one c hat π s]; rfl, by simp, ?_, rfl⟩
        simp only [stripMk_cons_mk, stripMk_stepT]
        simp [stripMk]
    cases c with
    | seq c₁ c₂ =>
      simp only [uexecT, hs, Bool.false_eq_true, ↓reduceIte] at hf ⊢
      by_cases ha : (uexecT m c₁ π s).out = .done
      · rw [seqT_done_eq ha] at hf ⊢
        have hs₁ := uexecT_done_alive m c₁ π s ha
        have e₁ := ih c₁ s hs ((show (uexecT m c₁ π s).out ≠ .fuel by rw [ha]; decide))
          (push c₂ k) ((uexecT m c₂ π (uexecT m c₁ π s).st).cost + n)
        have e₂ := ih c₂ _ hs₁ hf k n
        simp only [tailS, ha, ↓reduceIte] at e₁
        simp only [push, Nat.add_assoc]
        exact agree_seq e₁ e₂
      · rw [seqT_not_done_eq ha] at hf ⊢
        have e₁ := ih c₁ s hs hf (push c₂ k) n
        rw [tailS_abort (k' := k) ha] at e₁
        simpa only [push] using e₁
    | ite e c₁ c₂ =>
      simp only [uexecT, hs, Bool.false_eq_true, ↓reduceIte] at hf ⊢
      have e₁ := ih _ s hs hf k n
      have hfuel : (TRun.tick (.branch (decide (evalE e s.store ≠ 0)))
          (uexecT m (if evalE e s.store ≠ 0 then c₁ else c₂) π s)).cost + n
          = ((uexecT m (if evalE e s.store ≠ 0 then c₁ else c₂) π s).cost + n) + 1 := by
        simp only [TRun.tick]; omega
      rw [hfuel]
      simp only [push, urunS, hs, Bool.false_eq_true, ↓reduceIte]
      exact agree_tick _ e₁
    | loop e b =>
      simp only [uexecT, hs, Bool.false_eq_true, ↓reduceIte] at hf ⊢
      by_cases hg : evalE e s.store ≠ 0
      · rw [ite_eq_left hg] at hf ⊢
        simp only [TRun.tick] at hf
        by_cases ha : (uexecT m b π s).out = .done
        · rw [seqT_done_eq ha] at hf ⊢
          have hs₁ := uexecT_done_alive m b π s ha
          have e₁ := ih b s hs ((show (uexecT m b π s).out ≠ .fuel by rw [ha]; decide))
            (.loop e b :: k) ((uexecT m (.loop e b) π (uexecT m b π s).st).cost + n)
          have e₂ := ih (.loop e b) _ hs₁ hf k n
          simp only [tailS, ha, ↓reduceIte] at e₁
          have hseq := agree_seq e₁ e₂
          have hfuel : (TRun.tick (.branch true)
              ⟨(uexecT m (.loop e b) π (uexecT m b π s).st).st,
               (uexecT m b π s).cost + (uexecT m (.loop e b) π (uexecT m b π s).st).cost,
               (uexecT m b π s).ev ++ (uexecT m (.loop e b) π (uexecT m b π s).st).ev,
               (uexecT m b π s).lk ++ (uexecT m (.loop e b) π (uexecT m b π s).st).lk,
               (uexecT m (.loop e b) π (uexecT m b π s).st).out⟩).cost + n
              = ((uexecT m b π s).cost + ((uexecT m (.loop e b) π (uexecT m b π s).st).cost + n)) + 1 := by
            simp only [TRun.tick]; omega
          rw [hfuel]
          simp only [push, urunS, hs, Bool.false_eq_true, ↓reduceIte]
          rw [ite_eq_left hg]
          exact agree_tick true hseq
        · rw [seqT_not_done_eq ha] at hf ⊢
          have e₁ := ih b s hs hf (.loop e b :: k) n
          rw [tailS_abort (k' := k) ha] at e₁
          have hfuel : (TRun.tick (.branch true) (uexecT m b π s)).cost + n
              = ((uexecT m b π s).cost + n) + 1 := by
            simp only [TRun.tick]; omega
          rw [hfuel]
          simp only [push, urunS, hs, Bool.false_eq_true, ↓reduceIte]
          rw [ite_eq_left hg]
          have h := agree_tick true e₁
          have hT : tailS π n k (TRun.tick (.branch true) (uexecT m b π s))
              = tailS π n k (uexecT m b π s) := by
            simp [tailS, TRun.tick, ha]
          rw [hT]; exact h
      · rw [ite_eq_right hg]
        have hfuel : (⟨s, 1, [], [.branch false], .done⟩ : TRun).cost + n = n + 1 := by
          simp only; omega
        rw [hfuel]
        simp only [push, urunS, hs, Bool.false_eq_true, ↓reduceIte]
        rw [ite_eq_right hg]
        refine ⟨rfl, ?_, rfl, ?_, rfl⟩
        · simp only [TRun.tickS, tailS, ↓reduceIte]
        · simp only [TRun.tickS, tailS, ↓reduceIte, stripMk_cons_mk, stripMk_cons_branch,
            List.cons_append, List.nil_append]
    | _ => simp [atomic] at hat

/-! ## The guarantees by reduction -/

/-- **A finished `uexecT` run is the step run at its cost.** -/
theorem runS_finished {π : MedPolicy} {f : Nat} {c : UCmd} {s : UState} (hs : s.dead = false)
    (hf : (uexecT f c π s).out ≠ .fuel) :
    let R := urunS π (uexecT f c π s).cost (push c []) s
    R.ev = (uexecT f c π s).ev ∧ R.cost = (uexecT f c π s).cost ∧ R.out = (uexecT f c π s).out := by
  have h := runS_agree π f c s hs hf [] 0
  simp only [Nat.add_zero] at h
  obtain ⟨_, h2, h3, _, h5⟩ := h
  by_cases hd : (uexecT f c π s).out = .done
  · simp only [tailS, hd, ↓reduceIte, urunS] at h2 h3 h5
    exact ⟨by rw [h3, List.append_nil], by rw [h2, Nat.add_zero], by rw [h5, hd]⟩
  · simp only [tailS, hd, ↓reduceIte] at h2 h3 h5
    exact ⟨by rw [h3, List.append_nil], by rw [h2, Nat.add_zero], h5⟩

/-- Every step run of a program whose `uexecT` run finishes is a prefix of that finished run:
    its events are a prefix, and its cost is at most. -/
theorem runS_within {π : MedPolicy} {f : Nat} {c : UCmd} {s : UState} (hs : s.dead = false)
    (hf : (uexecT f c π s).out ≠ .fuel) (n : Nat) :
    (urunS π n (push c []) s).ev <+: (uexecT f c π s).ev ∧
    (urunS π n (push c []) s).cost ≤ (uexecT f c π s).cost := by
  obtain ⟨e1, e2, e3⟩ := runS_finished hs hf
  have hfin : (urunS π (uexecT f c π s).cost (push c []) s).out ≠ .fuel := by rw [e3]; exact hf
  rcases Nat.le_total n (uexecT f c π s).cost with h | h
  · have hx := runS_ext π n _ (push c []) s h
    exact ⟨e1 ▸ hx.2.1, e2 ▸ hx.2.2.2⟩
  · have hx := (runS_ext π _ n (push c []) s h).1 hfin
    rw [← hx]; exact ⟨e1 ▸ LCore.prefix_refl' _, Nat.le_of_eq e2⟩

/-- A `bcheck`-accepted program's `uexecT` run finishes, at some fuel. -/
theorem bcheck_finishesT {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) (σ : Store) :
    ∃ f, (uexecT f c π (initU σ)).out ≠ .fuel :=
  (ucmdLangT_lawful P π).bound_finishes (bcheck_boundT h π) σ trivial

/-- **Budget on step fuel.** -/
theorem bcheck_boundS {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS P π) k c := by
  intro n σ _
  obtain ⟨f, hf⟩ := bcheck_finishesT h π σ
  exact Nat.le_trans (runS_within (s := initU σ) rfl hf n).2 (bcheck_boundT h π f σ trivial)

/-- **Every prefix-closed trace certificate on `ucmdLangT` holds on step fuel**, for a program
    whose runs finish. -/
theorem traceS_of_traceT {P : Partition} {π : MedPolicy} {c : UCmd} {Φ : List LCore.Ev → Prop}
    (hΦ : LCore.PrefixClosed Φ) (hfin : ∀ σ, ∃ f, (uexecT f c π (initU σ)).out ≠ .fuel)
    (hc : LCore.Cert.trace (ucmdLangT P π) Φ c) : LCore.Cert.trace (ucmdLangS P π) Φ c := by
  intro n σ _
  obtain ⟨f, hf⟩ := hfin σ
  exact hΦ _ _ (runS_within (s := initU σ) rfl hf n).1 (hc f σ trivial)

theorem faultFree_prefixClosed : LCore.PrefixClosed (fun evs => faultEv ∉ evs) :=
  fun _ _ hab hb h => hb (hab.subset h)

/-- **Mediation on step fuel.** -/
theorem bcheck_mediatedS {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangS P π) (mediated π) c :=
  traceS_of_traceT (mediated_prefixClosed π) (bcheck_finishesT h π) (bcheck_mediatedT h π)

/-- **Memory safety on step fuel.** -/
theorem bcheck_memsafeS {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangS P π) (fun evs => faultEv ∉ evs) c :=
  traceS_of_traceT faultFree_prefixClosed (bcheck_finishesT h π) (bcheck_memsafeT h π)

/-! ## Noninterference on step fuel, in lockstep -/

/-- A frame stack typed by a chain of `JSecTy` judgments; the tracked set may shrink between
    frames. -/
inductive FTy (P : Partition) : List String → List UCmd → Prop where
  | nil  : ∀ V, FTy P V []
  | cons : ∀ {V V₁ W : List String} {c : UCmd} {k : List UCmd}, JSecTy P V c V₁ →
      (∀ x ∈ W, x ∈ V₁) → FTy P W k → FTy P V (c :: k)

theorem push_fty {P : Partition} : ∀ {c : UCmd} {V V₁ W : List String} {k : List UCmd},
    JSecTy P V c V₁ → (∀ x ∈ W, x ∈ V₁) → FTy P W k → FTy P V (push c k)
  | .seq a b, V, V₁, W, k, hj, hw, hk => by
    cases hj with
    | seq h₁ h₂ => exact push_fty (c := a) h₁ (fun x h => h) (push_fty (c := b) h₂ hw hk)
  | .skip, _, _, _, _, hj, hw, hk | .assign _ _, _, _, _, _, hj, hw, hk
  | .check _, _, _, _, _, hj, hw, hk | .access _, _, _, _, _, hj, hw, hk
  | .memop _ _, _, _, _, _, hj, hw, hk | .sop _ _ _, _, _, _, _, hj, hw, hk
  | .hop _ _ _, _, _, _, _, hj, hw, hk | .ite _ _ _, _, _, _, _, hj, hw, hk
  | .loop _ _, _, _, _, _, hj, hw, hk => FTy.cons hj hw hk

theorem TRun.tickS_same {a a' : TRun} (l : LCore.Lk) (h : a.Same a') :
    (a.tickS l).Same (a'.tickS l) :=
  ⟨h.1, by simp only [TRun.tickS, h.2.1], by simp only [TRun.tickS, h.2.2.1], h.2.2.2⟩

theorem TRun.atomS_same {a a' : TRun} {k k' : UState → TRun} (h : a.Same a')
    (hk : a.out = .done → (k a.st).Same (k' a'.st)) : (a.atomS k).Same (a'.atomS k') := by
  obtain ⟨he, hl, hc, ho⟩ := h
  unfold TRun.atomS
  by_cases ha : a.out = .done
  · have ha' : a'.out = .done := ho ▸ ha
    obtain ⟨he', hl', hc', ho'⟩ := hk ha
    simp only [ha, ha', ↓reduceIte]
    exact ⟨by rw [he, he'], by rw [hl, hl'], by rw [hc, hc'], ho'⟩
  · have ha' : ¬ a'.out = .done := ho ▸ ha
    simp only [ha, ha', ↓reduceIte]
    exact ⟨he, by rw [hl], hc, ho⟩

/-- After one atomic step on each side, from related live states, the states are related again. -/
theorem jrel_step {P : Partition} {V V₁ : List String} {c : UCmd} (hj : JSecTy P V c V₁)
    (hat : atomic c = true) {π : MedPolicy} {s s' : UState} (hr : JRel P V s s')
    (hd : s.dead = false) (hd' : s'.dead = false)
    (hdone : (stepT c π s).out = .done) (hdone' : (stepT c π s').out = .done) :
    JRel P V₁ (stepT c π s).st (stepT c π s').st := by
  have h := jrel_done (n := 1) hj hr (by rw [uexecT_atomic hat 0 π hd]; exact hdone)
    (by rw [uexecT_atomic hat 0 π hd']; exact hdone')
  rwa [uexecT_atomic hat 0 π hd, uexecT_atomic hat 0 π hd'] at h

/-- **Noninterference on every step run.** Two related states running the same typed frames
    give indistinguishable records at every step fuel, step markers included. -/
theorem runS_same {P : Partition} (π : MedPolicy) : ∀ (n : Nat) (V : List String)
    (k : List UCmd) (s s' : UState), FTy P V k → JRel P V s s' →
      (urunS π n k s).Same (urunS π n k s') := by
  intro n
  induction n with
  | zero =>
    intro V k s s' _ _
    cases k <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | succ m ih =>
    intro V k s s' hk hr
    cases k with
    | nil => exact ⟨rfl, rfl, rfl, rfl⟩
    | cons c k =>
      have hdd : s.dead = s'.dead := hr.2.2.2.2.1.2.2.1
      by_cases hd : s.dead = true
      · have hd' : s'.dead = true := hdd ▸ hd
        simp only [urunS, hd, hd', ↓reduceIte]; exact ⟨rfl, rfl, rfl, rfl⟩
      have hd0 : s.dead = false := by simpa using hd
      have hd' : s'.dead = false := hdd ▸ hd0
      obtain _ | ⟨hj, hw, hk'⟩ := hk
      have hj0 := hj
      cases hj with
      | seq h₁ h₂ =>
        simp only [urunS, hd0, hd', Bool.false_eq_true, ↓reduceIte]
        exact ih _ _ s s' (push_fty h₁ (fun x h => h) (push_fty h₂ hw hk')) hr
      | iteL e he h₁ h₂ =>
        have hg : evalE e s.store = evalE e s'.store := evalE_lowEq e he hr.2.2.2.2.1.1
        simp only [urunS, hd0, hd', Bool.false_eq_true, ↓reduceIte, hg]
        apply TRun.tickS_same
        split
        · exact ih _ _ s s' (push_fty h₁ (fun x hx => interStr_left (hw x hx)) hk') hr
        · exact ih _ _ s s' (push_fty h₂ (fun x hx => interStr_right (hw x hx)) hk') hr
      | whileW e he hWV hc hWW =>
        have hg : evalE e s.store = evalE e s'.store := evalE_lowEq e he hr.2.2.2.2.1.1
        simp only [urunS, hd0, hd', Bool.false_eq_true, ↓reduceIte, hg]
        have hrW := JRel.mono hWV hr
        split
        · apply TRun.tickS_same
          exact ih _ _ s s' (push_fty hc (fun x h => h)
            (FTy.cons (JSecTy.whileW e he hWW hc hWW) hw hk')) hrW
        · apply TRun.tickS_same
          exact ih _ _ s s' hk' (JRel.mono hw hrW)
      | _ =>
        simp only [urunS, hd0, hd', Bool.false_eq_true, ↓reduceIte]
        exact TRun.atomS_same (stepT_same hj0 hr hd0)
          (fun hdone => ih _ _ _ _ hk' (JRel.mono hw (jrel_step hj0 rfl hr hd0 hd' hdone
            ((stepT_same hj0 hr hd0).2.2.2 ▸ hdone))))

/-- **Noninterference on step fuel.** -/
theorem bcheck_relS {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.rel (ucmdLangS P π) c := by
  intro n σ σ' _ _ hσ
  have hf := bcheck_sound c [] [] A' V' k h
  have hr : JRel P [] (initU σ) (initU σ') :=
    ⟨SepInv.initU, SepInv.initU, LabInv.initU, LabInv.initU,
     ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩,
     fun _ x hx => by simp at hx⟩
  obtain ⟨he, hl, hc, ho⟩ := runS_same π n [] (push c []) _ _
    (push_fty hf.joint (W := []) (fun x hx => by simp at hx) (FTy.nil _)) hr
  show ({ ev := _, lk := _, cost := _, out := _ } : LCore.Beh) = { ev := _, lk := _, cost := _, out := _ }
  rw [he, hl, hc, ho]

/-- **Adequacy on step fuel**: `bcheck`'s four guarantees on `ucmdLangS`, over every run. -/
theorem bcheck_lcoreS {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS P π) k c
  ∧ LCore.Cert.trace (ucmdLangS P π) (mediated π) c
  ∧ LCore.Cert.trace (ucmdLangS P π) (fun evs => faultEv ∉ evs) c
  ∧ LCore.Cert.rel (ucmdLangS P π) c :=
  ⟨bcheck_boundS h π, bcheck_mediatedS h π, bcheck_memsafeS h π, bcheck_relS h π⟩

end ConfTyping
