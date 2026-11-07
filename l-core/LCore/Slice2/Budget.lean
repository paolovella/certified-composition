/-
  BOUND-01 step 3: the checker's budget over counted loops, by a potential (as in amortised resource analysis).

  `counted p` accepts a body that is a `seq` tree of three kinds of command: *plain* (loop-free, assigning no counter and no input), *init*
  (`c := e` for a counter `c`, `e` reading only inputs), and *counted loops* `loop (var c) (seq B (c := c + -1))` with `B` plain. The counters
  are the loop guards. Loops are not nested, and no loop sits in an `ite`. `forN` and `forMax` are of this form.

  `pot` gives each frame list and store an upper bound on what the rest of the run costs. `run_pot`: the cost at every fuel is at most `pot`.
  So `slice_boundR`: the budget `pot (frames of the body) (initial store)` is a function of the input, and `boundR` holds on the source.
-/
import LCore.Slice2.For

namespace LCore.Slice2.Budget

open Slice (W64 Expr Store upd eval initFrom sec0 inp tick)

/-! ## The shapes -/

def evars : Expr → List String
  | .lit _ => []
  | .var x => [x]
  | .add a b | .bin _ a b => evars a ++ evars b
  | .shr a _ => evars a

def assigns : Cmd → List String
  | .assign x _ | .load x _ => [x]
  | .seq a b | .ite _ a b => assigns a ++ assigns b
  | .loop _ b => assigns b
  | _ => []

def counters : Cmd → List String
  | .loop (.var c) b => c :: counters b
  | .loop _ b => counters b
  | .seq a b | .ite _ a b => counters a ++ counters b
  | _ => []

/-- `c + -1`, the decrement. -/
def isDec (c : String) : Expr → Bool
  | .add (.var y) (.lit w) => y == c && w.val == 2 ^ 64 - 1
  | _ => false

def plainC (cs S : List String) (c : Cmd) : Bool :=
  loopFree c && (assigns c).all (fun x => !cs.contains x && !S.contains x)

def topC (cs S : List String) : Cmd → Bool
  | .seq a b => topC cs S a && topC cs S b
  | .assign x e => (cs.contains x && (evars e).all S.contains) || plainC cs S (.assign x e)
  | .loop (.var c) (.seq B (.assign c' d)) => c' == c && cs.contains c && isDec c d && plainC cs S B
  | c => plainC cs S c

/-- **The checker's budget rule.** The counters are the loop guards, and none of them is an input. -/
def counted (p : Prog) : Bool :=
  topC (counters p.body) p.inputs p.body && (counters p.body).all (fun c => !p.inputs.contains c)

/-! ## The potential -/

/-- What the rest of a run can cost, from these frames and this store. -/
def pot (cs : List String) : List Frame → Store → Nat
  | [], _ => 0
  | (.assign x e, _) :: k, s => 1 + pot cs k (if cs.contains x then upd s x (eval e s) else s)
  | (.loop (.var c) (.seq B _), _) :: k, s => (s c).val * (costOf B + 2) + 1 + pot cs k s
  | (c, _) :: k, s => costOf c + pot cs k s

/-- The budget the checker gives a program, on an input. -/
def budget (p : Prog) (i : Nat → W64) : Nat := pot (counters p.body) (push p.body [] []) (initFrom i p.inputs 0)

/-! ## Frames the checker allows -/

section
variable (cs S : List String)

def IsPlain (c : Cmd) : Prop := plainC cs S c = true
def IsSet (c : Cmd) : Prop := ∃ x e, c = .assign x e ∧ cs.contains x = true ∧
  ((evars e).all S.contains = true ∨ isDec x e = true)
def IsInit (c : Cmd) : Prop := ∃ x e, c = .assign x e ∧ cs.contains x = true ∧ (evars e).all S.contains = true
def IsLoop (c : Cmd) : Prop := ∃ x B d, c = .loop (.var x) (.seq B (.assign x d)) ∧ cs.contains x = true ∧ isDec x d = true ∧
  plainC cs S B = true

/-- A frame in a loop's body: plain, or the decrement. -/
def BodyF (f : Frame) : Prop := IsPlain cs S f.1 ∨ ∃ x d, f.1 = .assign x d ∧ cs.contains x = true ∧ isDec x d = true
/-- A frame at the top: plain, an init, or a counted loop. -/
def TopF (f : Frame) : Prop := IsPlain cs S f.1 ∨ IsInit cs S f.1 ∨ IsLoop cs S f.1

def Ok (k : List Frame) : Prop := ∃ b t, k = b ++ t ∧ (∀ f ∈ b, BodyF cs S f) ∧ ∀ f ∈ t, TopF cs S f

/-- Stores that agree on the counters and the inputs. -/
def Agree (s s' : Store) : Prop := ∀ y, (cs.contains y = true ∨ S.contains y = true) → s y = s' y
end

/-! ## Small facts -/

theorem tick_cost (l : List Lk) (q : List Nat) (r : Beh) : (tick l q r).cost = 1 + r.cost := rfl

theorem upd_same (s : Store) (x : String) (v : W64) : upd s x v x = v := by simp [upd]
theorem upd_other (s : Store) {x y : String} (v : W64) (h : y ≠ x) : upd s x v y = s y := by simp [upd, h]

theorem upd_upd_same (s : Store) (x : String) (v w : W64) : upd (upd s x v) x w = upd s x w := by
  funext y; by_cases h : y = x <;> simp [upd, h]

theorem upd_comm (s : Store) {x y : String} (v w : W64) (h : x ≠ y) : upd (upd s x v) y w = upd (upd s y w) x v := by
  funext z; by_cases h1 : z = x <;> by_cases h2 : z = y <;> simp_all [upd]

theorem eval_agree {cs S : List String} {s s' : Store} (h : Agree cs S s s') : ∀ (e : Expr), (evars e).all S.contains = true → eval e s = eval e s'
  | .lit _, _ => rfl
  | .var x, he => by
    simp only [evars, List.all_cons, List.all_nil, Bool.and_true] at he
    exact h x (Or.inr he)
  | .add a b, he | .bin _ a b, he => by
    simp only [evars, List.all_append, Bool.and_eq_true] at he
    simp only [eval, eval_agree h a he.1, eval_agree h b he.2]
  | .shr a _, he => by
    simp only [evars] at he
    simp only [eval, eval_agree h a he]

/-- An expression that reads only inputs is unchanged by a write to something that is not an input. -/
theorem eval_upd_out {S : List String} {c : String} (hc : S.contains c = false) (s : Store) (v : W64) :
    ∀ (e : Expr), (evars e).all S.contains = true → eval e (upd s c v) = eval e s
  | .lit _, _ => rfl
  | .var x, he => by
    simp only [evars, List.all_cons, List.all_nil, Bool.and_true] at he
    have : x ≠ c := by rintro rfl; simp_all
    simp [eval, upd, this]
  | .add a b, he | .bin _ a b, he => by
    simp only [evars, List.all_append, Bool.and_eq_true] at he
    simp only [eval, eval_upd_out hc s v a he.1, eval_upd_out hc s v b he.2]
  | .shr a _, he => by
    simp only [evars] at he
    simp only [eval, eval_upd_out hc s v a he]

theorem isDec_shape {x : String} {d : Expr} (h : isDec x d = true) : ∃ w : W64, d = .add (.var x) (.lit w) ∧ w.val = 2 ^ 64 - 1 := by
  match d, h with
  | .add (.var y) (.lit w), h =>
    simp only [isDec, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨w, by rw [h.1], h.2⟩

theorem eval_dec {x : String} {d : Expr} (h : isDec x d = true) (s : Store) (hv : (s x).val ≠ 0) : (eval d s).val = (s x).val - 1 := by
  obtain ⟨w, rfl, hw⟩ := isDec_shape h
  have hlt := (s x).isLt
  simp only [eval, W64.add, W64.ofNat, hw]
  simp only [Nat.reducePow] at hlt ⊢
  omega

theorem agree_upd {cs S : List String} {s s' : Store} (h : Agree cs S s s') (x : String) (v : W64) : Agree cs S (upd s x v) (upd s' x v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp [upd]
  · simp [upd, hyx, h y hy]

theorem agree_out {cs S : List String} (s : Store) {x : String} (hx : cs.contains x = false ∧ S.contains x = false) (v : W64) :
    Agree cs S (upd s x v) s := by
  intro y hy
  have : y ≠ x := by
    rintro rfl; rcases hy with hy | hy <;> simp_all
  simp [upd, this]

theorem plain_assign {cs S : List String} {x : String} {e : Expr} (h : plainC cs S (.assign x e) = true) :
    cs.contains x = false ∧ S.contains x = false := by
  simp only [plainC, loopFree, assigns, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact h

theorem plain_load {cs S : List String} {x : String} {e : Expr} (h : plainC cs S (.load x e) = true) :
    cs.contains x = false ∧ S.contains x = false := by
  simp only [plainC, loopFree, assigns, List.all_cons, List.all_nil, Bool.and_true, Bool.true_and, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  exact h

theorem plain_seq {cs S : List String} {a b : Cmd} (h : plainC cs S (.seq a b) = true) : plainC cs S a = true ∧ plainC cs S b = true := by
  simp only [plainC, loopFree, assigns, List.all_append, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩

theorem plain_ite {cs S : List String} {e : Expr} {a b : Cmd} (h : plainC cs S (.ite e a b) = true) :
    plainC cs S a = true ∧ plainC cs S b = true := by
  simp only [plainC, loopFree, assigns, List.all_append, Bool.and_eq_true] at h ⊢
  exact ⟨⟨h.1.1, h.2.1⟩, h.1.2, h.2.2⟩

theorem plain_loop {cs S : List String} {e : Expr} {b : Cmd} : plainC cs S (.loop e b) = false := by
  simp [plainC, loopFree]

theorem push_app : ∀ (c : Cmd) (p : List Nat) (k : List Frame), push c p k = push c p [] ++ k
  | .seq a b, p, k => by
    simp only [push]
    rw [push_app b _ k, push_app a _ (push b (p ++ [1]) [] ++ k), push_app a _ (push b (p ++ [1]) []), List.append_assoc]
  | .skip, _, _ | .assign _ _, _, _ | .ite _ _ _, _, _ | .loop _ _, _, _ | .load _ _, _, _ | .store _ _, _, _ => rfl

theorem push_plain_frames {cs S : List String} : ∀ (c : Cmd) (p : List Nat), plainC cs S c = true → ∀ f ∈ push c p [], IsPlain cs S f.1
  | .seq a b, p, h, f, hf => by
    obtain ⟨ha, hb⟩ := plain_seq h
    simp only [push] at hf
    rw [push_app a] at hf
    rcases List.mem_append.1 hf with hf | hf
    · exact push_plain_frames a _ ha f hf
    · exact push_plain_frames b _ hb f hf
  | .skip, _, h, f, hf | .assign _ _, _, h, f, hf | .ite _ _ _, _, h, f, hf | .loop _ _, _, h, f, hf
  | .load _ _, _, h, f, hf | .store _ _, _, h, f, hf => by
    simp only [push, List.mem_singleton] at hf
    subst hf
    exact h

/-- **A plain command's frames cost what `costOf` says.** -/
theorem pot_push_plain {cs S : List String} : ∀ (c : Cmd) (p : List Nat) (k : List Frame) (s : Store), plainC cs S c = true →
    pot cs (push c p k) s = costOf c + pot cs k s
  | .seq a b, p, k, s, h => by
    obtain ⟨ha, hb⟩ := plain_seq h
    simp only [push, costOf]
    rw [pot_push_plain a _ _ s ha, pot_push_plain b _ _ s hb]
    omega
  | .assign x e, p, k, s, h => by
    have hx := (plain_assign h).1
    simp only [push, pot, hx, Bool.false_eq_true, ↓reduceIte, costOf]
  | .loop e b, _, _, _, h => by simp [plain_loop] at h
  | .skip, _, _, _, _ | .ite _ _ _, _, _, _, _ | .load _ _, _, _, _, _ | .store _ _, _, _, _, _ => rfl

/-! ## The potential reads only the counters and the inputs -/

theorem pot_agree {cs S : List String} : ∀ (k : List Frame) (s s' : Store), (∀ f ∈ k, BodyF cs S f ∨ TopF cs S f) → Agree cs S s s' →
    pot cs k s = pot cs k s'
  | [], _, _, _, _ => rfl
  | (c, p) :: k, s, s', hk, h => by
    have hf := hk _ List.mem_cons_self
    have hk' : ∀ f ∈ k, BodyF cs S f ∨ TopF cs S f := fun f hf => hk f (List.mem_cons_of_mem _ hf)
    cases c with
    | assign x e =>
      simp only [pot]
      by_cases hx : cs.contains x = true
      · have he : eval e s = eval e s' := by
          rcases hf with (hp | ⟨y, d, hy, _, hd⟩) | (hp | ⟨y, d, hy, _, hd⟩ | ⟨_, _, _, hy, _⟩)
          · exact absurd (plain_assign hp).1 (by rw [hx]; simp)
          · cases hy; obtain ⟨w, rfl, _⟩ := isDec_shape hd
            simp only [eval]; rw [h x (Or.inl hx)]
          · exact absurd (plain_assign hp).1 (by rw [hx]; simp)
          · cases hy; exact eval_agree h e hd
          · cases hy
        simp only [hx, ↓reduceIte, he]
        rw [pot_agree k _ _ hk' (agree_upd h x _)]
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        rw [pot_agree k _ _ hk' h]
    | loop e b =>
      rcases hf with (hp | ⟨_, _, hy, _⟩) | (hp | ⟨_, _, hy, _⟩ | ⟨x, B, d, hy, hx, _, _⟩)
      · simp [IsPlain, plain_loop] at hp
      · cases hy
      · simp [IsPlain, plain_loop] at hp
      · cases hy
      · cases hy
        simp only [pot]
        rw [h x (Or.inl hx), pot_agree k _ _ hk' h]
    | skip | seq _ _ | ite _ _ _ | load _ _ | store _ _ =>
      simp only [pot]
      rw [pot_agree k _ _ hk' h]

/-! ## After a loop, a smaller counter costs no more -/

theorem pot_mono {cs S : List String} (hD : ∀ y, cs.contains y = true → S.contains y = false) {c : String} (hc : cs.contains c = true) :
    ∀ (t : List Frame) (s : Store) (v : W64), (∀ f ∈ t, TopF cs S f) → v.val ≤ (s c).val → pot cs t (upd s c v) ≤ pot cs t s
  | [], _, _, _, _ => Nat.le_refl _
  | (cmd, p) :: k, s, v, ht, hv => by
    have hf := ht _ List.mem_cons_self
    have hk : ∀ f ∈ k, TopF cs S f := fun f hf => ht f (List.mem_cons_of_mem _ hf)
    have hcS : S.contains c = false := hD c hc
    cases cmd with
    | assign x e =>
      simp only [pot]
      by_cases hx : cs.contains x = true
      · obtain ⟨y, e', hy, _, he⟩ : IsInit cs S (.assign x e) := by
          rcases hf with hp | hi | ⟨_, _, _, hy, _⟩
          · exact absurd (plain_assign hp).1 (by rw [hx]; simp)
          · exact hi
          · cases hy
        cases hy
        have hev : eval e (upd s c v) = eval e s := eval_upd_out hcS s v e he
        simp only [hx, ↓reduceIte, hev]
        by_cases hxc : x = c
        · subst hxc; rw [upd_upd_same]; omega
        · rw [upd_comm s v _ (Ne.symm hxc)]
          have := pot_mono hD hc k (upd s x (eval e s)) v hk (by rw [upd_other s _ (Ne.symm hxc)]; exact hv)
          omega
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        have := pot_mono hD hc k s v hk hv
        omega
    | loop e b =>
      rcases hf with hp | ⟨_, _, hy, _⟩ | ⟨x, B, d, hy, _, _, _⟩
      · simp [IsPlain, plain_loop] at hp
      · cases hy
      · cases hy
        simp only [pot]
        have := pot_mono hD hc k s v hk hv
        have hm : (upd s c v x).val * (costOf B + 2) ≤ (s x).val * (costOf B + 2) := by
          by_cases hxc : x = c
          · subst hxc; rw [upd_same]; exact Nat.mul_le_mul_right _ hv
          · rw [upd_other s v hxc]; exact Nat.le_refl _
        omega
    | skip | seq _ _ | ite _ _ _ | load _ _ | store _ _ =>
      simp only [pot]
      have := pot_mono hD hc k s v hk hv
      omega


/-! ## Frame lists -/

theorem ok_cons {cs S : List String} {f : Frame} {k : List Frame} (h : Ok cs S (f :: k)) :
    (BodyF cs S f ∧ Ok cs S k) ∨ (TopF cs S f ∧ ∀ g ∈ k, TopF cs S g) := by
  obtain ⟨b, t, hk, hb, ht⟩ := h
  cases b with
  | nil =>
    simp only [List.nil_append] at hk
    subst hk
    exact Or.inr ⟨ht _ List.mem_cons_self, fun g hg => ht g (List.mem_cons_of_mem _ hg)⟩
  | cons g b =>
    simp only [List.cons_append, List.cons.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact Or.inl ⟨hb _ List.mem_cons_self, b, t, rfl, fun x hx => hb x (List.mem_cons_of_mem _ hx), ht⟩

theorem ok_top {cs S : List String} {t : List Frame} (h : ∀ f ∈ t, TopF cs S f) : Ok cs S t :=
  ⟨[], t, rfl, fun _ h => by simp at h, h⟩

theorem ok_all {cs S : List String} {k : List Frame} (h : Ok cs S k) : ∀ f ∈ k, BodyF cs S f ∨ TopF cs S f := by
  obtain ⟨b, t, rfl, hb, ht⟩ := h
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · exact Or.inl (hb f hf)
  · exact Or.inr (ht f hf)

theorem ok_push_plain {cs S : List String} {c : Cmd} (p : List Nat) {k : List Frame} (hc : plainC cs S c = true) (h : Ok cs S k) :
    Ok cs S (push c p k) := by
  obtain ⟨b, t, rfl, hb, ht⟩ := h
  refine ⟨push c p [] ++ b, t, by rw [push_app, List.append_assoc], ?_, ht⟩
  intro f hf
  rcases List.mem_append.1 hf with hf | hf
  · exact Or.inl (push_plain_frames c p hc f hf)
  · exact hb f hf

/-! ## One step at a time -/

section
variable {cs S : List String} {ret : Expr} {m : Nat}

theorem step_plain (IH : ∀ k s a, Ok cs S k → (run ret m k s a).cost ≤ pot cs k s) {c : Cmd} {p : List Nat} {k : List Frame}
    {s : Store} {a : Arr} (hc : plainC cs S c = true) (hk : Ok cs S k) :
    (run ret (m + 1) ((c, p) :: k) s a).cost ≤ pot cs ((c, p) :: k) s := by
  have hall := ok_all hk
  cases c with
  | skip => have := IH k s a hk; simp only [run, tick_cost, pot, costOf]; omega
  | assign x e =>
    have hx := plain_assign hc
    have := IH k (upd s x (eval e s)) a hk
    rw [pot_agree k _ s hall (agree_out s hx _)] at this
    simp only [run, tick_cost, pot, hx.1, Bool.false_eq_true, ↓reduceIte]; omega
  | load x e =>
    have hx := plain_load hc
    have := IH k (upd s x (a (idx (eval e s)))) a hk
    rw [pot_agree k _ s hall (agree_out s hx _)] at this
    simp only [run, tick_cost, pot, costOf]; omega
  | store e v => have := IH k s (updA a (idx (eval e s)) (eval v s)) hk; simp only [run, tick_cost, pot, costOf]; omega
  | seq c₁ c₂ =>
    obtain ⟨h1, h2⟩ := plain_seq hc
    have := IH (push c₁ (p ++ [0]) (push c₂ (p ++ [1]) k)) s a (ok_push_plain (p ++ [0]) h1 (ok_push_plain (p ++ [1]) h2 hk))
    rw [pot_push_plain _ _ _ _ h1, pot_push_plain _ _ _ _ h2] at this
    simp only [run, pot, costOf]; omega
  | ite e c₁ c₂ =>
    obtain ⟨h1, h2⟩ := plain_ite hc
    simp only [run]
    split
    · have := IH (push c₁ (p ++ [0]) k) s a (ok_push_plain (p ++ [0]) h1 hk)
      rw [pot_push_plain _ _ _ _ h1] at this
      simp only [tick_cost, pot, costOf]
      have := Nat.le_max_left (costOf c₁) (costOf c₂); omega
    · have := IH (push c₂ (p ++ [1]) k) s a (ok_push_plain (p ++ [1]) h2 hk)
      rw [pot_push_plain _ _ _ _ h2] at this
      simp only [tick_cost, pot, costOf]
      have := Nat.le_max_right (costOf c₁) (costOf c₂); omega
  | loop e b => simp [plain_loop] at hc

theorem step_set (IH : ∀ k s a, Ok cs S k → (run ret m k s a).cost ≤ pot cs k s) {x : String} {e : Expr} {p : List Nat}
    {k : List Frame} {s : Store} {a : Arr} (hx : cs.contains x = true) (hk : Ok cs S k) :
    (run ret (m + 1) ((.assign x e, p) :: k) s a).cost ≤ pot cs ((.assign x e, p) :: k) s := by
  have := IH k (upd s x (eval e s)) a hk
  simp only [run, tick_cost, pot, hx, ↓reduceIte]; omega

theorem step_loop (hD : ∀ y, cs.contains y = true → S.contains y = false) (IH : ∀ k s a, Ok cs S k → (run ret m k s a).cost ≤ pot cs k s)
    {x : String} {B : Cmd} {d : Expr} {p : List Nat} {k : List Frame} {s : Store} {a : Arr}
    (hx : cs.contains x = true) (hd : isDec x d = true) (hB : plainC cs S B = true) (hk : ∀ f ∈ k, TopF cs S f) :
    (run ret (m + 1) ((.loop (.var x) (.seq B (.assign x d)), p) :: k) s a).cost ≤
      pot cs ((.loop (.var x) (.seq B (.assign x d)), p) :: k) s := by
  simp only [run]
  split
  · rename_i hv
    have hv' : (s x).val ≠ 0 := hv
    have hloop : TopF cs S (.loop (.var x) (.seq B (.assign x d)), p) := Or.inr (Or.inr ⟨x, B, d, rfl, hx, hd, hB⟩)
    have hok : Ok cs S (push (.seq B (.assign x d)) (p ++ [0]) ((.loop (.var x) (.seq B (.assign x d)), p) :: k)) := by
      simp only [push]
      refine ⟨push B (p ++ [0] ++ [0]) [] ++ [(.assign x d, p ++ [0] ++ [1])], (.loop (.var x) (.seq B (.assign x d)), p) :: k, ?_, ?_, ?_⟩
      · rw [push_app B]; simp only [List.append_assoc, List.singleton_append]
      · intro f hf
        rcases List.mem_append.1 hf with hf | hf
        · exact Or.inl (push_plain_frames B _ hB f hf)
        · simp only [List.mem_singleton] at hf; subst hf; exact Or.inr ⟨x, d, rfl, hx, hd⟩
      · intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · exact hloop
        · exact hk f hf
    have := IH _ s a hok
    simp only [push] at this
    rw [pot_push_plain _ _ _ _ hB] at this
    have hval : (eval d s).val = (s x).val - 1 := eval_dec hd s hv'
    have hmono := pot_mono hD hx k s (eval d s) hk (by omega)
    simp only [pot, hx, ↓reduceIte, upd_same, hval] at this
    simp only [tick_cost, pot, push, eval]
    obtain ⟨v, hvv⟩ : ∃ v, (s x).val = v + 1 := ⟨(s x).val - 1, by omega⟩
    rw [hvv] at this ⊢
    simp only [Nat.add_sub_cancel] at this
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have := IH k s a (ok_top hk)
    simp only [tick_cost, pot]
    omega

end

/-- **At every fuel, a run costs at most the potential.** -/
theorem run_pot {cs S : List String} (hD : ∀ y, cs.contains y = true → S.contains y = false) (ret : Expr) :
    ∀ (n : Nat) (k : List Frame) (s : Store) (a : Arr), Ok cs S k → (run ret n k s a).cost ≤ pot cs k s := by
  intro n
  induction n with
  | zero => intro k s a _; cases k <;> simp [run]
  | succ m IH =>
    intro k s a hk
    cases k with
    | nil => simp [run]
    | cons f k =>
      obtain ⟨c, p⟩ := f
      rcases ok_cons hk with ⟨hf, hk'⟩ | ⟨hf, ht⟩
      · rcases hf with hp | ⟨x, d, hc, hx, _⟩
        · exact step_plain IH hp hk'
        · simp only at hc; subst hc; exact step_set IH hx hk'
      · rcases hf with hp | ⟨x, e, hc, hx, _⟩ | ⟨x, B, d, hc, hx, hd, hB⟩
        · exact step_plain IH hp (ok_top ht)
        · simp only at hc; subst hc; exact step_set IH hx (ok_top ht)
        · simp only at hc; subst hc; exact step_loop hD IH hx hd hB ht


/-! ## What the checker accepts starts in good frames -/

theorem topC_frames {cs S : List String} : ∀ (c : Cmd) (q : List Nat), topC cs S c = true → ∀ f ∈ push c q [], TopF cs S f := by
  intro c
  induction c with
  | seq a b iha ihb =>
    intro q h f hf
    simp only [topC, Bool.and_eq_true] at h
    simp only [push] at hf
    rw [push_app a] at hf
    rcases List.mem_append.1 hf with hf | hf
    · exact iha _ h.1 f hf
    · exact ihb _ h.2 f hf
  | assign x e =>
    intro q h f hf
    simp only [push, List.mem_singleton] at hf; subst hf
    simp only [topC, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with ⟨hx, he⟩ | hp
    · exact Or.inr (Or.inl ⟨x, e, rfl, hx, he⟩)
    · exact Or.inl hp
  | loop e b _ =>
    intro q h f hf
    simp only [push, List.mem_singleton] at hf; subst hf
    match e, b, h with
    | .var x, .seq B (.assign y d), h =>
      simp only [topC, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, hx⟩, hd⟩, hB⟩ := h
      exact Or.inr (Or.inr ⟨y, B, d, rfl, hx, hd, hB⟩)
    | .lit _, _, h | .add _ _, _, h => simp [topC, plainC, loopFree] at h
    | .var _, .skip, h | .var _, .assign _ _, h | .var _, .ite _ _ _, h | .var _, .loop _ _, h | .var _, .load _ _, h
    | .var _, .store _ _, h => simp [topC, plainC, loopFree] at h
    | .var _, .seq _ .skip, h | .var _, .seq _ (.seq _ _), h | .var _, .seq _ (.ite _ _ _), h | .var _, .seq _ (.loop _ _), h
    | .var _, .seq _ (.load _ _), h | .var _, .seq _ (.store _ _), h => simp [topC, plainC, loopFree] at h
  | skip | ite _ _ _ _ _ | load _ _ | store _ _ =>
    intro q h f hf
    simp only [push, List.mem_singleton] at hf; subst hf
    exact Or.inl h

theorem counted_ok {p : Prog} (h : counted p = true) :
    Ok (counters p.body) p.inputs (push p.body [] []) ∧ ∀ y, (counters p.body).contains y = true → p.inputs.contains y = false := by
  simp only [counted, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨ok_top (topC_frames _ _ h.1), fun y hy => ?_⟩
  have := h.2 y (List.contains_iff_mem.1 hy)
  simpa using this

/-! ## The budget, on the source -/

/-- **The checker's budget is a certificate.** A program `counted` accepts has `boundR` on the source language, with the budget `budget p`,
    a function of the input. -/
theorem slice_boundR (E : Type) (P : Nat → Bool) {p : Prog} (hc : counted p = true) :
    Cert.boundR (sliceLang E P) (fun i k => k = budget p i.1) p := by
  obtain ⟨hok, hD⟩ := counted_ok hc
  intro i _
  exact ⟨_, rfl, fun n => run_pot hD p.ret n _ _ zeroA hok⟩

/-! ## Witnesses -/

open For

theorem countUp_counted : counted countUp = true := by decide
theorem capped_counted : counted capped = true := by decide

/-- **`countUp`'s budget grows with its public input, `4n + 2`, and on these inputs the run costs exactly that**: the budget is tight. -/
theorem countUp_budget :
    budget countUp (inp 5 3) = 14 ∧ budget countUp (inp 5 10) = 42 ∧
    (src countUp 1000 5 3).cost = 14 ∧ (src countUp 1000 5 10).cost = 42 := by
  decide +kernel

/-- **`capped`'s budget does not depend on the input**, at all. -/
theorem capped_budget_const (i : Nat → W64) : budget capped i = 23 := by
  simp [budget, capped, forMax, counters, push, pot, costOf, upd, eval, num, W64.ofNat]
  rfl

/-- And it is tight at the cap: with the body run every round the run costs 23, and 19 when it never runs. -/
theorem capped_runs : (src capped 1000 5 10).cost = 23 ∧ (src capped 1000 5 0).cost = 19 := by
  decide +kernel

/-- **So `capped` has a constant budget, `bound` itself**, through `bound_iff_boundR`. -/
theorem capped_bound (E : Type) (P : Nat → Bool) : Cert.bound (sliceLang E P) 23 capped := by
  refine (Cert.bound_iff_boundR _ _ _).mpr ?_
  intro i hi
  obtain ⟨k, hk, hb⟩ := slice_boundR E P capped_counted i hi
  exact ⟨k, by rw [hk]; exact capped_budget_const i.1, hb⟩

/-- **Refused, a loop that is not counted**: `spin`'s guard is a literal. -/
theorem spin_not_counted : counted spin = false := by decide

/-- **Refused, a counter assigned in the body.** -/
def resetInBody : Prog where
  inputs := ["s", "n"]
  body := .seq (.assign "c" (.var "n")) (.loop (.var "c") (.seq (.assign "c" (num 5)) (.assign "c" (.add (.var "c") minusOne))))
  ret := num 0
theorem resetInBody_not_counted : counted resetInBody = false := by decide

/-- **Refused, a counter set from a variable the program assigns.** -/
def fromAssigned : Prog where
  inputs := ["s", "n"]
  body := .seq (.assign "t" (num 7)) (forN "c" (.var "t") .skip)
  ret := num 0
theorem fromAssigned_not_counted : counted fromAssigned = false := by decide

/-- **Refused, a loop nested in a loop's body.** -/
def nested : Prog where
  inputs := ["s", "n"]
  body := forN "c" (.var "n") (forN "d" (.var "n") .skip)
  ret := num 0
theorem nested_not_counted : counted nested = false := by decide

/-- **Refused, a counter that is an input.** -/
def inputCounter : Prog where
  inputs := ["s", "n"]
  body := .loop (.var "n") (.seq .skip (.assign "n" (.add (.var "n") minusOne)))
  ret := num 0
theorem inputCounter_not_counted : counted inputCounter = false := by decide

end LCore.Slice2.Budget
