/-
  VS-1 step 3: the slice's source language, its checker, and `rel` and `bound` on it.

  A program names its inputs in order, runs assignments and branches over `W64`, and returns one word.
  Its input is `Inputs × E`, where `E` is the machine's passive environment, which the source ignores
  (`research/2026-11/VS-1-KERNEL.md`). The result is the event `Ev.ext "ret"`, emitted on finishing.

  **Attacker:** sees every event and all leakage (branch bits and positions), cost and outcome, and knows the
  inputs at public positions and the whole environment. Secrets are inputs at the positions `P` marks.

  **Limits.** No loops, heap, strings, functions or mediation. This is a statement about this language: nothing
  here reaches a machine until the passes of steps 5 to 7 carry it.
-/
import LCore.Kernel.Pass
import LCore.Slice.Word

namespace LCore.Slice

/-! ## The language -/

inductive Expr where
  | lit : W64 → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  /-- `^ | & -`, RC-01. -/
  | bin : Op → Expr → Expr → Expr
  /-- A logical shift right by a literal amount, RC-01. -/
  | shr : Expr → Nat → Expr
  deriving DecidableEq, Repr

inductive Cmd where
  | skip   : Cmd
  | assign : String → Expr → Cmd
  | seq    : Cmd → Cmd → Cmd
  | ite    : Expr → Cmd → Cmd → Cmd
  deriving DecidableEq, Repr

/-- A program: its inputs by position, its body, and what it returns. -/
structure Prog where
  inputs : List String
  body   : Cmd
  ret    : Expr
  deriving DecidableEq, Repr

abbrev Store := String → W64

def upd (s : Store) (x : String) (v : W64) : Store := fun y => if y = x then v else s y

def eval : Expr → Store → W64
  | .lit w, _   => w
  | .var x, s   => s x
  | .add a b, s => W64.add (eval a s) (eval b s)
  | .bin o a b, s => o.w (eval a s) (eval b s)
  | .shr a k, s => W64.shr (eval a s) k

/-- A frame: a command and its position. -/
abbrev Frame := Cmd × List Nat

/-- Flatten `seq` onto the frame stack. -/
def push : Cmd → List Nat → List Frame → List Frame
  | .seq a b, p, k => push a (p ++ [0]) (push b (p ++ [1]) k)
  | c, p, k => (c, p) :: k

/-- The event that returns a word. -/
def retEv (w : W64) : Ev := .ext "ret" [Int.ofNat w.val]

/-- One step at position `p`, with what else it leaks. -/
def tick (l : List Lk) (p : List Nat) (r : Beh) : Beh :=
  { r with cost := 1 + r.cost, lk := .step p :: (l ++ r.lk) }

/-- **The run**: `n` steps of the frame machine. On finishing, it returns `ret`. -/
def run (ret : Expr) : Nat → List Frame → Store → Beh
  | _, [], s => { ev := [retEv (eval ret s)], lk := [], cost := 0, out := .done }
  | 0, _ :: _, _ => { ev := [], lk := [], cost := 0, out := .fuel }
  | n + 1, (c, p) :: k, s =>
    match c with
    | .skip => tick [] p (run ret n k s)
    | .assign x e => tick [] p (run ret n k (upd s x (eval e s)))
    | .seq a b => run ret n (push a (p ++ [0]) (push b (p ++ [1]) k)) s
    | .ite e a b =>
      if (eval e s).val ≠ 0 then tick [.branch true] p (run ret n (push a (p ++ [0]) k) s)
      else tick [.branch false] p (run ret n (push b (p ++ [1]) k) s)

/-- The initial store: the input word at each name's position, and zero elsewhere. A name listed twice
    takes its first position. -/
def initFrom (v : Nat → W64) : List String → Nat → Store
  | [], _ => fun _ => W64.ofNat 0
  | x :: xs, k => fun y => if y = x then v k else initFrom v xs (k + 1) y

/-- How many input words the machine holds (the data segment's capacity). -/
def cap : Nat := 64

/-- **The source language.** `E` is the passive environment, and `P` marks the secret positions. -/
def sliceLang (E : Type) (P : Nat → Bool) : Lang where
  Prog  := Prog
  In    := (Nat → W64) × E
  lowIn i i' := ∀ k, P k = false → i.1 k = i'.1 k
  run n p i := run p.ret n (push p.body [] []) (initFrom i.1 p.inputs 0)
  Adm i := ∀ k, cap ≤ k → i.1 k = W64.ofNat 0

/-! ## Lawful -/

/-- More fuel only extends a run. -/
def Ext (a b : Beh) : Prop :=
  (a.out ≠ .fuel → a = b) ∧ a.ev <+: b.ev ∧ a.lk <+: b.lk ∧ a.cost ≤ b.cost

theorem Ext.refl (a : Beh) : Ext a a :=
  ⟨fun _ => rfl, List.prefix_refl _, List.prefix_refl _, Nat.le_refl _⟩

theorem tick_ext {a b : Beh} (l : List Lk) (p : List Nat) (h : Ext a b) :
    Ext (tick l p a) (tick l p b) := by
  refine ⟨fun hf => ?_, h.2.1, ?_, Nat.add_le_add_left h.2.2.2 _⟩
  · rw [h.1 hf]
  · obtain ⟨t, ht⟩ := h.2.2.1
    exact ⟨t, by simp [tick, ← ht]⟩

theorem run_ext (ret : Expr) : ∀ (n n' : Nat) (k : List Frame) (s : Store), n ≤ n' →
    Ext (run ret n k s) (run ret n' k s) := by
  intro n
  induction n with
  | zero =>
    intro n' k s _
    cases k with
    | nil => cases n' <;> exact Ext.refl _
    | cons f k => exact ⟨fun h => absurd rfl h, List.nil_prefix, List.nil_prefix, Nat.zero_le _⟩
  | succ m ih =>
    intro n' k s hle
    obtain ⟨m', rfl⟩ : ∃ m', n' = m' + 1 := ⟨n' - 1, by omega⟩
    have hm : m ≤ m' := by omega
    cases k with
    | nil => exact Ext.refl _
    | cons f k =>
      obtain ⟨c, p⟩ := f
      cases c with
      | skip => exact tick_ext _ _ (ih m' _ s hm)
      | assign x e => exact tick_ext _ _ (ih m' _ _ hm)
      | seq a b => exact ih m' _ s hm
      | ite e a b =>
        simp only [run]
        split
        · exact tick_ext _ _ (ih m' _ s hm)
        · exact tick_ext _ _ (ih m' _ s hm)

/-- No frame is a `seq`. -/
def NoSeq (k : List Frame) : Prop := ∀ f ∈ k, ∀ a b, f.1 ≠ .seq a b

theorem push_noSeq : ∀ (c : Cmd) (p : List Nat) (k : List Frame), NoSeq k → NoSeq (push c p k)
  | .seq a b, p, k, h => push_noSeq a _ _ (push_noSeq b _ k h)
  | .skip, _, k, h | .assign _ _, _, k, h | .ite _ _ _, _, k, h => by
    intro f hf a b
    simp only [push, List.mem_cons] at hf
    rcases hf with rfl | hf
    · simp
    · exact h f hf a b

theorem run_diverge (ret : Expr) : ∀ (n : Nat) (k : List Frame) (s : Store), NoSeq k →
    (run ret n k s).out = .fuel → n ≤ (run ret n k s).cost := by
  intro n
  induction n with
  | zero => intro _ _ _ _; exact Nat.zero_le _
  | succ m ih =>
    intro k s hk hf
    cases k with
    | nil => simp [run] at hf
    | cons f k =>
      obtain ⟨c, p⟩ := f
      have hk' : NoSeq k := fun x hx => hk x (List.mem_cons_of_mem _ hx)
      cases c with
      | skip =>
        simp only [run, tick] at hf ⊢
        have := ih k s hk' hf; omega
      | assign x e =>
        simp only [run, tick] at hf ⊢
        have := ih k _ hk' hf; omega
      | seq a b => exact absurd rfl (hk _ List.mem_cons_self a b)
      | ite e a b =>
        simp only [run] at hf ⊢
        split at hf
        · rename_i hg; rw [if_pos hg]; simp only [tick] at hf ⊢
          have := ih _ s (push_noSeq _ _ _ hk') hf; omega
        · rename_i hg; rw [if_neg hg]; simp only [tick] at hf ⊢
          have := ih _ s (push_noSeq _ _ _ hk') hf; omega

theorem sliceLang_lawful (E : Type) (P : Nat → Bool) : (sliceLang E P).Lawful where
  ev_mono p i n n' h := (run_ext _ n n' _ _ h).2.1
  lk_mono p i n n' h := (run_ext _ n n' _ _ h).2.2.1
  cost_mono p i n n' h := (run_ext _ n n' _ _ h).2.2.2
  stable p i n n' h hf := ((run_ext _ n n' _ _ h).1 hf).symm
  diverge p := ⟨0, fun n i h =>
    run_diverge _ n _ _ (push_noSeq _ _ _ (fun _ hx => by simp at hx)) h⟩

/-! ## The budget: every program has one, since nothing loops -/

def costOf : Cmd → Nat
  | .skip | .assign _ _ => 1
  | .seq a b => costOf a + costOf b
  | .ite _ a b => 1 + max (costOf a) (costOf b)

def costK : List Frame → Nat
  | [] => 0
  | (c, _) :: k => costOf c + costK k

theorem costK_push : ∀ (c : Cmd) (p : List Nat) (k : List Frame),
    costK (push c p k) = costOf c + costK k
  | .seq a b, p, k => by
    simp only [push, costK_push a, costK_push b, costOf]; omega
  | .skip, _, _ | .assign _ _, _, _ | .ite _ _ _, _, _ => rfl

theorem run_cost (ret : Expr) : ∀ (n : Nat) (k : List Frame) (s : Store),
    (run ret n k s).cost ≤ costK k := by
  intro n
  induction n with
  | zero => intro k s; cases k <;> simp [run]
  | succ m ih =>
    intro k s
    cases k with
    | nil => simp [run]
    | cons f k =>
      obtain ⟨c, p⟩ := f
      cases c with
      | skip =>
        have := ih k s
        simp only [run, tick, costK, costOf]; omega
      | assign x e =>
        have := ih k (upd s x (eval e s))
        simp only [run, tick, costK, costOf]; omega
      | seq a b =>
        have := ih (push a (p ++ [0]) (push b (p ++ [1]) k)) s
        rw [costK_push, costK_push] at this
        simp only [run, costK, costOf]; omega
      | ite e a b =>
        simp only [run]
        split
        · have := ih (push a (p ++ [0]) k) s
          rw [costK_push] at this
          simp only [tick, costK, costOf]; omega
        · have := ih (push b (p ++ [1]) k) s
          rw [costK_push] at this
          simp only [tick, costK, costOf]; omega

/-- **`bound` on the source.** -/
theorem slice_bound (E : Type) (P : Nat → Bool) (p : Prog) :
    Cert.bound (sliceLang E P) (costOf p.body) p := by
  intro n i _
  have := run_cost p.ret n (push p.body [] []) (initFrom i.1 p.inputs 0)
  rw [costK_push] at this
  show (run p.ret n (push p.body [] []) (initFrom i.1 p.inputs 0)).cost ≤ costOf p.body
  simpa [costK] using this

/-! ## The checker -/

/-- Does this expression read a variable in `H`, the ones that may hold a secret? -/
def highE (H : List String) : Expr → Bool
  | .lit _   => false
  | .var x   => decide (x ∈ H)
  | .add a b | .bin _ a b => highE H a || highE H b
  | .shr a _ => highE H a

/-- Track which variables may hold a secret. `none` refuses a branch on a secret. -/
def highC (H : List String) : Cmd → Option (List String)
  | .skip => some H
  | .assign x e => if highE H e then some (x :: H) else some (H.filter (· ≠ x))
  | .seq a b => (highC H a).bind fun H₁ => highC H₁ b
  | .ite e a b =>
    if highE H e then none
    else (highC H a).bind fun Ha => (highC H b).map fun Hb => Ha ++ Hb

/-- The names at secret positions. -/
def highInit (P : Nat → Bool) : List String → Nat → List String
  | [], _ => []
  | x :: xs, k => if P k then x :: highInit P xs (k + 1) else highInit P xs (k + 1)

/-- **The checker**: no branch on a secret, and no secret in the result. Its answer is the budget. -/
def sliceCheck (P : Nat → Bool) (p : Prog) : Option Nat :=
  (highC (highInit P p.inputs 0) p.body).bind fun H =>
    if highE H p.ret then none else some (costOf p.body)

/-! ## `rel` -/

/-- Two stores that agree on everything not in `H`. -/
def Low (H : List String) (s s' : Store) : Prop := ∀ x, x ∉ H → s x = s' x

theorem Low.mono {H H' : List String} {s s' : Store} (hs : ∀ x, x ∈ H → x ∈ H') (h : Low H s s') :
    Low H' s s' :=
  fun x hx => h x (fun hm => hx (hs x hm))

theorem eval_low {H : List String} {s s' : Store} (h : Low H s s') :
    ∀ e, highE H e = false → eval e s = eval e s'
  | .lit _, _ => rfl
  | .var x, he => h x (by simpa [highE] using he)
  | .add a b, he | .bin _ a b, he => by
    simp only [highE, Bool.or_eq_false_iff] at he
    simp only [eval, eval_low h a he.1, eval_low h b he.2]
  | .shr a _, he => by
    simp only [highE] at he
    simp only [eval, eval_low h a he]

/-- Frames the checker accepts, ending where the result is low. A later frame may track more than an
    earlier one ended with, which is what the arms of a branch need. -/
inductive FT (ret : Expr) : List String → List Frame → Prop where
  | nil  : ∀ {H}, highE H ret = false → FT ret H []
  | cons : ∀ {H H₁ H₂ : List String} {c : Cmd} {p : List Nat} {k : List Frame},
      highC H c = some H₁ → (∀ x, x ∈ H₁ → x ∈ H₂) → FT ret H₂ k → FT ret H ((c, p) :: k)

theorem push_ft {ret : Expr} : ∀ (c : Cmd) (p : List Nat) {H H₁ H₂ : List String} {k : List Frame},
    highC H c = some H₁ → (∀ x, x ∈ H₁ → x ∈ H₂) → FT ret H₂ k → FT ret H (push c p k)
  | .seq a b, p, H, H₁, H₂, k, hc, hs, hk => by
    simp only [highC] at hc
    rcases ea : highC H a with _ | Ha
    · rw [ea] at hc; simp at hc
    · rw [ea, Option.bind_some] at hc
      exact push_ft a _ ea (fun _ h => h) (push_ft b _ hc hs hk)
  | .skip, _, _, _, _, _, hc, hs, hk | .assign _ _, _, _, _, _, _, hc, hs, hk
  | .ite _ _ _, _, _, _, _, _, hc, hs, hk => FT.cons hc hs hk

/-- **Two low-equal runs of accepted frames show the same, at every fuel.** -/
theorem run_same {ret : Expr} : ∀ (n : Nat) (H : List String) (k : List Frame) (s s' : Store),
    FT ret H k → Low H s s' → run ret n k s = run ret n k s' := by
  intro n
  induction n with
  | zero =>
    intro H k s s' hk hl
    cases hk with
    | nil he => simp only [run, eval_low hl _ he]
    | cons => rfl
  | succ m ih =>
    intro H k s s' hk hl
    cases hk with
    | nil he => simp only [run, eval_low hl _ he]
    | @cons H H₁ H₂ c p k hc hs hk' =>
      cases c with
      | skip =>
        simp only [highC, Option.some.injEq] at hc
        subst hc
        simp only [run]
        rw [ih _ _ s s' hk' (Low.mono hs hl)]
      | assign x e =>
        simp only [run]
        have hnew : Low H₁ (upd s x (eval e s)) (upd s' x (eval e s')) := by
          intro y hy
          simp only [highC] at hc
          split at hc
          · simp only [Option.some.injEq] at hc
            subst hc
            have hne : y ≠ x := fun h => hy (by simp [h])
            have hyH : y ∉ H := fun h => hy (List.mem_cons_of_mem _ h)
            simp [upd, hne, hl y hyH]
          · rename_i he
            simp only [Option.some.injEq] at hc
            subst hc
            by_cases hyx : y = x
            · simp [upd, hyx, eval_low hl e (by simpa using he)]
            · have hyH : y ∉ H := fun h => hy (List.mem_filter.mpr ⟨h, by simpa using hyx⟩)
              simp [upd, hyx, hl y hyH]
        rw [ih _ _ _ _ hk' (Low.mono hs hnew)]
      | seq a b =>
        simp only [highC] at hc
        rcases ea : highC H a with _ | Ha
        · rw [ea] at hc; simp at hc
        rw [ea, Option.bind_some] at hc
        exact ih _ _ s s' (push_ft a _ ea (fun _ h => h) (push_ft b _ hc hs hk')) hl
      | ite e a b =>
        simp only [highC] at hc
        split at hc
        · simp at hc
        rename_i he
        rcases ea : highC H a with _ | Ha
        · rw [ea] at hc; simp at hc
        rw [ea, Option.bind_some] at hc
        rcases eb : highC H b with _ | Hb
        · rw [eb] at hc; simp at hc
        rw [eb] at hc
        simp only [Option.map_some, Option.some.injEq] at hc
        subst hc
        have hg : eval e s = eval e s' := eval_low hl e (by simpa using he)
        simp only [run, hg]
        split
        · rw [ih _ _ s s' (push_ft a _ ea
            (fun x h => hs x (List.mem_append_left _ h)) hk') hl]
        · rw [ih _ _ s s' (push_ft b _ eb
            (fun x h => hs x (List.mem_append_right _ h)) hk') hl]

/-- The initial stores of two inputs that agree at public positions agree off the secret names. -/
theorem initFrom_low {P : Nat → Bool} {v v' : Nat → W64} (h : ∀ k, P k = false → v k = v' k) :
    ∀ (xs : List String) (k : Nat), Low (highInit P xs k) (initFrom v xs k) (initFrom v' xs k)
  | [], _ => fun _ _ => rfl
  | x :: xs, k => by
    intro y hy
    simp only [initFrom]
    cases hP : P k with
    | true =>
      simp only [highInit, hP, ↓reduceIte, List.mem_cons, not_or] at hy
      simp only [hy.1, ↓reduceIte]
      exact initFrom_low h xs (k + 1) y hy.2
    | false =>
      simp only [highInit, hP, Bool.false_eq_true, ↓reduceIte] at hy
      by_cases hyx : y = x
      · simp only [hyx, ↓reduceIte, h k hP]
      · simp only [hyx, ↓reduceIte]
        exact initFrom_low h xs (k + 1) y hy

/-- **`rel` on the source.** What the checker accepts shows the same, at every fuel, on inputs that agree at
    public positions, whatever the environment. -/
theorem sliceCheck_rel {E : Type} {P : Nat → Bool} {p : Prog} {k : Nat} (h : sliceCheck P p = some k) :
    Cert.rel (sliceLang E P) p := by
  intro n i i' _ _ hi
  simp only [sliceCheck] at h
  rcases eh : highC (highInit P p.inputs 0) p.body with _ | H
  · rw [eh] at h; simp at h
  rw [eh, Option.bind_some] at h
  split at h
  · simp at h
  rename_i hr
  exact run_same n _ _ _ _
    (push_ft p.body [] eh (fun _ h => h) (FT.nil (by simpa using hr)))
    (initFrom_low hi p.inputs 0)

/-- **What the checker's answer means**: the budget. -/
theorem sliceCheck_bound {E : Type} {P : Nat → Bool} {p : Prog} {k : Nat} (h : sliceCheck P p = some k) :
    Cert.bound (sliceLang E P) k p := by
  simp only [sliceCheck] at h
  rcases eh : highC (highInit P p.inputs 0) p.body with _ | H
  · rw [eh] at h; simp at h
  rw [eh, Option.bind_some] at h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    subst h
    exact slice_bound E P p

/-! ## Witnesses -/

/-- Position 0 is secret; position 1 is public. -/
def sec0 : Nat → Bool := fun k => k == 0

/-- An input with `a` at position 0 and `b` at position 1. -/
def inp (a b : Nat) : Nat → W64 :=
  fun k => if k = 0 then W64.ofNat a else if k = 1 then W64.ofNat b else W64.ofNat 0

theorem inp_adm (a b k : Nat) (h : cap ≤ k) : inp a b k = W64.ofNat 0 := by
  have : cap = 64 := rfl
  have h0 : k ≠ 0 := by omega
  have h1 : k ≠ 1 := by omega
  simp [inp, h0, h1]

theorem inp_low (a a' b : Nat) : ∀ k, sec0 k = false → inp a b k = inp a' b k := by
  intro k hk
  have h0 : k ≠ 0 := by
    intro h; subst h; simp [sec0] at hk
  simp [inp, h0]

/-- Refuted by a pair of inputs that differ only in the secret. -/
theorem leak_of_ne {p : Prog} (hne : (sliceLang Unit sec0).run 20 p (inp 5 1, ()) ≠
    (sliceLang Unit sec0).run 20 p (inp 6 1, ())) : ¬ Cert.rel (sliceLang Unit sec0) p :=
  fun h => hne (h 20 _ _ (inp_adm 5 1) (inp_adm 6 1) (inp_low 5 6 1))

/-- **Accepted**: a public branch, with the secret read and overwritten before the result. -/
def clean : Prog where
  inputs := ["s", "b"]
  body := .seq (.assign "t" (.add (.var "s") (.lit (W64.ofNat 1))))
    (.seq (.assign "t" (.var "b"))
      (.ite (.var "b") (.assign "t" (.add (.var "t") (.var "b"))) .skip))
  ret := .var "t"

theorem clean_checks : sliceCheck sec0 clean = some 4 := by decide

theorem clean_rel (E : Type) : Cert.rel (sliceLang E sec0) clean := sliceCheck_rel clean_checks
theorem clean_bound (E : Type) : Cert.bound (sliceLang E sec0) 4 clean := sliceCheck_bound clean_checks

/-- **The accepted program does something**: it finishes, with the result it should, and its result depends
    on the public input, so `rel` is not vacuous here. -/
theorem clean_runs :
    ((sliceLang Unit sec0).run 20 clean (inp 5 3, ())).ev = [retEv (W64.ofNat 6)]
  ∧ ((sliceLang Unit sec0).run 20 clean (inp 5 3, ())).out = .done
  ∧ ((sliceLang Unit sec0).run 20 clean (inp 5 3, ())).cost = 4
  ∧ (sliceLang Unit sec0).run 20 clean (inp 5 3, ()) ≠ (sliceLang Unit sec0).run 20 clean (inp 5 0, ()) := by
  decide

/-- Words wrap, on the source too. -/
theorem wraps_in_source :
    ((sliceLang Unit sec0).run 20
      { inputs := ["s", "b"], body := .skip, ret := .add (.lit (W64.ofNat (2 ^ 64 - 1))) (.var "b") }
      (inp 5 1, ())).ev = [retEv (W64.ofNat 0)] := by
  decide

/-- **Refused, the branch rule**, and the branch does leak. -/
def secretBranch : Prog where
  inputs := ["s", "b"]
  body := .ite (.var "s") .skip (.seq .skip .skip)
  ret := .lit (W64.ofNat 0)

theorem secretBranch_refused : sliceCheck sec0 secretBranch = none := by decide

/-- It needs a secret that is zero on one side, to take the other arm. -/
theorem secretBranch_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretBranch := by
  intro h
  have := h 20 (inp 0 1, ()) (inp 6 1, ()) (inp_adm 0 1) (inp_adm 6 1) (inp_low 0 6 1)
  revert this; decide

/-- **Refused, the result rule**, and the result leaks. -/
def secretRet : Prog where
  inputs := ["s", "b"]
  body := .skip
  ret := .var "s"

theorem secretRet_refused : sliceCheck sec0 secretRet = none := by decide
theorem secretRet_leaks : ¬ Cert.rel (sliceLang Unit sec0) secretRet := leak_of_ne (by decide)

/-- **Refused, the assignment rule**: a secret through two variables. -/
def laundered : Prog where
  inputs := ["s", "b"]
  body := .seq (.assign "x" (.var "s")) (.assign "y" (.add (.var "x") (.lit (W64.ofNat 1))))
  ret := .var "y"

theorem laundered_refused : sliceCheck sec0 laundered = none := by decide
theorem laundered_leaks : ¬ Cert.rel (sliceLang Unit sec0) laundered := leak_of_ne (by decide)

/-- **Refused, the join rule**: a secret in one arm of a public branch. -/
def oneArm : Prog where
  inputs := ["s", "b"]
  body := .ite (.var "b") (.assign "x" (.var "s")) (.assign "x" (.lit (W64.ofNat 0)))
  ret := .var "x"

theorem oneArm_refused : sliceCheck sec0 oneArm = none := by decide
theorem oneArm_leaks : ¬ Cert.rel (sliceLang Unit sec0) oneArm := leak_of_ne (by decide)

/-- **Refused**: a secret listed under a name that is also public. The checker marks the name secret. -/
def shadowed : Prog where
  inputs := ["s", "s"]
  body := .skip
  ret := .var "s"

theorem shadowed_refused : sliceCheck sec0 shadowed = none := by decide
theorem shadowed_leaks : ¬ Cert.rel (sliceLang Unit sec0) shadowed := leak_of_ne (by decide)

/-- **The environment changes nothing on the source**: it is passive here. Step 5 must prove the same on the
    compiled program, where it is not free. -/
theorem env_passive (p : Prog) (P : Nat → Bool) (n : Nat) (v : Nat → W64) (e e' : Bool) :
    (sliceLang Bool P).run n p (v, e) = (sliceLang Bool P).run n p (v, e') := rfl

end LCore.Slice
