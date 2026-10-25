/-
  Heap and memory safety — brick 11, the memory-safety sub-project, brick 1.

  Every prior brick certified *confidentiality* channels (store, timing,
  termination). Memory safety is a different kind of property — a *safety*
  property of a richer machine: the semantics can get **stuck** on an invalid
  dereference (a wild pointer, an out-of-bounds access). The map has carried
  memory safety as CARRIED since brick 1 — transported across seams but not
  *generated*. This sub-project generates it.

  The machine (additive: fresh `MCmd`/`MState`, the 26 existing modules
  untouched) has a heap and an allocation high-water mark `n`: addresses in
  `[0, n)` are allocated, everything else is wild. `mexec` returns
  `Option MState` — `none` is a **memory error** (a dereference of a wild
  address), the stuck state. Memory safety is "never `none`".

  The checker `mcheck` is flow-sensitive: it tracks the set of variables known
  to hold valid (in-bounds) addresses, allows a load/store only through such a
  variable, and `alloc` grows the set. Soundness (`mcheck_safe`) is the
  by-construction guarantee: **a checked program never hits a memory error, and
  its checker-tracked pointers stay valid** — proved by induction on an
  invariant tying the tracked set to the heap's allocated region. Teeth
  (`mwild_store_errors`, `mwild_rejected`): an unchecked wild store both errors at
  runtime and is rejected by the checker — the two agree the access is unsafe.
-/
import ConfTyping.Imp

namespace ConfTyping

-- Lean 4.35: plain `simp` closes `x ≤ x` on `Int` with `Std.le_refl` at the `Int` order
-- package, which depends on `Classical.choice`. Use `Int.le_refl`, as under 4.31 (P0-02).
attribute [-simp] Std.le_refl
attribute [local simp] Int.le_refl

/-! ## The heap machine -/

/-- The heap: a total map on addresses; only the region `[0, n)` is allocated. -/
abbrev Heap := Int → Int

/-- Machine state: variables, heap, and the allocation high-water mark `n`
    (addresses `[0, n)` are live). -/
abbrev MState := Store × Heap × Nat

/-- Update a heap cell. -/
def updH (h : Heap) (a : Int) (v : Int) : Heap := fun b => if b = a then v else h b

/-- An address is valid iff it lies in the allocated region. -/
def validB (a : Int) (n : Nat) : Bool := decide (0 ≤ a) && decide (a < n)

/-- Heap commands: pure assignment, control flow, and the three memory
    operations — allocate a fresh cell, load through a pointer, store through a
    pointer. -/
inductive MCmd where
  | skip   : MCmd
  | assign : String → Expr → MCmd
  | seq    : MCmd → MCmd → MCmd
  | ite    : Expr → MCmd → MCmd → MCmd
  | alloc  : String → MCmd          -- x := fresh cell address
  | load   : String → String → MCmd -- y := *x
  | store  : String → Expr → MCmd   -- *x := e

/-- The heap semantics. `none` is a **memory error**: a load or store through a
    wild (non-allocated) address. `alloc` hands back a fresh address `n` and
    grows the live region. -/
def mexec : MCmd → MState → Option MState
  | .skip,        s => some s
  | .assign x e,  (σ, h, n) => some (upd σ x (evalE e σ), h, n)
  | .seq c₁ c₂,   s => (mexec c₁ s).bind (mexec c₂)
  | .ite e c₁ c₂, (σ, h, n) =>
      if evalE e σ ≠ 0 then mexec c₁ (σ, h, n) else mexec c₂ (σ, h, n)
  | .alloc x,     (σ, h, n) => some (upd σ x (n : Int), updH h (n : Int) 0, n + 1)
  | .load y x,    (σ, h, n) =>
      if validB (σ x) n then some (upd σ y (h (σ x)), h, n) else none
  | .store x e,   (σ, h, n) =>
      if validB (σ x) n then some (σ, updH h (σ x) (evalE e σ), n) else none

/-! ## The invariant and the flow-sensitive checker -/

/-- The memory-safety invariant: every checker-tracked variable holds a valid
    (in-bounds) address. -/
def Inv (V : List String) : MState → Prop
  | (σ, _, n) => ∀ x ∈ V, 0 ≤ σ x ∧ σ x < n

/-- List intersection via filter (mathlib-free, with the membership lemma we
    need from core `List.mem_filter`). -/
def inter (V₁ V₂ : List String) : List String :=
  V₁.filter (fun x => decide (x ∈ V₂))

/-- Remove a variable from the tracked set, via filter (clean `mem_filter`
    lemmas mathlib-free, unlike `List.erase`). -/
def remove (x : String) (V : List String) : List String :=
  V.filter (fun y => decide (y ≠ x))

/-- The flow-sensitive checker: threads the set of known-valid pointer
    variables, and returns `none` if any memory op dereferences an untracked
    variable. -/
def mcheck (V : List String) : MCmd → Option (List String)
  | .skip        => some V
  | .assign x _  => some (remove x V)
  | .seq c₁ c₂   => (mcheck V c₁).bind (fun V₁ => mcheck V₁ c₂)
  | .ite _ c₁ c₂ =>
      match mcheck V c₁, mcheck V c₂ with
      | some V₁, some V₂ => some (inter V₁ V₂)
      | _, _ => none
  | .alloc x     => some (x :: V)
  | .load y x    => if x ∈ V then some (remove y V) else none
  | .store x _   => if x ∈ V then some V else none

/-! ## Soundness: a checked program never errors -/

theorem inter_subset_left {z : String} {V₁ V₂ : List String}
    (h : z ∈ inter V₁ V₂) : z ∈ V₁ :=
  (List.mem_filter.mp h).1

theorem inter_subset_right {z : String} {V₁ V₂ : List String}
    (h : z ∈ inter V₁ V₂) : z ∈ V₂ := by
  have := (List.mem_filter.mp h).2
  simpa using of_decide_eq_true this

theorem mem_of_mem_remove {z x : String} {V : List String}
    (h : z ∈ remove x V) : z ∈ V :=
  (List.mem_filter.mp h).1

theorem ne_of_mem_remove {z x : String} {V : List String}
    (h : z ∈ remove x V) : z ≠ x := by
  have := (List.mem_filter.mp h).2
  simpa using of_decide_eq_true this

/-- **Memory safety, by construction.** If the checker accepts `c` from a state
    satisfying the input invariant, then `c` runs without a memory error and its
    result satisfies the output invariant. The tracked pointers stay valid, and
    every dereference is therefore in bounds. -/
theorem mcheck_safe :
    ∀ (c : MCmd) (V V' : List String) (s : MState),
      mcheck V c = some V' → Inv V s →
      ∃ s', mexec c s = some s' ∧ Inv V' s' := by
  intro c
  induction c with
  | skip =>
      intro V V' s hchk hinv
      simp only [mcheck, Option.some.injEq] at hchk; subst hchk
      exact ⟨s, rfl, hinv⟩
  | assign x e =>
      intro V V' s hchk hinv
      simp only [mcheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨σ, h, n⟩ := s
      refine ⟨(upd σ x (evalE e σ), h, n), rfl, ?_⟩
      intro z hz
      have hzV : z ∈ V := mem_of_mem_remove hz
      have hzx : z ≠ x := ne_of_mem_remove hz
      have := hinv z hzV
      simpa [upd, hzx] using this
  | seq c₁ c₂ ih₁ ih₂ =>
      intro V V' s hchk hinv
      simp only [mcheck, Option.bind_eq_bind] at hchk
      cases hV₁ : mcheck V c₁ with
      | none => rw [hV₁] at hchk; simp at hchk
      | some V₁ =>
          rw [hV₁] at hchk
          simp only [Option.bind_some] at hchk
          obtain ⟨s₁, hs₁, hinv₁⟩ := ih₁ V V₁ s hV₁ hinv
          obtain ⟨s', hs', hinv'⟩ := ih₂ V₁ V' s₁ hchk hinv₁
          refine ⟨s', ?_, hinv'⟩
          show (mexec c₁ s).bind (mexec c₂) = some s'
          rw [hs₁, Option.bind_some, hs']
  | ite e c₁ c₂ ih₁ ih₂ =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n⟩ := s
      simp only [mcheck] at hchk
      cases hV₁ : mcheck V c₁ with
      | none => rw [hV₁] at hchk; simp at hchk
      | some V₁ =>
          cases hV₂ : mcheck V c₂ with
          | none => rw [hV₁, hV₂] at hchk; simp at hchk
          | some V₂ =>
              rw [hV₁, hV₂] at hchk
              simp only [Option.some.injEq] at hchk; subst hchk
              by_cases hb : evalE e σ ≠ 0
              · obtain ⟨s', hs', hinv'⟩ := ih₁ V V₁ (σ, h, n) hV₁ hinv
                refine ⟨s', ?_, ?_⟩
                · show (if evalE e σ ≠ 0 then _ else _) = some s'
                  rw [if_pos hb]; exact hs'
                · intro z hz; exact hinv' z (inter_subset_left hz)
              · obtain ⟨s', hs', hinv'⟩ := ih₂ V V₂ (σ, h, n) hV₂ hinv
                refine ⟨s', ?_, ?_⟩
                · show (if evalE e σ ≠ 0 then _ else _) = some s'
                  rw [if_neg hb]; exact hs'
                · intro z hz; exact hinv' z (inter_subset_right hz)
  | alloc x =>
      intro V V' s hchk hinv
      simp only [mcheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨σ, h, n⟩ := s
      refine ⟨(upd σ x (n : Int), updH h (n : Int) 0, n + 1), rfl, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hzV
      · have hu : upd σ z (n : Int) z = (n : Int) := by simp [upd]
        rw [hu]; omega
      · by_cases hzx : z = x
        · subst hzx
          have hu : upd σ z (n : Int) z = (n : Int) := by simp [upd]
          rw [hu]; omega
        · have hval := hinv z hzV
          have hu : upd σ x (n : Int) z = σ z := by simp [upd, hzx]
          rw [hu]; omega
  | load y x =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n⟩ := s
      simp only [mcheck] at hchk
      by_cases hxV : x ∈ V
      · rw [if_pos hxV] at hchk
        simp only [Option.some.injEq] at hchk; subst hchk
        have hval := hinv x hxV
        have hvb : validB (σ x) n = true := by
          simp only [validB, Bool.and_eq_true, decide_eq_true_eq]; exact hval
        refine ⟨(upd σ y (h (σ x)), h, n), ?_, ?_⟩
        · show (if validB (σ x) n then _ else _) = _
          rw [if_pos hvb]
        · intro z hz
          have hzV : z ∈ V := mem_of_mem_remove hz
          have hzy : z ≠ y := ne_of_mem_remove hz
          have := hinv z hzV
          simpa [upd, hzy] using this
      · rw [if_neg hxV] at hchk; simp at hchk
  | store x e =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n⟩ := s
      simp only [mcheck] at hchk
      by_cases hxV : x ∈ V
      · rw [if_pos hxV] at hchk
        simp only [Option.some.injEq] at hchk; subst hchk
        have hval := hinv x hxV
        have hvb : validB (σ x) n = true := by
          simp only [validB, Bool.and_eq_true, decide_eq_true_eq]; exact hval
        refine ⟨(σ, updH h (σ x) (evalE e σ), n), ?_, ?_⟩
        · show (if validB (σ x) n then _ else _) = _
          rw [if_pos hvb]
        · exact hinv
      · rw [if_neg hxV] at hchk; simp at hchk

/-- **Certified memory-safe by `decide`.** From the empty tracked set (no
    assumed-valid pointers) a checked program runs to a real state — never a
    memory error. -/
theorem msafe_of_check {c : MCmd} {V' : List String}
    (h : mcheck [] c = some V') (s : MState) :
    ∃ s', mexec c s = some s' := by
  obtain ⟨s', hs', _⟩ := mcheck_safe c [] V' s h (by intro _ hz; cases hz)
  exact ⟨s', hs'⟩

/-! ## Non-vacuity and teeth -/

/-- A safe program: allocate, store through the fresh pointer, read it back. -/
def MPsafe : MCmd :=
  .seq (.alloc "p") (.seq (.store "p" (.num 5)) (.load "q" "p"))

theorem mpsafe_checks : (mcheck [] MPsafe).isSome = true := by decide

/-- Certified: `P_safe` never commits a memory error, from any start state. -/
theorem mpsafe_memsafe (s : MState) : ∃ s', mexec MPsafe s = some s' := by
  obtain ⟨V', hV'⟩ := Option.isSome_iff_exists.mp mpsafe_checks
  exact msafe_of_check hV' s

/-- A wild program: store through `p` without allocating it. -/
def MPwild : MCmd := .store "p" (.num 5)

/-- **The wild store errors.** From the initial state (`p = 0`, nothing
    allocated so `n = 0`), storing through `p` dereferences address `0 ≥ n` — a
    memory error. -/
theorem mwild_store_errors :
    mexec MPwild (fun _ => 0, fun _ => 0, 0) = none := by
  simp [mexec, MPwild, validB]

/-- **The checker rejects it** — `p` is not a tracked valid pointer. Checker and
    semantics agree the access is unsafe. -/
theorem mwild_rejected : mcheck [] MPwild = none := by decide

end ConfTyping
