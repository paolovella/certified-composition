/-
  Free and use-after-free — brick 12, the memory-safety sub-project, brick 2.

  Brick 11's machine could only *grow* the live region (a high-water mark), so
  the only memory error was a wild address. The real prize is **use-after-free**
  (CWE-416): dereferencing a pointer whose cell has been freed. That needs a
  machine that can *shrink* the live set, so the state carries a **liveness map**
  `L : Int → Bool` (freshness still from a mark `n`, but a live cell can be
  freed), and `free` is a new operation. `fexec` returns `none` on a
  use-after-free *or* a double-free.

  Freeing is sound only under a **linearity** discipline: the checker's tracked
  pointers must hold *distinct* live addresses, so freeing one cannot dangle
  another (there are no tracked aliases). The invariant `FInv` carries exactly
  that — tracked ⟹ live, tracked ⟹ in-bounds, and tracked addresses pairwise
  distinct — and soundness (`fcheck_safe`) proves a checked program never hits a
  use-after-free or double-free. Since pointers are produced only by `alloc`
  (never copied into another tracked variable), the mark keeps every tracked
  address distinct for free.

  The witness (`uaf_errors`, `uaf_rejected`): `alloc p; free p; store p 5`
  dereferences a freed cell — a memory error at runtime, and rejected by the
  checker, which drops `p` from the tracked set at the `free`. Double-free
  (`double_free_errors`) is caught the same way.
-/
import ConfTyping.MemSafe

namespace ConfTyping

/-! ## The machine with free -/

/-- Machine state with a liveness map: `(vars, heap, fresh-mark, live)`.
    `L a = true` iff address `a` is currently allocated. -/
abbrev FState := Store × Heap × Nat × (Int → Bool)

/-- Update the liveness map. -/
def updB (L : Int → Bool) (a : Int) (b : Bool) : Int → Bool :=
  fun c => if c = a then b else L c

/-- Heap commands with `free`. -/
inductive FCmd where
  | skip   : FCmd
  | assign : String → Expr → FCmd
  | seq    : FCmd → FCmd → FCmd
  | ite    : Expr → FCmd → FCmd → FCmd
  | alloc  : String → FCmd
  | free   : String → FCmd          -- free the cell pointed to by x
  | load   : String → String → FCmd
  | store  : String → Expr → FCmd

/-- The semantics. `none` is a memory error: a load/store/free through a
    non-live (wild or freed) address. `alloc` takes a fresh address `n` and
    marks it live; `free` marks the address dead. -/
def fexec : FCmd → FState → Option FState
  | .skip,        s => some s
  | .assign x e,  (σ, h, n, L) => some (upd σ x (evalE e σ), h, n, L)
  | .seq c₁ c₂,   s => (fexec c₁ s).bind (fexec c₂)
  | .ite e c₁ c₂, (σ, h, n, L) =>
      if evalE e σ ≠ 0 then fexec c₁ (σ, h, n, L) else fexec c₂ (σ, h, n, L)
  | .alloc x,     (σ, h, n, L) =>
      some (upd σ x (n : Int), updH h (n : Int) 0, n + 1, updB L (n : Int) true)
  | .free x,      (σ, h, n, L) =>
      if L (σ x) then some (σ, h, n, updB L (σ x) false) else none
  | .load y x,    (σ, h, n, L) =>
      if L (σ x) then some (upd σ y (h (σ x)), h, n, L) else none
  | .store x e,   (σ, h, n, L) =>
      if L (σ x) then some (σ, updH h (σ x) (evalE e σ), n, L) else none

/-! ## The linearity invariant -/

/-- Tracked pointers are live, in-bounds, and pairwise distinct — the last
    clause (linearity) is what makes `free` sound. -/
def FInv (V : List String) : FState → Prop
  | (σ, _, n, L) =>
      (∀ x ∈ V, L (σ x) = true) ∧
      (∀ x ∈ V, 0 ≤ σ x ∧ σ x < n) ∧
      (∀ x ∈ V, ∀ y ∈ V, x ≠ y → σ x ≠ σ y)

/-- The flow-sensitive checker: `free x` requires `x` tracked and drops it. -/
def fcheck (V : List String) : FCmd → Option (List String)
  | .skip        => some V
  | .assign x _  => some (remove x V)
  | .seq c₁ c₂   => (fcheck V c₁).bind (fun V₁ => fcheck V₁ c₂)
  | .ite _ c₁ c₂ =>
      match fcheck V c₁, fcheck V c₂ with
      | some V₁, some V₂ => some (inter V₁ V₂)
      | _, _ => none
  | .alloc x     => some (x :: V)
  | .free x      => if x ∈ V then some (remove x V) else none
  | .load y x    => if x ∈ V then some (remove y V) else none
  | .store x _   => if x ∈ V then some V else none

/-! ## Soundness: no use-after-free, no double-free -/

/-- **Memory safety with free, by construction.** A checked program never hits a
    use-after-free or double-free, and the linearity invariant is preserved. -/
theorem fcheck_safe :
    ∀ (c : FCmd) (V V' : List String) (s : FState),
      fcheck V c = some V' → FInv V s →
      ∃ s', fexec c s = some s' ∧ FInv V' s' := by
  intro c
  induction c with
  | skip =>
      intro V V' s hchk hinv
      simp only [fcheck, Option.some.injEq] at hchk; subst hchk
      exact ⟨s, rfl, hinv⟩
  | assign x e =>
      intro V V' s hchk hinv
      simp only [fcheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨σ, h, n, L⟩ := s
      obtain ⟨hli, hbd, hds⟩ := hinv
      refine ⟨(upd σ x (evalE e σ), h, n, L), rfl, ?_, ?_, ?_⟩
      · intro z hz
        have hzx : z ≠ x := ne_of_mem_remove hz
        have := hli z (mem_of_mem_remove hz); simpa [upd, hzx] using this
      · intro z hz
        have hzx : z ≠ x := ne_of_mem_remove hz
        have := hbd z (mem_of_mem_remove hz); simpa [upd, hzx] using this
      · intro z hz w hw hzw
        have hzx : z ≠ x := ne_of_mem_remove hz
        have hwx : w ≠ x := ne_of_mem_remove hw
        have := hds z (mem_of_mem_remove hz) w (mem_of_mem_remove hw) hzw
        simpa [upd, hzx, hwx] using this
  | seq c₁ c₂ ih₁ ih₂ =>
      intro V V' s hchk hinv
      simp only [fcheck, Option.bind_eq_bind] at hchk
      cases hV₁ : fcheck V c₁ with
      | none => rw [hV₁] at hchk; simp at hchk
      | some V₁ =>
          rw [hV₁] at hchk; simp only [Option.bind_some] at hchk
          obtain ⟨s₁, hs₁, hinv₁⟩ := ih₁ V V₁ s hV₁ hinv
          obtain ⟨s', hs', hinv'⟩ := ih₂ V₁ V' s₁ hchk hinv₁
          refine ⟨s', ?_, hinv'⟩
          show (fexec c₁ s).bind (fexec c₂) = some s'
          rw [hs₁, Option.bind_some, hs']
  | ite e c₁ c₂ ih₁ ih₂ =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n, L⟩ := s
      simp only [fcheck] at hchk
      cases hV₁ : fcheck V c₁ with
      | none => rw [hV₁] at hchk; simp at hchk
      | some V₁ =>
          cases hV₂ : fcheck V c₂ with
          | none => rw [hV₁, hV₂] at hchk; simp at hchk
          | some V₂ =>
              rw [hV₁, hV₂] at hchk
              simp only [Option.some.injEq] at hchk; subst hchk
              by_cases hb : evalE e σ ≠ 0
              · obtain ⟨s', hs', hli', hbd', hds'⟩ := ih₁ V V₁ (σ, h, n, L) hV₁ hinv
                have hexec : fexec (.ite e c₁ c₂) (σ, h, n, L) = some s' := by
                  show (if evalE e σ ≠ 0 then _ else _) = some s'; rw [ite_eq_left hb]; exact hs'
                refine ⟨s', hexec, ?_, ?_, ?_⟩
                · intro z hz; exact hli' z (inter_subset_left hz)
                · intro z hz; exact hbd' z (inter_subset_left hz)
                · intro z hz w hw; exact hds' z (inter_subset_left hz) w (inter_subset_left hw)
              · obtain ⟨s', hs', hli', hbd', hds'⟩ := ih₂ V V₂ (σ, h, n, L) hV₂ hinv
                have hexec : fexec (.ite e c₁ c₂) (σ, h, n, L) = some s' := by
                  show (if evalE e σ ≠ 0 then _ else _) = some s'; rw [ite_eq_right hb]; exact hs'
                refine ⟨s', hexec, ?_, ?_, ?_⟩
                · intro z hz; exact hli' z (inter_subset_right hz)
                · intro z hz; exact hbd' z (inter_subset_right hz)
                · intro z hz w hw; exact hds' z (inter_subset_right hz) w (inter_subset_right hw)
  | alloc x =>
      intro V V' s hchk hinv
      simp only [fcheck, Option.some.injEq] at hchk; subst hchk
      obtain ⟨σ, h, n, L⟩ := s
      obtain ⟨hli, hbd, hds⟩ := hinv
      refine ⟨(upd σ x (n : Int), updH h (n : Int) 0, n + 1, updB L (n : Int) true),
              rfl, ?_, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hzV
        · simp [upd, updB]
        · by_cases hzx : z = x
          · subst hzx; simp [upd, updB]
          · have hb := (hbd z hzV).2
            have hzn : σ z ≠ (n : Int) := by omega
            have h1 : upd σ x (n : Int) z = σ z := by simp [upd, hzx]
            rw [h1]; simp only [updB, ite_eq_right hzn]; exact hli z hzV
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hzV
        · have hu : upd σ z (n : Int) z = (n : Int) := by simp [upd]
          rw [hu]; omega
        · by_cases hzx : z = x
          · subst hzx
            have hu : upd σ z (n : Int) z = (n : Int) := by simp [upd]
            rw [hu]; omega
          · have hbz := hbd z hzV
            have hu : upd σ x (n : Int) z = σ z := by simp [upd, hzx]
            omega
      · intro z hz w hw hzw
        -- distinctness: the fresh var is the only one mapping to `n`; olds are `< n`.
        have hσx : ∀ p : String, upd σ x (n : Int) p = if p = x then (n : Int) else σ p :=
          fun _ => rfl
        have key : ∀ p, p ∈ x :: V → p = x ∨ (p ∈ V ∧ p ≠ x ∧ σ p < (n : Int)) := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hpV
          · exact Or.inl rfl
          · by_cases hpx : p = x
            · exact Or.inl hpx
            · exact Or.inr ⟨hpV, hpx, (hbd p hpV).2⟩
        rcases key z hz with hzx | ⟨hzV, hzx, hzlt⟩
        · rcases key w hw with hwx | ⟨hwV, hwx, hwlt⟩
          · exact absurd (hzx.trans hwx.symm) hzw
          · rw [hσx z, hσx w, ite_eq_left hzx, ite_eq_right hwx]; omega
        · rcases key w hw with hwx | ⟨hwV, hwx, hwlt⟩
          · rw [hσx z, hσx w, ite_eq_right hzx, ite_eq_left hwx]; omega
          · rw [hσx z, hσx w, ite_eq_right hzx, ite_eq_right hwx]; exact hds z hzV w hwV hzw
  | free x =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n, L⟩ := s
      simp only [fcheck] at hchk
      by_cases hxV : x ∈ V
      · rw [ite_eq_left hxV] at hchk
        simp only [Option.some.injEq] at hchk; subst hchk
        obtain ⟨hli, hbd, hds⟩ := hinv
        have hlx : L (σ x) = true := hli x hxV
        refine ⟨(σ, h, n, updB L (σ x) false), ?_, ?_, ?_, ?_⟩
        · show (if L (σ x) then _ else _) = _; rw [ite_eq_left hlx]
        · intro z hz
          have hzx : z ≠ x := ne_of_mem_remove hz
          have hzV := mem_of_mem_remove hz
          have hne : σ z ≠ σ x := hds z hzV x hxV hzx
          simp only [updB, ite_eq_right hne]; exact hli z hzV
        · intro z hz; exact hbd z (mem_of_mem_remove hz)
        · intro z hz w hw hzw
          exact hds z (mem_of_mem_remove hz) w (mem_of_mem_remove hw) hzw
      · rw [ite_eq_right hxV] at hchk; simp at hchk
  | load y x =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n, L⟩ := s
      simp only [fcheck] at hchk
      by_cases hxV : x ∈ V
      · rw [ite_eq_left hxV] at hchk
        simp only [Option.some.injEq] at hchk; subst hchk
        obtain ⟨hli, hbd, hds⟩ := hinv
        have hlx : L (σ x) = true := hli x hxV
        refine ⟨(upd σ y (h (σ x)), h, n, L), ?_, ?_, ?_, ?_⟩
        · show (if L (σ x) then _ else _) = _; rw [ite_eq_left hlx]
        · intro z hz
          have hzy : z ≠ y := ne_of_mem_remove hz
          have := hli z (mem_of_mem_remove hz); simpa [upd, hzy] using this
        · intro z hz
          have hzy : z ≠ y := ne_of_mem_remove hz
          have := hbd z (mem_of_mem_remove hz); simpa [upd, hzy] using this
        · intro z hz w hw hzw
          have hzy : z ≠ y := ne_of_mem_remove hz
          have hwy : w ≠ y := ne_of_mem_remove hw
          have := hds z (mem_of_mem_remove hz) w (mem_of_mem_remove hw) hzw
          simpa [upd, hzy, hwy] using this
      · rw [ite_eq_right hxV] at hchk; simp at hchk
  | store x e =>
      intro V V' s hchk hinv
      obtain ⟨σ, h, n, L⟩ := s
      simp only [fcheck] at hchk
      by_cases hxV : x ∈ V
      · rw [ite_eq_left hxV] at hchk
        simp only [Option.some.injEq] at hchk; subst hchk
        obtain ⟨hli, hbd, hds⟩ := hinv
        have hlx : L (σ x) = true := hli x hxV
        refine ⟨(σ, updH h (σ x) (evalE e σ), n, L), ?_, hli, hbd, hds⟩
        show (if L (σ x) then _ else _) = _; rw [ite_eq_left hlx]
      · rw [ite_eq_right hxV] at hchk; simp at hchk

/-- **Certified use-after-free-safe by `decide`.** From the empty tracked set a
    checked program runs to a real state — never a memory error. -/
theorem fsafe_of_check {c : FCmd} {V' : List String}
    (h : fcheck [] c = some V') (s : FState) :
    ∃ s', fexec c s = some s' := by
  have hinv : FInv [] s := by
    obtain ⟨σ, hh, n, L⟩ := s
    refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;> cases hx
  obtain ⟨s', hs', _⟩ := fcheck_safe c [] V' s h hinv
  exact ⟨s', hs'⟩

/-! ## Non-vacuity and teeth -/

/-- A safe program: allocate, use, then free. -/
def FPsafe : FCmd :=
  .seq (.alloc "p") (.seq (.store "p" (.num 5)) (.free "p"))

theorem fpsafe_checks : (fcheck [] FPsafe).isSome = true := by decide

theorem fpsafe_memsafe (s : FState) : ∃ s', fexec FPsafe s = some s' := by
  obtain ⟨V', hV'⟩ := Option.isSome_iff_exists.mp fpsafe_checks
  exact fsafe_of_check hV' s

/-- The use-after-free program: allocate, free, then dereference the freed
    pointer. -/
def FPuaf : FCmd :=
  .seq (.alloc "p") (.seq (.free "p") (.store "p" (.num 5)))

/-- **Use-after-free errors.** After `alloc p; free p`, the cell `p` points to
    is dead, so the store dereferences a freed address — a memory error. -/
theorem uaf_errors (s : FState) : fexec FPuaf s = none := by
  obtain ⟨σ, h, n, L⟩ := s
  simp [fexec, FPuaf, updB, upd]

/-- **The checker rejects it** — `free p` drops `p` from the tracked set, so the
    following store through `p` is unchecked. Checker and semantics agree the
    use-after-free is unsafe. -/
theorem uaf_rejected : fcheck [] FPuaf = none := by decide

/-- Double-free program. -/
def FPdouble : FCmd :=
  .seq (.alloc "p") (.seq (.free "p") (.free "p"))

/-- **Double-free errors** — the second `free` targets an already-dead cell. -/
theorem double_free_errors (s : FState) : fexec FPdouble s = none := by
  obtain ⟨σ, h, n, L⟩ := s
  simp [fexec, FPdouble, updB, upd]

/-- And the checker rejects the double-free too. -/
theorem double_free_rejected : fcheck [] FPdouble = none := by decide

end ConfTyping
