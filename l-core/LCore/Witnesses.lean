/-
  Witnesses for the kernel (PH1 steps 1–4). Every certificate shape is shown inhabited *and*
  refuted, on a toy language, so none of the definitions is vacuous. A transfer is exercised
  through a pass that really changes the leakage and the cost (CLAUDE.md: every rule has an
  accepted and a refused witness). Not Ring 0: this file only uses the kernel.
-/
import LCore.Kernel.Pass

namespace LCore.Witness

/-- A toy language. An input is (public, secret). Program `true` branches and spends on the
    secret; program `false` only looks at the public part. -/
def toy : Lang where
  Prog  := Bool
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run _ p i :=
    { ev   := [.read "r"]
      lk   := [.branch (if p then i.2 != 0 else i.1 != 0)]
      cost := if p then i.2 else 3
      out  := .done }

/-! ## `rel` -/

theorem toy_rel_holds : Cert.rel toy false := by
  intro n i i' h
  show (⟨_, _, _, _⟩ : Beh) = ⟨_, _, _, _⟩
  simp only [toy] at h ⊢
  simp [h]

theorem toy_rel_fails : ¬ Cert.rel toy true := by
  intro h
  have := h 0 (0, 0) (0, 1) rfl
  simp [toy] at this

/-! ## `bound` -/

theorem toy_bound_holds : Cert.bound toy 3 false := by
  intro n i; simp [toy]

theorem toy_bound_fails : ¬ Cert.bound toy 3 true := by
  intro h
  have := h 0 (0, 4)
  simp [toy] at this

/-! ## `trace` -/

theorem toy_trace_holds : Cert.trace toy (fun evs => ∀ e ∈ evs, e = .read "r") true := by
  intro n i e he; simpa [toy] using he

theorem toy_trace_fails : ¬ Cert.trace toy (fun evs => evs = []) true := by
  intro h
  have := h 0 (0, 0)
  simp [toy] at this

/-! ## A pass that changes leakage and cost -/

/-- The target: the same programs, run with one extra (public) bounds-check branch and one
    extra unit of cost, the shape of a pass that inserts a check. -/
def toyPad : Lang where
  Prog  := Bool
  In    := Nat × Nat
  lowIn i i' := i.1 = i'.1
  run n p i :=
    { ev   := (toy.run n p i).ev
      lk   := .branch true :: (toy.run n p i).lk
      cost := (toy.run n p i).cost + 1
      out  := (toy.run n p i).out }

def padPass : PassCert toy toyPad where
  comp p := .ok p
  enc i := i
  lkT _ l := .branch true :: l
  costT _ c := c + 1
  fuelT _ m := m
  costMono _ a b h := Nat.add_le_add_right h 1
  sim p p' h m i := by cases h; rfl

/-- **The transfers, exercised.** `false`'s three certificates arrive on the padded program
    with no proof about the pad itself; the budget arrives transformed (3 + 1). -/
theorem padPass_carries :
    (∀ m i i', toy.lowIn i i' → toyPad.run m false (padPass.enc i) = toyPad.run m false (padPass.enc i'))
  ∧ (∀ m i, (toyPad.run m false (padPass.enc i)).cost ≤ 4)
  ∧ (∀ m i, ∀ e ∈ (toyPad.run m true (padPass.enc i)).ev, e = .read "r") :=
  ⟨padPass.rel_transfer rfl toy_rel_holds,
   padPass.bound_transfer rfl toy_bound_holds,
   padPass.trace_transfer rfl toy_trace_holds⟩

/-- And the transfer is not vacuous: `true`, which is not `rel`, stays distinguishable after
    the pass. -/
theorem padPass_keeps_the_leak :
    toyPad.run 0 true (padPass.enc (0, 0)) ≠ toyPad.run 0 true (padPass.enc (0, 1)) := by
  simp [toyPad, toy, padPass]

/-- The identity pass on the padded language: composing with it must change nothing. -/
def idPad : PassCert toyPad toyPad where
  comp p := .ok p
  enc i := i
  lkT _ l := l
  costT _ c := c
  fuelT _ m := m
  costMono _ _ _ h := h
  sim p p' h m i := by cases h; rfl

/-- **Composition, exercised.** The two-pass pipeline is itself a `PassCert`, and the budget
    arrives through both cost transformers. -/
theorem seq_carries_bound :
    ∀ m i, (toyPad.run m false ((padPass.seq idPad).enc i)).cost ≤ 4 :=
  (padPass.seq idPad).bound_transfer rfl toy_bound_holds

end LCore.Witness
