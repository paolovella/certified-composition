/-
  Component seams on L (F5, row 12): certified components compose, with a computed certificate.

  **A seam needs an interface.** `Cert.rel` does not compose on L, because `Beh` has no final store:
  `y := s` and `if y` each satisfy it, and their sequence leaks `s` (`bare_rel_breaks`). This is
  `broken_seam` on L, and it is why a component's certificate cannot be its `Cert` alone.

  **The interface** is what `bcheck` threads: the authorized rights and the tracked pointers. A component
  is a program checked from an entry interface to an exit interface. `bcheck_seam` says the sequence of
  two matching components is checked at the sum of their costs. So the composite has `bcheck`'s four
  guarantees with no reasoning about the composite (`seam_certified`), and `splitPass` carries them
  (`seam_carried`).

  **Limits.** Sequence only. `Bridge.comp`'s graded reception and the trusted-base ledger stay on toy
  `Cmd`. Components share one partition. A pair matching the counted-loop pattern `asFor` is excluded,
  because `bcheck` treats it as one loop. This is `ucmdLangS` only (item L-UNIFY).
-/
import ConfTyping.Split

namespace ConfTyping.Seam

open Split (split split_carries Lc)

/-! ## The seam -/

/-- **Two matching components compose, at the sum of their costs.** The second component's entry
    interface is the first's exit interface. -/
theorem bcheck_seam {P : Partition} {a b : UCmd} {A V A₁ V₁ A₂ V₂ : List String} {k₁ k₂ : Nat}
    (hf : asFor (.seq a b) = none)
    (h₁ : bcheck P A V a = some (A₁, V₁, k₁)) (h₂ : bcheck P A₁ V₁ b = some (A₂, V₂, k₂)) :
    bcheck P A V (.seq a b) = some (A₂, V₂, k₁ + k₂) := by
  show bcheckF P (usize a + usize b + 1) A V (.seq a b) = _
  simp only [bcheckF, hf]
  rw [bcheckF_enough a A V _ (by omega), h₁, Option.bind_some,
    bcheckF_enough b A₁ V₁ _ (by omega), h₂]
  rfl

/-- **The composite has all four guarantees**, with its budget computed from the components'. -/
theorem seam_certified {P : Partition} {a b : UCmd} {A₁ V₁ A₂ V₂ : List String} {k₁ k₂ : Nat}
    (hf : asFor (.seq a b) = none)
    (h₁ : bcheck P [] [] a = some (A₁, V₁, k₁)) (h₂ : bcheck P A₁ V₁ b = some (A₂, V₂, k₂))
    (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS P π) (k₁ + k₂) (.seq a b)
  ∧ LCore.Cert.trace (ucmdLangS P π) (mediated π) (.seq a b)
  ∧ LCore.Cert.trace (ucmdLangS P π) (fun evs => faultEv ∉ evs) (.seq a b)
  ∧ LCore.Cert.rel (ucmdLangS P π) (.seq a b) :=
  bcheck_lcoreS (bcheck_seam hf h₁ h₂) π

/-- **And `splitPass` carries them to the compiled composite.** -/
theorem seam_carried {P : Partition} {a b : UCmd} {A₁ V₁ A₂ V₂ : List String} {k₁ k₂ : Nat}
    (hf : asFor (.seq a b) = none)
    (h₁ : bcheck P [] [] a = some (A₁, V₁, k₁)) (h₂ : bcheck P A₁ V₁ b = some (A₂, V₂, k₂))
    (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS P π) (Lc (.seq a b) * (k₁ + k₂)) (split (.seq a b))
  ∧ LCore.Cert.trace (ucmdLangS P π) (mediated π) (split (.seq a b))
  ∧ LCore.Cert.trace (ucmdLangS P π) (fun evs => faultEv ∉ evs) (split (.seq a b))
  ∧ LCore.Cert.rel (ucmdLangS P π) (split (.seq a b)) :=
  split_carries (bcheck_seam hf h₁ h₂) π

/-! ## Witnesses: without the interface a seam breaks -/

/-- The secret. -/
def secS : Partition := fun x => x == "s"

/-- A secret written to a public variable. No final store is observed, so this alone shows nothing. -/
def writeY : UCmd := .assign "y" (.var "s")

/-- A branch on that public variable. -/
def branchY : UCmd := .ite (.var "y") .skip (.seq .skip .skip)

theorem writeY_rel (π : MedPolicy) : LCore.Cert.rel (ucmdLangS secS π) writeY := by
  intro n σ σ' _ _ _
  cases n with
  | zero => rfl
  | succ m =>
    cases m <;> simp [ucmdLangS, writeY, push, urunS, stepT, uexec, uaddrs, stepEv, TRun.atomS, initU]

theorem branchY_checks : (bcheck secS [] [] branchY).isSome = true := by decide

theorem branchY_rel (π : MedPolicy) : LCore.Cert.rel (ucmdLangS secS π) branchY := by
  cases h : bcheck secS [] [] branchY with
  | none => have := branchY_checks; rw [h] at this; cases this
  | some r => exact bcheck_relS (A' := r.1) (V' := r.2.1) (k := r.2.2) h π

/-- A store holding `v` in the secret. -/
def storeS (v : Int) : Store := fun x => if x == "s" then v else 0

theorem storeS_low (v v' : Int) : lowEq secS (storeS v) (storeS v') := by
  intro x hx
  have h : (x == "s") = false := hx
  simp [storeS, h]

/-- **Each satisfies `Cert.rel`, and the sequence leaks the secret.** -/
theorem bare_rel_breaks :
    LCore.Cert.rel (ucmdLangS secS (fun _ => true)) writeY
  ∧ LCore.Cert.rel (ucmdLangS secS (fun _ => true)) branchY
  ∧ ¬ LCore.Cert.rel (ucmdLangS secS (fun _ => true)) (.seq writeY branchY) := by
  refine ⟨writeY_rel _, branchY_rel _, ?_⟩
  intro h
  have := h 20 _ _ trivial trivial (storeS_low 0 1)
  revert this; decide

/-- **The interface refuses it**, at the first component. -/
theorem writeY_refused : bcheck secS [] [] writeY = none := by decide

/-! ## Witnesses: two components, accepted and refused -/

/-- No secrets. -/
def noSec : Partition := fun _ => false

/-- Checks a right and allocates a pointer: it supplies both. -/
def supplier : UCmd := .seq (.check "r") (.memop .alloc "p")

/-- Uses the right and the pointer: it needs both. -/
def consumer : UCmd := .seq (.access "r") (.memop .deref "p")

theorem supplier_checks : bcheck noSec [] [] supplier = some (["r"], ["p"], 2) := by decide
theorem consumer_checks : bcheck noSec ["r"] ["p"] consumer = some (["r"], ["p"], 2) := by decide

/-- **Accepted**: the budget is computed from the components, and the checker agrees with it. -/
theorem supplier_consumer_certified (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangS noSec π) (2 + 2) (.seq supplier consumer)
  ∧ LCore.Cert.trace (ucmdLangS noSec π) (mediated π) (.seq supplier consumer)
  ∧ LCore.Cert.trace (ucmdLangS noSec π) (fun evs => faultEv ∉ evs) (.seq supplier consumer)
  ∧ LCore.Cert.rel (ucmdLangS noSec π) (.seq supplier consumer) :=
  seam_certified rfl supplier_checks consumer_checks π

theorem supplier_consumer_agrees :
    bcheck noSec [] [] (.seq supplier consumer) = some (["r"], ["p"], 4) := by decide

/-- A read that needs a right from whatever ran before it. -/
def reader : UCmd := .access "r"

/-- **The second component is fine on its own entry interface.** -/
theorem reader_checks : bcheck noSec ["r"] [] reader = some (["r"], [], 1) := by decide

/-- **But `skip` does not supply that interface, so the seam is refused.** -/
theorem unsupplied_refused : bcheck noSec [] [] (.seq .skip reader) = none := by decide

/-- **And the failure is real**: the read happens with the right refused. -/
theorem unsupplied_unmediated :
    ¬ LCore.Cert.trace (ucmdLangS noSec (fun _ => false)) (mediated (fun _ => false))
      (.seq .skip reader) := by
  intro h
  have hm : mediated (fun _ => false)
      ((ucmdLangS noSec (fun _ => false)).run 20 (.seq .skip reader) (fun _ => 0)).ev :=
    h 20 _ trivial
  have := hm "r" (by decide)
  cases this

end ConfTyping.Seam
