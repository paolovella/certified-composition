/-
  Declassification on L (F5, row 4): release of whole input variables, a `Cert.rel` on `ucmdLangS`.

  **Attacker:** sees every channel and all leakage, cost and outcome, and knows the public inputs and
  the released ones. The certificate says that is all a run can tell it about the inputs.

  **How.** `released P R` is the secrets `P` minus the released variables `R`. `bcheck` at that
  partition is the whole checker, so a release is declared by naming it and no rule is new. Its
  input relation is exactly agreement on public and released inputs (`released_lowEq`), and releasing
  nothing is row 1 (`released_none`).

  **Limits.** A release is a whole variable's initial value, never a computed one: a program that
  reveals only whether `r` is zero must still release all of `r` (`revealR_coarser`). Computed release
  is item REL-01, and `Ev.release` stays unproduced until then. The certificate says "at most `R`",
  not that `R` was the right thing to release. Strings start empty here, so it speaks about integer
  secrets; string secrets are row 7b's.
-/
import ConfTyping.Split

namespace ConfTyping.Release

open Split (split split_carries)

/-- The secrets `P` minus the released variables `R`. -/
def released (P R : Partition) : Partition := fun x => P x && !R x

/-- **The input relation says what it should**: agreement on public inputs and on released ones. -/
theorem released_lowEq {P R : Partition} {σ σ' : Store} :
    lowEq (released P R) σ σ' ↔ lowEq P σ σ' ∧ ∀ x, R x = true → σ x = σ' x := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (by simp [released, hx]), fun x hx => h x (by simp [released, hx])⟩
  · intro ⟨hl, hr⟩ x hx
    cases hP : P x with
    | false => exact hl x hP
    | true =>
      have hR : R x = true := by simpa [released, hP] using hx
      exact hr x hR

/-- **Releasing nothing is row 1.** -/
theorem released_none (P : Partition) : released P (fun _ => false) = P := by
  funext x
  simp [released]

/-- **Row 4 on L.** If `bcheck` accepts a program with `R` released, every run shows the same on
    inputs that agree on public and released variables. -/
theorem bcheck_release {P R : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck (released P R) [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.rel (ucmdLangS (released P R) π) c :=
  bcheck_relS h π

/-- **The release is carried through `splitPass`**: the bound on what is revealed holds on the
    compiled program too. -/
theorem bcheck_release_carried {P R : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck (released P R) [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.rel (ucmdLangS (released P R) π) (split c) :=
  (split_carries h π).2.2.2

/-! ## Witnesses -/

/-- Two secrets. -/
def secrets : Partition := fun x => x == "r" || x == "s"
/-- `r` is released, `s` is not. -/
def relR : Partition := fun x => x == "r"
/-- Nothing is released. -/
def relNone : Partition := fun _ => false

/-- A store with the given secrets. -/
def store (r s : Int) : Store := fun x => if x == "r" then r else if x == "s" then s else 0

theorem store_agree_r (r s s' : Int) : lowEq (released secrets relR) (store r s) (store r s') := by
  intro x hx
  by_cases hr : x = "r"
  · subst hr; rfl
  by_cases hs : x = "s"
  · subst hs; exact absurd hx (by decide)
  have h1 : (x == "r") = false := by simpa using hr
  have h2 : (x == "s") = false := by simpa using hs
  simp [store, h1, h2]

theorem store_agree_public (r r' s s' : Int) : lowEq secrets (store r s) (store r' s') := by
  intro x hx
  have h : (x == "r") = false ∧ (x == "s") = false := by
    simpa [secrets, Bool.or_eq_false_iff] using hx
  simp [store, h.1, h.2]

/-- A branch on the released variable. -/
def revealR : UCmd := .ite (.var "r") .skip (.seq .skip .skip)

/-- **Accepted**, with `r` released. -/
theorem revealR_checks : (bcheck (released secrets relR) [] [] revealR).isSome = true := by decide

theorem revealR_certified (π : MedPolicy) :
    LCore.Cert.rel (ucmdLangS (released secrets relR) π) revealR := by
  cases h : bcheck (released secrets relR) [] [] revealR with
  | none => have := revealR_checks; rw [h] at this; cases this
  | some r => exact bcheck_release (A' := r.1) (V' := r.2.1) (k := r.2.2) h π

/-- **Declaration is what lets it through.** With nothing released it is refused. -/
theorem revealR_refused : bcheck (released secrets relNone) [] [] revealR = none := by decide

/-- **And it does reveal `r`**, so the refusal is not vacuous. -/
theorem revealR_leaks :
    ¬ LCore.Cert.rel (ucmdLangS (released secrets relNone) (fun _ => true)) revealR := by
  intro h
  have hrel : lowEq (released secrets relNone) (store 0 0) (store 1 0) := by
    rw [show released secrets relNone = secrets from released_none secrets]
    exact store_agree_public 0 1 0 0
  have := h 20 _ _ trivial trivial hrel
  revert this; decide

/-- **The limit.** `revealR` shows only whether `r` is zero, so `r = 1` and `r = 2` look the same,
    yet the only certificate available releases all of `r`. Only REL-01 can state the bit. -/
theorem revealR_coarser :
    (ucmdLangS (released secrets relR) (fun _ => true)).run 20 revealR (store 1 0)
      = (ucmdLangS (released secrets relR) (fun _ => true)).run 20 revealR (store 2 0) := by
  decide

/-- A branch on the secret that was not released. -/
def overreach : UCmd := .ite (.var "s") .skip (.seq .skip .skip)

/-- **Refused**: releasing `r` says nothing about `s`. -/
theorem overreach_refused : bcheck (released secrets relR) [] [] overreach = none := by decide

theorem overreach_leaks :
    ¬ LCore.Cert.rel (ucmdLangS (released secrets relR) (fun _ => true)) overreach := by
  intro h
  have := h 20 _ _ trivial trivial (store_agree_r 0 0 1)
  revert this; decide

/-- **The classic attack**: overwrite the released variable with a secret, then use it. -/
def launder : UCmd := .seq (.assign "r" (.var "s")) revealR

/-- **Refused**: a released variable is public from the start, so a secret cannot be written to it. -/
theorem launder_refused : bcheck (released secrets relR) [] [] launder = none := by decide

theorem launder_leaks :
    ¬ LCore.Cert.rel (ucmdLangS (released secrets relR) (fun _ => true)) launder := by
  intro h
  have := h 20 _ _ trivial trivial (store_agree_r 0 0 1)
  revert this; decide

end ConfTyping.Release
