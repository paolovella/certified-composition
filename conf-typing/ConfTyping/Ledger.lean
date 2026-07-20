/-
  The assumption ledger — brick 4, session 1: conditional certificates that
  accumulate their trusted base under composition, and never silently discharge
  it.

  Bricks 2 and 3 both deferred this: a real component depends on things it does
  not verify — an upstream's data classification, an external library's
  correctness, a crypto primitive's security. Such a dependency is an
  *assumption*, not evidence. This module makes assumptions first-class:

  * a **ledger** `Γ : List Prop` records a component's trusted base;
  * a **conditional certificate** `CondBoundary c P Γ := Sat Γ → BoundaryNI c P`
    is a guarantee *relative to* that base;
  * composition **appends** ledgers (`condBoundary_seq`, `condReleases_seq`):
    the composite's trusted base is the union of the parts';
  * **discharge** is explicit (`condBoundary_discharge`): to turn a conditional
    certificate into an unconditional one you must *prove* the ledger — the
    empty ledger is exactly the unconditional certificate (`condBoundary_nil`);
  * **no silent discharge** (`ledger_no_silent_discharge`): a component whose
    security genuinely rests on an assumption cannot be certified with that
    assumption dropped — the ledger entry is load-bearing, witnessed. This is
    the composition-level analogue of `attest_is_not_J_evidence` (§6.1): an
    attestation coexists with an obligation but never becomes its proof.
-/
import ConfTyping.SecTy
import ConfTyping.FlowBridge

namespace ConfTyping

/-! ## The ledger and its satisfaction -/

/-- A ledger is a list of assumptions (external propositions a component
    relies on). -/
abbrev Ledger := List Prop

/-- The ledger holds when every assumption in it holds. -/
def Sat : Ledger → Prop
  | []      => True
  | p :: ps => p ∧ Sat ps

theorem sat_append (Γ₁ Γ₂ : Ledger) : Sat (Γ₁ ++ Γ₂) ↔ Sat Γ₁ ∧ Sat Γ₂ := by
  induction Γ₁ with
  | nil => simp only [List.nil_append, Sat, true_and]
  | cons p ps ih => simp only [List.cons_append, Sat, ih]; exact and_assoc.symm

/-! ## Conditional certificates -/

/-- A boundary certificate *relative to* a trusted base `Γ`. -/
def CondBoundary (c : Cmd) (P : Partition) (Γ : Ledger) : Prop :=
  Sat Γ → BoundaryNI c P

/-- A release certificate relative to a trusted base. -/
def CondReleases (c : Cmd) (P : Partition) (Γ : Ledger) (φ : Release) : Prop :=
  Sat Γ → BoundaryReleases c P φ

/-! ## Accumulation: the trusted base is the union -/

/-- **The ledger composes by union.** The composite's boundary certificate
    holds relative to the *append* of the two components' trusted bases —
    each part's assumptions are carried, none silently dropped. -/
theorem condBoundary_seq {c₁ c₂ : Cmd} {P : Partition} {Γ₁ Γ₂ : Ledger}
    (h₁ : CondBoundary c₁ P Γ₁) (h₂ : CondBoundary c₂ P Γ₂) :
    CondBoundary (.seq c₁ c₂) P (Γ₁ ++ Γ₂) := by
  intro hsat
  rw [sat_append] at hsat
  exact boundaryNI_seq (h₁ hsat.1) (h₂ hsat.2)

/-- Releases accumulate the same way, with the brick-2 computed release. -/
theorem condReleases_seq {c₁ c₂ : Cmd} {P : Partition} {Γ₁ Γ₂ : Ledger}
    {φ₁ φ₂ : Release}
    (h₁ : CondReleases c₁ P Γ₁ φ₁) (h₂ : CondReleases c₂ P Γ₂ φ₂) :
    CondReleases (.seq c₁ c₂) P (Γ₁ ++ Γ₂) (seqRelease c₁ φ₁ φ₂) := by
  intro hsat
  rw [sat_append] at hsat
  exact boundaryReleases_seq (h₁ hsat.1) (h₂ hsat.2)

/-! ## Discharge is explicit -/

/-- The empty ledger is exactly the unconditional certificate. -/
theorem condBoundary_nil {c : Cmd} {P : Partition} :
    CondBoundary c P [] ↔ BoundaryNI c P := by
  constructor
  · intro h; exact h trivial
  · intro h _; exact h

/-- **Discharge.** To collapse a conditional certificate to an unconditional
    one you must *prove* the whole ledger — nothing is free. -/
theorem condBoundary_discharge {c : Cmd} {P : Partition} {Γ : Ledger}
    (h : CondBoundary c P Γ) (hsat : Sat Γ) : BoundaryNI c P :=
  h hsat

/-- Discharge one assumption at the head, given its proof. -/
theorem condBoundary_discharge_head {c : Cmd} {P : Partition} {A : Prop}
    {Γ : Ledger} (h : CondBoundary c P (A :: Γ)) (ha : A) : CondBoundary c P Γ :=
  fun hsat => h ⟨ha, hsat⟩

/-- An unconditional certificate holds under any ledger (adding unused
    assumptions is always sound — the trusted base is an over-approximation). -/
theorem condBoundary_of_unconditional {c : Cmd} {P : Partition} {Γ : Ledger}
    (h : BoundaryNI c P) : CondBoundary c P Γ :=
  fun _ => h

/-- Weakening: any additional assumption may be added to a ledger. -/
theorem condBoundary_weaken {c : Cmd} {P : Partition} {A : Prop} {Γ : Ledger}
    (h : CondBoundary c P Γ) : CondBoundary c P (A :: Γ) :=
  fun hsat => h hsat.2

/-! ## No silent discharge — the ledger has teeth

    The mechanism is only honest if an assumption a component *actually uses*
    cannot be dropped. Witness: a component that copies an input channel `x`
    into a Low output is secure *only if `x` is itself classified Low* — a
    trust assumption about the upstream's labeling. The conditional
    certificate relative to that assumption holds for **every** classification
    (`cx_cond`), but the unconditional certificate is **false** at a
    classification where `x` is High (`cx_not_unconditional`): the ledger
    entry `P "x" = false` is load-bearing, and dropping it is unsound. -/

/-- Copy input channel `x` into the Low output `l`. -/
def Cx : Cmd := .assign "l" (.var "x")

/-- A classification where `x` is High (secret) and `l` is Low (public). -/
def Phx : Partition := fun y => y == "x"

/-- **The conditional certificate, for every classification.** Assuming the
    upstream labels `x` as Low, the copy is boundary-secure — proved through
    the checker's own `assignL` rule, so this is checker-grade evidence
    relative to the assumption. -/
theorem cx_cond (P : Partition) : CondBoundary Cx P [P "x" = false] := by
  intro hsat
  have hx : P "x" = false := hsat.1
  have he : exprLow P (.var "x") = true := by simp [exprLow, hx]
  exact secTy_boundaryNI (SecTy.assignL "l" (.var "x") he)

def ξ0 : Store := upd (fun _ => 0) "x" 1
def ξ1 : Store := fun _ => 0

theorem cx_ξ0 : evalStore Cx ξ0 "l" = 1 := by
  simp [Cx, evalStore, eval, evalE, ξ0, upd]

theorem cx_ξ1 : evalStore Cx ξ1 "l" = 0 := by
  simp [Cx, evalStore, eval, evalE, ξ1, upd]

/-- **The unconditional certificate is false** where `x` is actually High:
    two runs agreeing on all public data but differing on the secret `x`
    produce different public outputs. The assumption cannot be dropped. -/
theorem cx_not_unconditional : ¬ BoundaryNI Cx Phx := by
  intro h
  have hle : lowEq Phx ξ0 ξ1 := by
    intro y hy
    have hyx : y ≠ "x" := by intro hx; subst hx; simp [Phx] at hy
    simp [ξ0, ξ1, upd, hyx]
  have key := h ξ0 ξ1 hle "l" (by decide)
  rw [cx_ξ0, cx_ξ1] at key
  exact absurd key (by decide)

/-- **No silent discharge.** The conditional certificate holds under the
    trust assumption for every classification, yet the unconditional
    certificate fails at a classification where the assumption is false. So a
    ledger entry a component relies on is load-bearing: certifying the
    component with it dropped is unsound. The composition-level
    `attest_is_not_J_evidence`. -/
theorem ledger_no_silent_discharge :
    (∀ P, CondBoundary Cx P [P "x" = false]) ∧ ¬ BoundaryNI Cx Phx :=
  ⟨cx_cond, cx_not_unconditional⟩

end ConfTyping
