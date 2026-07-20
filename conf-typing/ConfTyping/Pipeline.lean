/-
  The product — brick 3, session 3: multi-tenant isolation and the pipeline
  theorem.

  This module closes the security program's second-brick fork (VULN-COVERAGE
  row 12: "component boundaries") with the two demos the map has owed:

  * **Multi-tenant isolation (row 7, upgraded to [proved]).** Cross-tenant
    isolation *is* noninterference — the T1 relabeling, made concrete. One
    multiplexing component, checked against each tenant's partition, is proved
    isolated each way (`multiplex_isolates_A/B`), and the isolation survives
    composition (`multiplex_pipeline_isolates_B`). A component that copies one
    tenant's data into another's channel is rejected by the checker
    (`leaky_rejected`) and proved non-isolated (`leaky_not_isolated`): the
    instance has teeth.

  * **The pipeline theorem (syntax in, certified composed Bridge out).** Two
    components — the first Closure-checked, the second Policy-checked — compose
    into a single certified boundary (`certified_pipeline`), which is a Bridge
    in the transport interface (`certified_pipeline_bridge`), whose generic
    `Bridge.comp` certificate is the seam certificate
    (`certified_pipeline_reconstruction`). Nothing about the composite is
    re-verified; the two `secCheck`/`secCheckD` calls plus the generic
    composition law do all of it.
-/
import ConfTyping.SecTyD

namespace ConfTyping

open TransportCalculus

/-! ## Boundary-NI weakens to any release -/

/-- A Closure-certified component satisfies the Policy certificate for any
    declared release (it reveals nothing, so any budget bounds it). -/
theorem BoundaryReleases.ofBoundaryNI {c : Cmd} {P : Partition}
    (h : BoundaryNI c P) (φ : Release) : BoundaryReleases c P φ :=
  fun σ σ' hle _ => h σ σ' hle

/-! ## Multi-tenant isolation — cross-tenant NI, checked

    Two tenants A and B share a multiplexing component. Each tenant's data
    and output channel are classified *together*: from B's isolation
    viewpoint, `{b, outB}` are secret (High) and everything else is public.
    A component that routes each tenant's data only to that tenant's own
    channel is isolated *both ways*, and the checker proves it. -/

/-- Tenant B's isolation partition: B's data and B's channel are High. -/
def PtenantB : Partition := fun x => x == "b" || x == "outB"

/-- Tenant A's isolation partition: A's data and A's channel are High. -/
def PtenantA : Partition := fun x => x == "a" || x == "outA"

/-- The multiplexer: route each tenant's data to its own output channel. -/
def Multiplex : Cmd :=
  .seq (.assign "outA" (.var "a")) (.assign "outB" (.var "b"))

theorem multiplex_checks_B : secCheck PtenantB false Multiplex = true := by decide
theorem multiplex_checks_A : secCheck PtenantA false Multiplex = true := by decide

/-- **Isolation of B (as noninterference).** A's view — the whole non-B
    store — is independent of B's data. `resultO PtenantB` is exactly the
    Low (non-B) channel, so this is `J_NI` at B's partition: cross-tenant
    isolation *is* noninterference, checked. -/
theorem multiplex_isolates_B : J_NI Multiplex (resultO PtenantB) PtenantB :=
  resultNI_of_check multiplex_checks_B

/-- **Isolation of A**, symmetrically. -/
theorem multiplex_isolates_A : J_NI Multiplex (resultO PtenantA) PtenantA :=
  resultNI_of_check multiplex_checks_A

/-- Isolation survives composition: two multiplexer stages in a pipeline are
    still isolated, with zero per-composite reasoning (the seam theorem). -/
theorem multiplex_pipeline_isolates_B :
    BoundaryNI (.seq Multiplex Multiplex) PtenantB :=
  boundaryNI_seq (boundaryNI_of_check multiplex_checks_B)
                 (boundaryNI_of_check multiplex_checks_B)

/-! ### Teeth: a cross-tenant leak is caught -/

/-- A component that routes B's data into A's channel — a cross-tenant leak. -/
def Leaky : Cmd := .assign "outA" (.var "b")

/-- **The checker rejects the leak.** -/
theorem leaky_rejected : secCheck PtenantB false Leaky = false := by decide

def τ0 : Store := upd (fun _ => 0) "b" 1
def τ1 : Store := fun _ => 0

theorem leaky_τ0 : evalStore Leaky τ0 "outA" = 1 := by
  simp [Leaky, evalStore, eval, evalE, τ0, upd]

theorem leaky_τ1 : evalStore Leaky τ1 "outA" = 0 := by
  simp [Leaky, evalStore, eval, evalE, τ1, upd]

/-- **And the rejection is semantically correct.** `Leaky` really does leak
    B's data into A's channel: two runs agreeing on everything public but
    differing on B's secret produce different A-outputs. Checker and
    semantics agree. -/
theorem leaky_not_isolated : ¬ BoundaryNI Leaky PtenantB := by
  intro h
  have hle : lowEq PtenantB τ0 τ1 := by
    intro x hx
    have hxb : x ≠ "b" := by
      intro hb; subst hb; simp [PtenantB] at hx
    simp [τ0, τ1, upd, hxb]
  have key := h τ0 τ1 hle "outA" (by decide)
  rw [leaky_τ0, leaky_τ1] at key
  exact absurd key (by decide)

/-! ## The pipeline theorem: syntax in, certified composed Bridge out -/

/-- **The pipeline theorem.** A Closure-checked component followed by a
    Policy-checked component composes into one certified boundary — the
    composite `BoundaryReleases` certificate is *computed* (the first
    component reveals nothing, so the composite release is the second's
    ledger, paired). No semantic reasoning about the composite: two checker
    calls and the brick-2 seam theorem. -/
theorem certified_pipeline {c₁ c₂ : Cmd} {P : Partition} {Δ : List Permit}
    (h₁ : secCheck P false c₁ = true)
    (h₂ : secCheckD P Δ false c₂ = true) :
    BoundaryReleases (.seq c₁ c₂) P
      (seqRelease c₁ (fun _ => .int 0) (relOf P c₂)) :=
  boundaryReleases_seq
    (BoundaryReleases.ofBoundaryNI (boundaryNI_of_check h₁) _)
    (boundaryReleases_of_check h₂)

/-- **The pipeline is a Bridge** in the same transport interface as Lipschitz
    maps, Markov kernels, and quantum channels — obtained from the two
    syntactic checks. -/
def certified_pipeline_bridge {c₁ c₂ : Cmd} {P : Partition} {Δ : List Permit}
    (h₁ : secCheck P false c₁ = true)
    (h₂ : secCheckD P Δ false c₂ = true) :
    Bridge Store (Mono QD qle) QD flowGA qd :=
  Bridge.ofRelease (certified_pipeline h₁ h₂)

/-- The pipeline Bridge's map is the composite's boundary map. -/
theorem certified_pipeline_map {c₁ c₂ : Cmd} {P : Partition} {Δ : List Permit}
    (h₁ : secCheck P false c₁ = true)
    (h₂ : secCheckD P Δ false c₂ = true) :
    (certified_pipeline_bridge h₁ h₂).map = evalStore (.seq c₁ c₂) := rfl

/-- **The whole product, one statement.** Feed two syntactic checks; the
    *generic* `Bridge.comp` (the interface's composition law, shared with
    every quantitative tier) produces a certificate dominated by the
    pipeline's seam certificate — security composition reconstructed by the
    same law that composes contraction estimates. -/
theorem certified_pipeline_reconstruction
    {c₁ c₂ : Cmd} {P : Partition} {Δ : List Permit}
    (h₁ : secCheck P false c₁ = true)
    (h₂ : secCheckD P Δ false c₂ = true) :
    ∀ σ σ', qle
      ((((Bridge.ofRelease (boundaryReleases_of_check h₂)).comp
          (Bridge.ofComponent c₁)).cert).toFun (qd σ σ'))
      ((leakBound P
          (seqRelease c₁ (fun _ => .int 0) (relOf P c₂))).toFun (qd σ σ')) :=
  comp_reconstructs_seq_release
    (BoundaryReleases.ofBoundaryNI (boundaryNI_of_check h₁) _)
    (boundaryReleases_of_check h₂)

/-! ## A concrete certified pipeline

    `P_ok` (Closure-checked, session 1) followed by `P_leak` (Policy-checked
    under one guard permit, session 2): the whole stack certified from two
    `decide`s. -/

theorem demo_pipeline :
    BoundaryReleases (.seq Pok Pleak) Phigh
      (seqRelease Pok (fun _ => .int 0) (relOf Phigh Pleak)) :=
  certified_pipeline (Δ := [Permit.guard (.var "b")]) pok_checks pleak_checksD

/-- The same pipeline as a Bridge in the transport interface — the security
    program's product, end to end: two checked components, one composed
    certified morphism, in the interface shared with the quantitative
    tiers. -/
def demo_pipeline_bridge : Bridge Store (Mono QD qle) QD flowGA qd :=
  certified_pipeline_bridge (Δ := [Permit.guard (.var "b")]) pok_checks pleak_checksD

end ConfTyping
