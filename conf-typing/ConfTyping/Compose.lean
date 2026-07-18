/-
  The seam module — brick 2, session 1: certified composition of components.

  A *component* is a program with a boundary certificate: a claim about the
  store (and instrumented outcome) it hands to whatever runs next, stated at
  the Low-boundary granularity. This module proves the seam theorems: the
  composite of two certified components is certified, with the composite
  certificate *computed* from the parts —

  * `boundaryNI_seq` / `outNI_seq` : boundary certificates compose;
  * `seq_all_channels`             : from the two component certificates,
                                     every derivable channel of the composite
                                     is certified (via A3, nothing new);
  * `releases_seq`                 : delimited release composes; the composite
                                     release is the *pair* ⟨φ₁, φ₂ ∘ boundary⟩
                                     — a non-scalar certificate algebra with
                                     the first component's map threaded through
                                     the second's release (the same semidirect
                                     shape as the Hölder certificate in
                                     `transport-kernel/`).

  The writer structure of `eval` does the work: `eval (seq c₁ c₂)` threads the
  store, adds the costs, concatenates the branch traces (`eval_seq`, `rfl`),
  so every observation of a composite factors through the component outcomes.

  Integrity reading: all seam theorems apply verbatim at the untrusted
  relabeling (`taint_result_seq`) — T1 made that free.
-/
import ConfTyping.Integrity

namespace ConfTyping

/-! ## The writer decomposition -/

/-- The component's boundary map: the store it hands to the next component. -/
def evalStore (c : Cmd) (σ : Store) : Store := (eval c σ).1

/-- Outcome gluing: the composite outcome is the second store, summed costs,
    concatenated traces. -/
def glue (r₁ r₂ : Outcome) : Outcome := (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2)

/-- **The writer decomposition** — definitional: a composite run is the two
    component runs glued. -/
theorem eval_seq (c₁ c₂ : Cmd) (σ : Store) :
    eval (.seq c₁ c₂) σ = glue (eval c₁ σ) (eval c₂ (evalStore c₁ σ)) := rfl

/-- Every observation of a composite factors through the component outcomes. -/
theorem obs_seq (o : Obs) (c₁ c₂ : Cmd) (σ : Store) :
    obs o (.seq c₁ c₂) σ = o (glue (eval c₁ σ) (eval c₂ (evalStore c₁ σ))) := rfl

/-! ## Boundary certificates -/

/-- **The boundary certificate (Closure form).** Low-equivalent inputs yield
    Low-equivalent boundary stores: the component certifies its entire Low
    boundary — the granularity at which components compose. -/
def BoundaryNI (c : Cmd) (P : Partition) : Prop :=
  ∀ σ σ', lowEq P σ σ' → lowEq P (evalStore c σ) (evalStore c σ')

/-- The boundary certificate is a channel claim: `BoundaryNI` is exactly
    `J_NI` at the boundary channel `resultO`. Components speak the same
    observation language as adversaries. -/
theorem boundaryNI_iff_resultNI (c : Cmd) (P : Partition) :
    BoundaryNI c P ↔ J_NI c (resultO P) P := by
  constructor
  · intro h σ σ' hle
    simp only [obs, resultO]
    congr 1
    funext x
    cases hPx : P x with
    | true  => simp
    | false => simp
               exact h σ σ' hle x hPx
  · intro h σ σ' hle x hPx
    have key := h σ σ' hle
    simp only [obs, resultO] at key
    injection key with hf
    have := congrFun hf x
    simpa [evalStore, hPx] using this

theorem boundaryNI_skip (P : Partition) : BoundaryNI .skip P :=
  fun _ _ h => h

/-- **Seam theorem, Closure form, boundary channel.** Boundary certificates
    compose — the certified boundary of `c₁` is exactly what `c₂`'s
    certificate consumes. -/
theorem boundaryNI_seq {c₁ c₂ : Cmd} {P : Partition}
    (h₁ : BoundaryNI c₁ P) (h₂ : BoundaryNI c₂ P) :
    BoundaryNI (.seq c₁ c₂) P :=
  fun σ σ' hle => h₂ _ _ (h₁ σ σ' hle)

/-- The composite's data sink is certified from `c₁`'s boundary certificate
    and `c₂`'s sink certificate. -/
theorem resultNI_seq {c₁ c₂ : Cmd} {P : Partition}
    (h₁ : BoundaryNI c₁ P) (h₂ : J_NI c₂ (resultO P) P) :
    J_NI (.seq c₁ c₂) (resultO P) P :=
  fun σ σ' hle => h₂ _ _ (h₁ σ σ' hle)

/-! ## The total boundary certificate: all three instrumented channels -/

/-- The total outcome channel: Low store, cost, and branch trace jointly —
    definitionally the joint `tup (resultO P) (tup wall branchO)` of the
    primitive observation language `𝒪`. -/
def outO (P : Partition) : Obs := tup (resultO P) (tup wall branchO)

/-- A total boundary certificate yields Low-equivalence of boundary stores. -/
theorem outNI_boundary {c : Cmd} {P : Partition} (h : J_NI c (outO P) P) :
    BoundaryNI c P := by
  intro σ σ' hle x hPx
  have key := h σ σ' hle
  simp only [obs, outO, tup, resultO] at key
  injection key with kst _
  injection kst with hf
  have := congrFun hf x
  simpa [evalStore, hPx] using this

/-- **Seam theorem, total form.** Total boundary certificates compose: the
    composite's Low store, cost, and branch trace are all certified from the
    two component certificates. Costs add and traces concatenate, so the
    composite channel values are *computed* from component channel values. -/
theorem outNI_seq {c₁ c₂ : Cmd} {P : Partition}
    (h₁ : J_NI c₁ (outO P) P) (h₂ : J_NI c₂ (outO P) P) :
    J_NI (.seq c₁ c₂) (outO P) P := by
  intro σ σ' hle
  have hble : lowEq P (evalStore c₁ σ) (evalStore c₁ σ') :=
    outNI_boundary h₁ σ σ' hle
  have k₁ := h₁ σ σ' hle
  have k₂ := h₂ _ _ hble
  simp only [obs, outO, tup, resultO, wall, branchO] at k₁ k₂
  injection k₁ with kst₁ krest₁
  injection krest₁ with kt₁ kb₁
  injection k₂ with kst₂ krest₂
  injection krest₂ with kt₂ kb₂
  injection kt₁ with ht₁
  injection kt₂ with ht₂
  injection kb₁ with hb₁
  injection kb₂ with hb₂
  have hT : (eval c₁ σ).2.1 + (eval c₂ (evalStore c₁ σ)).2.1
          = (eval c₁ σ').2.1 + (eval c₂ (evalStore c₁ σ')).2.1 := by omega
  have hB : (eval c₁ σ).2.2 ++ (eval c₂ (evalStore c₁ σ)).2.2
          = (eval c₁ σ').2.2 ++ (eval c₂ (evalStore c₁ σ')).2.2 := by
    rw [hb₁, hb₂]
  simp only [obs, outO, tup, resultO, wall, branchO, eval_seq, glue]
  rw [kst₂, hT, hB]

/-- **Every derivable composite channel is certified.** Any post-processing
    of the total channel — by A3, the whole derivable observation algebra —
    is certified for the composite from the two component certificates
    alone. The seam adds no new obligations. -/
theorem seq_all_channels {c₁ c₂ : Cmd} {P : Partition}
    (h₁ : J_NI c₁ (outO P) P) (h₂ : J_NI c₂ (outO P) P) (f : Val → Val) :
    J_NI (.seq c₁ c₂) (post f (outO P)) P :=
  JNI_postproc f _ _ _ (outNI_seq h₁ h₂)

/-- The integrity reading, verbatim (T1): untrusted data crossing two
    components cannot reach the composite's trusted sink unless a component
    certificate lets it. -/
theorem taint_result_seq {c₁ c₂ : Cmd} {U : Untrusted}
    (h₁ : BoundaryNI c₁ U) (h₂ : J_taint c₂ (resultO U) U) :
    J_taint (.seq c₁ c₂) (resultO U) U :=
  resultNI_seq h₁ h₂

/-! ## The release seam: delimited release composes, non-scalarly -/

/-- **The boundary release certificate (Policy form).** Runs agreeing on Low
    and on the declared release `φ` hand Low-equivalent stores to the next
    component. -/
def BoundaryReleases (c : Cmd) (P : Partition) (φ : Release) : Prop :=
  ∀ σ σ', lowEq P σ σ' → φ σ = φ σ' → lowEq P (evalStore c σ) (evalStore c σ')

/-- The Policy boundary certificate is also a channel claim: exactly
    `ReleasesAtMost` at the boundary channel. -/
theorem boundaryReleases_iff (c : Cmd) (P : Partition) (φ : Release) :
    BoundaryReleases c P φ ↔ ReleasesAtMost c (resultO P) P φ := by
  constructor
  · intro h σ σ' hle hφ
    simp only [obs, resultO]
    congr 1
    funext x
    cases hPx : P x with
    | true  => simp
    | false => simp
               exact h σ σ' hle hφ x hPx
  · intro h σ σ' hle hφ x hPx
    have key := h σ σ' hle hφ
    simp only [obs, resultO] at key
    injection key with hf
    have := congrFun hf x
    simpa [evalStore, hPx] using this

/-- **The composed release.** What the seam reveals: `c₁`'s declared release,
    paired with `c₂`'s release *evaluated at the boundary*. The `mul` of the
    release world threads the first component's map through the second's
    release — a non-scalar certificate algebra, the same semidirect shape as
    the Hölder certificate `(Cg·Cf^rg, rg·rf)` in `transport-kernel/`. -/
def seqRelease (c₁ : Cmd) (φ₁ φ₂ : Release) : Release :=
  fun σ => .pair (φ₁ σ) (φ₂ (evalStore c₁ σ))

/-- **Seam theorem, Policy form (the headline).** If `c₁`'s boundary releases
    at most `φ₁` and `c₂`'s sink releases at most `φ₂`, the composite's sink
    releases at most `seqRelease c₁ φ₁ φ₂`. Declassification budgets
    accumulate across the seam; nothing is silently discharged. -/
theorem releases_seq {c₁ c₂ : Cmd} {P : Partition} {φ₁ φ₂ : Release}
    (h₁ : BoundaryReleases c₁ P φ₁)
    (h₂ : ReleasesAtMost c₂ (resultO P) P φ₂) :
    ReleasesAtMost (.seq c₁ c₂) (resultO P) P (seqRelease c₁ φ₁ φ₂) := by
  intro σ σ' hle hφ
  simp only [seqRelease] at hφ
  injection hφ with hφ₁ hφ₂
  exact h₂ _ _ (h₁ σ σ' hle hφ₁) hφ₂

/-- Closure is the degenerate Policy seam: with constant releases the seam
    theorem specializes to the Closure form (consistency check — the strata
    nest across the seam exactly as they nest per-component). -/
theorem releases_seq_const_consistency {c₁ c₂ : Cmd} {P : Partition} {v w : Val}
    (h₁ : BoundaryNI c₁ P) (h₂ : J_NI c₂ (resultO P) P) :
    ReleasesAtMost (.seq c₁ c₂) (resultO P) P (seqRelease c₁ (fun _ => v) (fun _ => w)) :=
  releases_seq (fun σ σ' hle _ => h₁ σ σ' hle)
               ((closure_is_const_policy c₂ (resultO P) P w).mpr h₂)

/-! ## Non-vacuity: a concrete certified seam -/

/-- `P_leak`'s Policy certificate, restated at the boundary granularity —
    one line from the existing bound. -/
theorem pleak_boundary_releases :
    BoundaryReleases Pleak Phigh φ_bit :=
  (boundaryReleases_iff Pleak Phigh φ_bit).mpr result_releases_at_most_bit

/-- **A certified seam, end to end.** Two policy components in sequence: the
    composite releases at most the paired bits — computed by `releases_seq`
    from the two component certificates, no re-verification of the composite.
    (Here `P_leak` does not write the secret, so both components release the
    same bit; the pair is the honest general form.) -/
theorem pleak_chain_releases :
    ReleasesAtMost (.seq Pleak Pleak) (resultO Phigh) Phigh
      (seqRelease Pleak φ_bit φ_bit) :=
  releases_seq pleak_boundary_releases result_releases_at_most_bit

end ConfTyping
