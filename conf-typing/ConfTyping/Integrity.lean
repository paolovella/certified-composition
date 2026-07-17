/-
  The integrity/taint module — VULN-COVERAGE row 3 (injection), theorems T1 and T2.

  T1 (taint duality): integrity noninterference — untrusted sources cannot
  influence trusted sinks — is `J_NI` at the source/sink relabeling
  (High := untrusted, observation := trusted sink). The §10 apparatus is
  parametric in `(P, o)`, so admissibility, separability, and the 2-safety
  uniqueness theorem apply verbatim: the taint form of injection-freedom is
  the *unique* admissible 2-safety formulation. Sanitizers are the Policy
  stratum's dual — an endorsement carries a proof obligation
  (`InfluencedAtMost`, definitionally `ReleasesAtMost`), not a free pass.

  T2 (blacklist inadmissibility): the popular formulation "output never
  contains the bad value" is a value predicate; it fails A3 by a one-line
  post-processor. Security reading: post-processing is exactly what
  adversarial contexts do to outputs (encodings), so blacklist sanitization
  dies to encodings — as a theorem, not folklore. The framework *forces* the
  flow formulation.

  Scope honesty: IMP has no strings, so "injection" here is the property
  *shape* (influence of untrusted sources on trusted sinks), not a model of
  SQL. The claim graded [proved] in VULN-COVERAGE.md is exactly the shape
  claim; the witnesses (`Pleak` integrity-read) make it non-vacuous.
-/
import ConfTyping.TwoSafety

namespace ConfTyping

/-! ## T1 — the taint reading is a relabeling, and it is forced -/

/-- Untrusted-role partition: `U x = true` reads "x is untrusted
    (attacker-controlled)". Same carrier as the confidentiality `Partition`;
    only the reading of `true` changes. -/
abbrev Untrusted := Partition

/-- Trusted-equivalence: the stores agree on every trusted variable.
    Definitionally `lowEq` at the relabeled partition — the dualization is a
    relabeling, not new structure. -/
def trustEq (U : Untrusted) (σ σ' : Store) : Prop := lowEq U σ σ'

/-- **Integrity noninterference (taint-freedom).** Untrusted inputs cannot
    influence the trusted sink `o`: two runs agreeing on trusted inputs give
    the same sink observation. -/
def J_taint (c : Cmd) (o : Obs) (U : Untrusted) : Prop :=
  ∀ σ σ', trustEq U σ σ' → obs o c σ = obs o c σ'

/-- **T1, the identity.** Integrity NI *is* `J_NI` at the source/sink
    relabeling — an `Iff.rfl`, which is the whole point: no new theory is
    needed for the integrity side, only a reading. -/
theorem taint_is_JNI (c : Cmd) (o : Obs) (U : Untrusted) :
    J_taint c o U ↔ J_NI c o U := Iff.rfl

/-- (A3) for the taint instance — inherited, not re-proved. -/
theorem Jtaint_postproc (f : Val → Val) (c : Cmd) (o : Obs) (U : Untrusted) :
    J_taint c o U → J_taint c (post f o) U :=
  JNI_postproc f c o U

/-- Separability for the taint instance — inherited, not re-proved. -/
theorem Jtaint_separable (c : Cmd) (o₁ o₂ : Obs) (U : Untrusted) :
    J_taint c o₁ U → J_taint c o₂ U → J_taint c (tup o₁ o₂) U :=
  JNI_separable c o₁ o₂ U

/-- **T1, the uniqueness half.** Any admissible (A3), nondegenerate (A2),
    inhabited 2-safety integrity judgment coincides with `J_taint` — the
    `qualitative_admissible_is_JNI` collapse, read at the integrity
    relabeling. The taint form of injection-freedom is not *a* choice of
    property; among admissible 2-safety properties it is the only one. -/
theorem admissible_taint_is_Jtaint (R : TwoSafety)
    (hpost : PostClosed R)
    (hA2 : ¬ (∀ x x', R x x'))
    (hne : ∃ x x', R x x')
    (c : Cmd) (o : Obs) (U : Untrusted) :
    J_rel R c o U ↔ J_taint c o U := by
  have hiff := qualitative_admissible_is_JNI R hpost hA2 hne
  constructor
  · intro h σ σ' ht; exact (hiff _ _).mp (h σ σ' ht)
  · intro h σ σ' ht; exact (hiff _ _).mpr (h σ σ' ht)

/-! ## Endorsement: sanitizers carry proof obligations -/

/-- **Endorsement / sanitization with a proof obligation** — the Policy
    stratum's integrity dual: the sink is influenced by untrusted data at
    most *through* the sanitizer value `φ`. Definitionally `ReleasesAtMost`
    at the relabeling; declaring a sanitizer is not a free pass, exactly as
    declaring a release is not. -/
def InfluencedAtMost (c : Cmd) (o : Obs) (U : Untrusted) (φ : Release) : Prop :=
  ReleasesAtMost c o U φ

/-- Full taint-freedom is the `φ = const` sanitizer — the integrity reading
    of `closure_is_const_policy`, inherited verbatim. -/
theorem sanitize_const_is_taint (c : Cmd) (o : Obs) (U : Untrusted) (v : Val) :
    InfluencedAtMost c o U (fun _ => v) ↔ J_taint c o U :=
  closure_is_const_policy c o U v

/-- Non-vacuity, positive side: `P_leak` integrity-read — `b` untrusted, the
    Low store the trusted sink — flows to the sink at most through the
    sanitized bit. The *same theorem* as the confidentiality bound; the map's
    "cross-tenant isolation is literally NI" row rests on this reusability. -/
theorem pleak_influenced_at_most_bit :
    InfluencedAtMost Pleak (resultO Phigh) Phigh φ_bit :=
  result_releases_at_most_bit

/-- Non-vacuity, negative side: the full-copy program defeats the
    bit-sanitizer bound — endorsement obligations are falsifiable. -/
theorem full_flow_defeats_sanitizer :
    ¬ InfluencedAtMost Pfull (resultO Phigh) Phigh φ_bit :=
  result_full_not_bounded_by_bit

/-! ## T2 — blacklist sanitization is inadmissible -/

/-- A value-predicate judgment: "the observed value always satisfies `Q`" —
    the blacklist/output-sanitization shape ("output never contains the bad
    string"), stated at the judgment level. -/
def J_pred (Q : Val → Prop) : JTy := fun c o _ => ∀ σ, Q (obs o c σ)

/-- **T2, general form.** No nontrivial value-predicate judgment satisfies
    (A3): if `Q` rules out some value and some channel satisfies `J_pred Q`,
    then one post-processor — an *encoder* — breaks it. Post-processing is
    what adversarial contexts do to outputs, so a blacklist "guarantee" is
    not a guarantee against any adversary that can re-encode. -/
theorem value_predicate_not_admissible (Q : Val → Prop)
    (hbad : ∃ v, ¬ Q v) (hgood : ∃ (c : Cmd) (o : Obs), ∀ σ, Q (obs o c σ)) :
    ¬ (∀ (f : Val → Val) (c : Cmd) (o : Obs) (P : Partition),
        J_pred Q c o P → J_pred Q c (post f o) P) := by
  intro hA3
  obtain ⟨bad, hQbad⟩ := hbad
  obtain ⟨c, o, hall⟩ := hgood
  exact hQbad (hA3 (fun _ => bad) c o (fun _ => false) (fun σ => hall σ) (fun _ => 0))

/-- The blacklist judgment: the sink never emits the forbidden value. -/
def blacklist (bad : Val) : JTy := J_pred (· ≠ bad)

/-- `wall` on `P_leak` never emits `.bits []` — a channel satisfying the
    blacklist, so the refutation below is not vacuous. -/
theorem wall_never_bits : ∀ σ, obs wall Pleak σ ≠ Val.bits [] := by
  intro σ h
  simp only [obs, wall] at h
  exact Val.noConfusion h

/-- **T2, the instance.** The blacklist judgment fails (A3): it holds of a
    real channel and is broken by the constant re-encoder. Hence — with T1's
    uniqueness half — the framework *forces* the flow formulation of
    injection-freedom: the blacklist shape is not admissible, and the
    admissible 2-safety shape is uniquely `J_taint`. -/
theorem blacklist_not_admissible :
    ¬ (∀ (f : Val → Val) (c : Cmd) (o : Obs) (P : Partition),
        blacklist (Val.bits []) c o P → blacklist (Val.bits []) c (post f o) P) :=
  value_predicate_not_admissible (· ≠ Val.bits [])
    ⟨Val.bits [], fun h => h rfl⟩
    ⟨Pleak, wall, wall_never_bits⟩

end ConfTyping
