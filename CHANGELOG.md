# Changelog — certified composition

Top-level arc across the three sub-projects. Each subdir keeps its own detailed
`CHANGELOG.md`; this traces the line of work as a whole. Dates are when the work
landed.

## conf-typing — the confidentiality-typing framework (mathlib-free)

- **0.1 – 0.3** — mechanized the IMP timing instance: instrumented semantics +
  determinism; parametric `J` with admissibility (A1–A3) and separability;
  the `P_leak` worked example; strata, the no-coercion discharge judgment, the
  J-invariant rejection; the conformance gate; Boolean soundness. Bounded the
  policy stratum (delimited release with a real proof obligation — closing the
  unbounded-permit hole) and made the gate transport *both* strata.
- **0.4 – 0.5** — joint generation and completeness (Thm. 2) via the factoring
  bridge (Prop. 1); separability-equivalence.
- **0.6 – 0.8** — the corrected §10: "separable ⟺ 2-safety" is **false**
  (`Rbad`); among admissible properties the only nondegenerate 2-safety one is
  noninterference; the k-safety hierarchy above 2-safety is kernel-determined
  (no genuinely k-ary admissible atoms).
- **0.9** — the Πₖ up-set characterization (`simA3_iff_respectsCoarsening`):
  admissible ⟺ closed upward under kernel coarsening, with the realizability /
  observation-cardinality condition pinned explicit.

## transport-calculus — the certified-morphism interface (mathlib-free)

- **0.1** — first cut: a `Bridge` carrying a certificate, `Bridge.comp`
  accumulating it; existence demonstrated by *composition* of two certified
  bridges (not a single morphism). Zero axioms.
- **0.2 (the eighth catch)** — corrected `Grade` → `GradedAction`: contact with
  mathlib's real `LipschitzWith` revealed that grade and distance are *two*
  types (`ℝ≥0` acting on `ℝ≥0∞`), a conflation the degenerate `Nat` (`M = D`)
  instance had hidden. The first correction delivered by an external object
  rather than internal review.
- field `coeff` → `cert`, and the over-claiming "genus / existence proof"
  framing dropped to "a common interface," once the Hölder instance showed the
  certificate need not be numeric.

## transport-kernel — mathlib instances

- **Tier 1** — mathlib olean cache stood up (the infra that gates importing
  anything).
- **Tier 2a** — `comp_reconstructs_lipschitz`: the genus receives mathlib's
  `LipschitzWith` and reconstructs `LipschitzWith.comp`.
- **Tier 2b** — `comp_reconstructs_holder`: a *non-scalar* pair certificate
  `(C, r)` with a semidirect-product law; the same `Bridge.comp` reconstructs
  `HolderWith.comp`. Two accumulation algebras, one composition law.
- **Tier 3** — Markov-kernel / Dobrushin (total variation), finite state spaces:
  the data-processing inequality `dpi` proved from scratch (coupling/overlap
  argument — mathlib has no DPI), `Bridge.ofKernel`, and
  `comp_reconstructs_dobrushin`: advanced composition as generic certificate
  accumulation. The quantitative centre, no longer prose.
- **Tier 3b** — the measure-theoretic Dobrushin contraction, arbitrary
  measurable state spaces: `tvDist` (TV distance for measures — absent from
  mathlib) and `tvDist_comp_le`, the DPI for `ProbabilityTheory.Kernel`
  pushforward `κ ∘ₘ μ`, via Hahn decomposition + the coupling argument in
  additive integral form (subtraction-free; no Fubini). Lands in the *same*
  graded action as Lipschitz (`lipGA`), and `Bridge.comp` reproduces
  submultiplicativity (`comp_reconstructs_dobrushin_measure`), also at kernel
  level through mathlib's own `∘ₖ` (`tvDist_kernel_comp_le`). The "finite-state
  only" caveat is discharged.
- **Tier 3c** — the discretization consistency lemma: `Dist.toMeasure` (Dirac
  embedding) with `tvDist_toMeasure` proving the finite `tvd` and the
  measure-theoretic `tvDist` are the same number, `toMeasure_push` matching the
  finite pushforward with `κ ∘ₘ ·`, and `dpi_via_measure` re-deriving the finite
  DPI as a corollary of the measure-theoretic one. The "not yet formally
  linked" caveat is discharged; the two Dobrushin developments provably agree
  where they overlap.

## Consolidation

- Merged the three previously-separate repos into this monorepo with a top-level
  README and CHANGELOG. Aligned the `cert` field name and the framing across
  `transport-calculus` and `transport-kernel` (the two had drifted —
  `coeff`/`cert` and stale "genus" language — while developed separately).
