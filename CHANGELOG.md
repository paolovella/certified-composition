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
- **the qualitative frontier, bracketed** — the non-monotone escapee question
  resolved into: complete lattice ⇒ factors; image-family sups ⇒ factors (and
  are not necessary); non-directed `D` ⇒ escapee (`D3`); directed + finite /
  bounded ⇒ factors; countable cofinality ⇒ factors (cofinal ℕ-ruler,
  cub-monotonized). Residual: uncountable cofinality.
- **the transfinite theorem, proved — "unformalizable" was wrong.** The
  uncountable-cofinality selection, previously called "plausible — unchecked,
  and unformalizable here (transfinite recursion, cardinals)", is now a
  mathlib-free theorem (`prefix_bounded_cofinal_factors`): selection over any
  well-ordered index needs **no limit steps** (`wruler_defeats_bounded_escapee`,
  `Classical.choice` only), and monotonization runs on Lean-core
  `WellFounded.fix` under `PrefixBounded` — `κ`-directedness stated without
  cardinals, weakened to segment-indexed families. `prefixBounded_of_directed`
  proves directedness supplies it at `ω` (re-deriving the countable case);
  uncountably it is not a theorem. The residual is now exactly one hypothesis
  wide: whether `Directed` without `PrefixBounded` admits an escapee.
- **the hunt — two walls proved, no capture.** Candidates die informatively
  (`ω₁ × ℕ` and ideal-of-sets orders are conditionally complete; chain designs
  self-dominate; gap encodings can't force a dominator *under* anything). Wall
  one: `sigma_directed_cofinal_factors` — σ-directedness + an ω₁-like cofinal
  family (`CountableSegments`) forces factorization, so an escapee there must
  contain a countable unbounded family. Wall two: `lists_not_sigma_directed` +
  `lists_bounded_factors` — `List Nat` under membership-inclusion fails
  σ-directedness yet factors everything (filtered bounding list = least upper
  bound), so failing σ-directedness is not sufficient. Residual profile: break
  conditional completeness unovershootably, with only-global failure
  (Aronszajn/gap shape); existence may be independent of ZFC.
- **the coherent-sequence encoding — the profile is realizable, up to set
  theory.** On paper: the fiber order `D_coh(e)` over a nontrivial coherent
  sequence (ZFC, via walks) is directed with finite joins, not σ-directed,
  and join-incomplete (bounded families with *no minimal* upper bound) — the
  first structure passing every wall. The escapee question on it reduces to a
  coherent-sequence uniformization principle (level-monotone bounded coherent
  sequences are provably trivial, so the canonical dominator is obstructed;
  MA/◊-sensitive, plausibly independent of ZFC). Formalized shadow: `Fb`
  (levels ℕ∪{∞}, finite patches over a constant floor) — directed, not
  σ-directed, bounded family with no minimal ub (`fb_no_minimal_ub`,
  choice-free), yet factors via an explicit ladder ruler (`fb_factors`). So
  the dip pathology alone is also non-lethal at countable cofinality; the
  hunt's remaining question lives at ω₁, outside a mathlib-free repo.
- **the ◊-side attempt (`NOTES-coherent-escapee.md`) — canonical dominators
  die; one bridge remains.** Prose rigor: two ZFC lemmas (level-preserving
  systems always factor; representative systems ⇒ everything factors, with
  "trivial ⇒ factors" as corollary) and one ◊ theorem (a coherent sequence
  with *no* representative system — block-diagonal lowering against
  ◊-guessed partial systems). The bridge from rep-death to an escapee did
  not close: pressure needs boundable infinite families, legality makes
  their requirements mod-finite-satisfiable, fibers absorb finite defects,
  and every coherence-extraction from a dominator needs the reps whose
  absence powers the kill. Open core, one sentence: does factors-everything
  imply reps? The note records the legal pressure system `Σ_succ`, the "+1
  trap", the self-obstruction phenomenon, and the two decisive follow-ups.
- **the ◊ theorem collapses to ZFC: reps ⟺ trivial.** Checking whether the
  walk sequences already lack reps answered far more strongly — *every*
  nontrivial coherent sequence lacks representative systems, in ZFC
  (coherence pins pairwise rep-differences finite; level-monotonicity
  concentrates countably many witnesses at one countable level, so movement
  below any α is finite; the escape set has finite initial segments, hence
  bounded; bounded escape trivializes). The ◊ construction is retired as
  unnecessary (kept in the note for the record); "canonical dominators
  exist iff trivial" is a ZFC dichotomy; the independence suspicion
  retreats to non-canonical dominators only; and the Bridge is restated as
  a pure ZFC question over the walks' `ρ₁`. If it holds, the transport
  escapee exists in ZFC.
- **the dip-side attempt — correction, chain-freeness, flipped verdict.**
  `Σ_succ` factors after all (uniform one-level shift dominator) — the
  prior "pressure" claim is retracted; limit-raising systems are legal
  exactly over block-tame sequences, whose tameness builds the dominator
  (absorption pattern, fourth instance). New ZFC theorem: `D_coh(e)` has
  an ω₁-chain with cofinal levels iff `e` is trivial (a chain is a
  club-indexed rep system) — over nontrivial sequences the fiber order is
  provably chain-free, explaining every failed chain-mediated argument.
  Kill schemes close into the legality circle at every entry (per-element
  budgets, countable-union accumulation, slice-illegality under floor
  sabotage). Verdict flipped: evidence now favors ZFC-factoring of all
  fiber orders; the escapee, if anywhere, needs a different species of
  directed order. Missing lemma named: global coordination of per-element
  finite gap-fill corrections.
- **the coordination lemma attempted — residue isolated, verdict
  oscillates.** A ⊑-refining ω₁-recursion with a finite-ledger invariant
  works except at one point; requirement-excess inherits uniformly (ZFC
  lemma — all past `M`-contributions land in one finite set `F_u`); the
  residue is exactly past-floor inversions on gap regions against moving
  targets, with level-overshoot provably useless. Sufficient condition
  named (uniformizing dip system; trivial sequences have one), which
  almost-extracts a rep system (one fiber-control gap). The Bridge is
  squeezed between per-`u` absorption (necessary) and uniform dips
  (sufficient) — one Fodor step and one extraction repair apart. If both
  close: dominator ⇒ trivial, and the escapee exists in ZFC.
- **the Fodor step attempted — the circle proves itself; the core goes
  Aronszajn.** Pressing down is sound; its input is unobtainable: probe
  systems exerting cofinal floor-pressure are legal iff sup-coherence
  already holds (the circle is an equivalence now). New ZFC lemmas:
  single-target dips free; bounded families never obstruct; the
  chain-continuation lemma (dips against a chain's own sup serve every
  continuation — the moving target is fake for chains). But the reduction
  is self-similar under per-element targets; club targets die over the
  ◊-sequence; and §7's "overshoot useless" is corrected — overshooting
  parks values on post-kill floors, making a dominator a `D`-indexed
  rep-like selection whose kill needs chains that chain-freeness forbids.
  Both directions lose their weapon at the last step. Hard core isolated:
  monotone fiber-valued selection with pairwise-finite deviations on the
  chain-free order — Aronszajn-type uniformization. Third flip: lean is
  now independence, one named gap per side.
- **the ◊-side gap attempted — a no-go theorem for the kill template
  (fourth flip).** Kills are structurally thin (coherence: finite below
  every lower level, inherited above), so they never accumulate;
  staggered kills contradict pairwise coherence; committed-value forcing
  needs img-levels cofinal in the kill stage, which legality forbids,
  markers block (infinite markers ∉ fiber), and delayed levels cannot
  reach (coherence caps late deviation at finite). Template no-go: legal
  forcing is bounded-family forcing; bounded families are absorbable;
  kills need unabsorbable forcing — covers all five kill designs tried.
  First one-sided evidence in the arc. Lean, fourth revision:
  ZFC-factoring; the MA-side route re-read as a candidate ZFC proof with
  its missing piece named (forcing-locality).
- **forcing-locality proved; the Bridge becomes a game on `e` alone.**
  The anti-kill (fiberhood-forcing, the one pattern the no-go missed)
  breaks nothing by pairwise coherence — so nothing legal forces values
  above eventual floors. Systems and dominators eliminate: down-sets have
  ⊑-cofinal ω-chains; requirement-sups are legality-bounded; the sole
  residue is floor-baking along chains, finite per pair and fractally
  self-similar across chains. Result: factors-everything(e) ⟺
  dip-schedulable(e), a two-quantifier combinatorial game on the coherent
  sequence alone. The seven-session hunt ends at one line: is every
  dip-schedulable coherent sequence trivial? Handed to set theory in
  final form.
- **`PROBLEM-dip-schedulability.md`** — the standalone problem statement
  for set theorists: definitions from scratch, the strong/weak game, the
  implication diagram with rigor-graded arrows (the strong/weak split and
  the realizability gap presented honestly rather than papered over),
  four numbered questions, four proved ZFC lemmas with proofs, the
  thinness remark (why naive ◊-attacks fail), and the
  independence-boundary discussion. Pure ω₁ combinatorics; no knowledge
  of the program required.
- **the reps theorem machine-checked in shadow.** `reps_implies_trivial`:
  over an abstract index with least witnesses, σ-directedness, and
  countable segments (the three ω₁ properties the proof uses), a coherent
  sequence with a level-monotone representative system is trivial —
  axiom-clean, no sorry, with a mathlib-free pigeonhole and
  totality-from-least-witnesses (axiom-free) as supporting lemmas. Paired
  with the boundary: ℕ fails σ-directedness and the concentration step
  provably fails there (`omega_concentration_fails` — the χ family moves
  at every coordinate). The hunt's engine is now machine-checked, and its
  regularity hypothesis demonstrably load-bearing.
- **Theorem B: uniformizing dip systems ⟺ trivial (ZFC); Question 1′
  proved.** The §7 H-extraction is refuted (wasteful dips hide columns
  below ω-cofinality levels) and replaced by the honest-column argument:
  monotone along honest levels; never-honest points finite per level
  automatically (they sit in `X_γ ∪ U_γ`); unbounded columns killed by
  witness-concentration at one level; the max honest value trivializes,
  sandwiched at a late honest level. Relativizes to cofinal level sets;
  corollary: level-factored strong schedulability ⟹ trivial. Question 1
  of the problem statement is rescoped to element-dependent schedules.
  Phase-0 hygiene: stale Dobrushin claims fixed in transport-calculus
  README; `tools/check-claims.sh` drift guard added.

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
