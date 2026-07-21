# Certified composition

Three Lean 4 formalizations forming one line of work, unified by a single
discipline:

> **Evidence carries its hypotheses, and composition *accumulates* them —
> never discharges or coerces silently.**

Each sub-project is a self-contained Lean package. All are `no sorry` and
axiom-audited; the two mathlib-free ones build instantly, the third needs the
mathlib olean cache (and compiles its Physlib dependency locally).

| dir | what | deps | status |
|---|---|---|---|
| [`conf-typing/`](conf-typing) | confidentiality-typing framework (the IMP timing instance + meta-theory) + the security seam/reception modules | `transport-calculus` (path; mathlib-free) | core closed; security program active (`VULN-COVERAGE.md`) |
| [`transport-calculus/`](transport-calculus) | the transport interface, its qualitative frontier, and the set-theoretic research line it opened | none (mathlib-free) | core proved; frontier reduced to one open question, shipped to its community |
| [`transport-kernel/`](transport-kernel) | instances of the interface against libraries other people built | mathlib, Physlib, `transport-calculus` (path) | tiers 1–5 done |

## The through-line

The same accountancy appears at every level:

- **`conf-typing`** — a discharge of a confidentiality obligation carries its
  evidence: `Discharge.pol` bundles `(φ, proof)`, not bare membership;
  `confidential_transport` carries both strata across the conformance gate;
  the assumption ledger tracks which theorem consumes which condition.
- **`transport-calculus`** — that accountancy made the primitive object. A
  `Bridge` is a map bundled with a certificate; `Bridge.comp` accumulates
  certificates (a monoid action on a distance order), and dropping the
  accumulation makes the composite's proof fail to type-check. Zero axioms.
- **`transport-kernel`** — the interface receives objects *someone else
  built*, and the receptions compose under **one generic law**: mathlib's
  `LipschitzWith` and `HolderWith`, finite Markov kernels, measure-theoretic
  kernels, and quantum channels all land in graded actions served by the same
  `Bridge.comp`. Advanced composition — classical, measure-theoretic, and
  quantum — is certificate accumulation, as theorems.

## What each sub-project actually proves

**`conf-typing`** (mathlib-free; core meta-theorems axiom-free):
- the parametric framework — admissibility (A1–A3), joint generation, bounded
  delimited-release policy, the conformance gate, Boolean soundness;
- the typed rejection of cross-stratum evidence, proved *J-invariant*;
- the corrected §10: among admissible properties the only nondegenerate
  2-safety one is noninterference; separability is the congruence-refinement
  of 2-safety; the k-safety hierarchy above 2 is kernel-determined.

**`transport-calculus`** (mathlib-free; `Bridge.comp` axiom-free):
- `GradedAction M D` and `Bridge.comp` — the interface and its composition law;
- the **qualitative frontier**, bracketed by theorems: complete-lattice /
  image-sup / bounded / directed-finite factorization; the `D3` escapee; the
  cofinal-ruler and countable-cofinality theorems; the transfinite selection
  theorem (`prefix_bounded_cofinal_factors`) with `PrefixBounded` as the
  cardinal-free κ-directedness; the hunt's walls
  (`sigma_directed_cofinal_factors`, `lists_bounded_factors`, `Fb`);
- the **reps engine, machine-checked**: over an abstract index with least
  witnesses, σ-directedness, and countable segments, a coherent sequence with
  a level-monotone representative system is trivial
  (`reps_implies_trivial`), paired with the ω-boundary witness showing the
  regularity hypothesis is load-bearing (`omega_concentration_fails`);
- the **research line** the frontier opened, in prose at graded rigor:
  [`NOTES-coherent-escapee.md`](transport-calculus/NOTES-coherent-escapee.md)
  (fifty-two sections: reps ⟺ trivial in ZFC, chain-freeness of the fiber
  order, the no-go for kill templates, forcing-locality, Theorem B —
  uniformizing dip systems ⟺ trivial — the reduction of the whole question
  to one game invariant, the game's Φ-completeness, the ◊-side kill of
  "everything schedules" (Theorem C), and the two-sided independence
  program whose standing open problem is the canonical walk sequence ρ₃
  under CH), and the standalone problem statement for set theorists,
  [`PROBLEM-dip-schedulability.md`](transport-calculus/PROBLEM-dip-schedulability.md):
  **is every strongly dip-schedulable coherent sequence on ω₁ trivial?** —
  level-factored case proved, toolbox machine-checked; conjectured false
  under MA_ω₁ with canonical witness ρ₃ (the hard part, a ccc, is in ZFC),
  open under CH.

**`transport-kernel`** (mathlib + Physlib + `transport-calculus`):
- **Tier 2** — `comp_reconstructs_lipschitz`, `comp_reconstructs_holder`: the
  generic `Bridge.comp` reconstructs mathlib's own composition lemmas, for a
  scalar and a non-scalar (semidirect-product) certificate algebra.
- **Tier 3** — the Dobrushin data-processing inequality for finite Markov
  kernels, proved from scratch (mathlib has no DPI), with
  `comp_reconstructs_dobrushin` and `coeff_submul`.
- **Tier 3b** — the measure-theoretic DPI over arbitrary measurable state
  spaces (`DobrushinMeasureReceive.lean`: `tvDist`, `tvDist_comp_le`,
  `comp_reconstructs_dobrushin_measure`), built on mathlib's
  `Measure`/`Kernel`.
- **Tier 3c** — discretization consistency: the finite and measure-theoretic
  developments provably agree (`tvDist_toMeasure`, `dpi_via_measure`).
- **Tier 4** — the **quantum** DPI against Physlib
  (`QuantumDobrushinReceive.lean`): trace-distance contraction at
  positive-trace-preserving generality (`traceNorm_map_le` — complete
  positivity not assumed), the quantum Dobrushin bound, the reception in the
  *same* graded action as the finite classical tier
  (`comp_reconstructs_quantum_dobrushin`), and diagonal consistency
  (`classical_contraction_via_quantum`): the finite development embeds into
  both generalizations, all machine-checked to agree. The DPI core is
  PR-shaped for Physlib upstreaming.
- **Tier 5** — the reps theorem at **actual ω₁** (`OmegaOneCoherent.lean`):
  mathlib's `ω₁.ToType` models the abstract index (σ-directedness *is* the
  regularity of ℵ₁), giving `omega1_reps_implies_trivial` — every coherent
  sequence on ω₁ with a pointwise level-monotone representative system is
  trivial — and its contrapositive for nontrivial sequences. To our knowledge
  the first machine-checked theorem about coherent sequences on ω₁. The
  mathlib-free engine and its mathlib model are verified separately and
  compose.

## The security claim (the original goal)

The program's origin is a framework for coding that is *inherently* free of
vulnerabilities. The honest form of that claim — which real vulnerability classes
are excluded by construction, relative to which model, spec, and TCB, and which are
merely carried, assumed, or out of scope — is maintained as a verdict-per-class map
in [`VULN-COVERAGE.md`](VULN-COVERAGE.md), built on the proved classification
machinery (`qualitative_admissible_is_JNI`, `simA3_iff_respectsCoarsening`,
`summary_not_composable`, `confidential_transport`, `Bridge.comp`) and the
integrity module it forced into existence (`taint_is_JNI` — integrity NI is a
relabeling, axiom-free; `blacklist_not_admissible` — output-blacklist
sanitization fails A3, axiom-free). Twelve classes, eight verdicts, every verdict
graded; the popular-but-wrong formulations (output blacklists,
`(ε,δ)`-composition) are rejected by theorems, not by taste. The seam row is
proved end-to-end: certified components compose with *computed* certificates
(`releases_seq`, axiom-free; the non-scalar `seqRelease`), the reception into
the transport interface is an equivalence (`bridge_iff_releases`), the generic
`Bridge.comp` reconstructs the seam theorem (`comp_reconstructs_seq_release`),
and both seam hypotheses are proved load-bearing by explicit failure witnesses
(`broken_seam`, `channel_certs_do_not_compose`). And the flow-property verdicts
are **generated, not hand-proved**: a syntax-directed checker (`secCheck`,
`secCheckD`) manufactures the boundary certificates, so a component earns its
verdict by `decide` — `checker_rederives_pleak_bound` reproduces the hand-proved
Paper-1 release bound as checker output (choice-free), multi-tenant isolation is
checked both ways (`multiplex_isolates_A/B`), and two syntactic checks compose
into one certified Bridge in the transport interface (`certified_pipeline`). And
every guarantee carries its **trusted base** as a composable ledger: a component's
assumptions (`CondBoundary c P Γ`) accumulate by union under the same `Bridge.comp`
(`ledgerBridge_comp_ledger`), can never be silently laundered into evidence
(`ledger_no_silent_discharge`), and are surfaced automatically for a composed
supply chain (`supply_chain_ledger`) — the bill of materials as a theorem. And the
clock is a certified channel, not just a caveat: a timing-sensitive checker
(`secCheckT`) forbids secret-dependent branching and certifies the whole
instrumented outcome — store, running time, and branch trace (`secTyT_sound`) —
rejecting the store-checker's timing-leak witness (`ptime_rejected_T`).

## Scope — what is *not* claimed

- The transport interface is **not** asserted to be the "correct general
  notion" of certified transport. It is a small interface that five
  independent instance families now inhabit under one composition law —
  status earned by instances, revisable by counterexamples.
- The qualitative frontier's last question — dip-schedulability — is **open**,
  not settled: the notes record sixteen verdict flips, each forced by a proof
  or a refutation, and the problem statement grades every arrow ([proved] /
  [argued] / [open]). The MA side of the independence program is a conjecture
  on a cited ccc, not a theorem; the CH side is one standing open problem
  (ρ₃), not a verdict.
- The quantum-DP row (Q4) is a research-pass verdict with two live readings
  (literature gap vs. genuine interface boundary), deliberately unresolved.
- "First machine-checked theorem about coherent sequences on ω₁" is a
  to-our-knowledge claim after an adversarial literature pass (notes §13),
  not a certainty.
- The **method** — adversarially attacking one's own statements and narrowing
  to machine-checked theorems — is how the work was produced, not a validated
  methodology. It travels only if a second hand runs it.

## Building

```sh
# mathlib-free — instant
cd conf-typing        && lake build
cd transport-calculus && lake build

# mathlib + Physlib — needs the olean cache; Physlib's modules compile locally
cd transport-kernel   && lake exe cache get && lake build
```

All pinned to Lean `v4.31.0` (see each `lean-toolchain`); transport-kernel
pins Physlib to a fixed commit sharing this repo's mathlib revision, so the
cache is shared.

`tools/check-claims.sh` guards the READMEs against status drift (retired
claims resurfacing, modules or notes going unmentioned); run it after landing
anything. Per-subdir `README.md` and `CHANGELOG.md` carry the detail; the
top-level [`CHANGELOG.md`](CHANGELOG.md) traces the arc across all three.
