# transport-kernel — the genus, instantiated against mathlib

Companion to the mathlib-free `transport-calculus` repo (which states the genus
and proves `Bridge.comp` with **zero axioms**). This repo does the thing a
mathlib-free abstraction cannot do for itself: **plug the interface into objects
someone else built**, and see whether it receives them.

Requires the mathlib olean cache (`lake exe cache get`); needs Lean 4.31.0.

## The three-tier cost ledger (so it isn't rediscovered mid-session)

| tier | what | cost | status |
|---|---|---|---|
| 1 | olean cache | multi-GB infra; gates *importing anything* | **done** (5.8G, 8542 oleans) |
| 2a | `LipschitzWith` receive | cache only — no new math | **done**, this repo |
| 2b | `HolderWith` receive | cache only — non-scalar certificate | **done**, this repo |
| 3 | Dobrushin / TV instance | cache **+** from-scratch data-processing inequality | **done** (finite state spaces), this repo |
| 3b | measure-theoretic Dobrushin | from-scratch TV distance + DPI over mathlib's `Measure`/`Kernel` | **done** (arbitrary measurable spaces), this repo |
| 3c | discretization consistency | Dirac embedding; `tvd`/`tvDist` proved equal; finite DPI re-derived from the measure one | **done**, this repo |
| 4 | quantum trace-distance DPI + Dobrushin | Physlib (`MState`, `PTPMap`/`CPTPMap`, `traceNorm`, Jordan via cfc) + from-scratch contraction | **done** (Q1–Q3), this repo; Q4 verdict recorded, Q5 PR-ready |
| 5 | the reps theorem at actual ω₁ | mathlib ordinals (`ToType`, regularity of ℵ₁) + `TransportCalculus` as a path dependency | **done** (`OmegaOneCoherent.lean`) |

## Tier 2 — the result (`TransportKernel/LipschitzReceive.lean`)

The genus receives mathlib's actual contractive morphisms:

- `lipGA : GradedAction ℝ≥0 ℝ≥0∞` — contraction constants (`ℝ≥0`) acting on
  extended distances (`ℝ≥0∞`) by coerced multiplication. **Grade ≠ distance** —
  the `M ≠ D` separation the eighth catch forced, now carried by the real types
  mathlib uses, with the coercion `ℝ≥0 ↪ ℝ≥0∞` as the action.
- `Bridge.ofLipschitz hf` — a `LipschitzWith K f` hypothesis lands *directly* in
  the `contracts` slot, no proof work: `edist (f x) (f y) ≤ K * edist x y` is
  exactly the certificate the interface asks for.
- `comp_reconstructs_lipschitz` — **the reception, as a theorem**: the generic
  `Bridge.comp` applied to two Lipschitz bridges is, definitionally, a proof of
  `LipschitzWith (Kf * Kg) (f ∘ g)`. The interface reproduces mathlib's own
  `LipschitzWith.comp` from generic certificate accumulation.

So the abstraction read off one toy proof (`Nat`, the degenerate `M = D` slice)
**receives an independently-built instance** (ℝ≥0 acting on ℝ≥0∞) and recovers
its composition law. That is reuse evidence of the only kind that counts:
survival of contact with an object not designed to fit.

## Tier 2b — a *different certificate algebra* (`TransportKernel/HolderReceive.lean`)

Lipschitz is a scalar certificate (`ℝ≥0`) accumulating by multiplication. Hölder
continuity is the harder test: the certificate is a **pair** `(C, r) : ℝ≥0 × ℝ≥0`
and `HolderWith.comp` accumulates it by a *semidirect-product* law

```
(Cg, rg) ⋄ (Cf, rf) = (Cg · Cf ^ rg,  rg · rf)      acting on distance by  C · d ^ r
```

- `holderGA : GradedAction (ℝ≥0 × ℝ≥0) ℝ≥0∞` — the non-scalar grade monoid; the
  `act_mul` field is real `rpow` algebra (`mul_rpow_of_nonneg`, `rpow_mul`,
  `coe_rpow_of_nonneg`), and it closes.
- `comp_reconstructs_holder` — the **same** generic `Bridge.comp` reconstructs
  `HolderWith.comp`, definitionally, no extra proof work.

This is the instance that settles the review's "certificate need not be numeric":
the grade monoid here is `ℝ≥0 × ℝ≥0` with a twisted multiplication, not a number.
Two takeaways:

- **The interface is reusable across accumulation *algebras*, not just objects.**
  Lipschitz (scalar) and Hölder (pair, semidirect) are *different monoids*, and
  the same `Bridge.comp` serves both. (Note `HolderWith C 1 = LipschitzWith C`,
  so Lipschitz is the `r = 1` slice — same object, but a genuinely different
  grade algebra, which is the point.)
- **It retroactively justifies keeping the name `GradedAction`.** A "grade" need
  not be numeric — a grading by *any* monoid qualifies, and `ℝ≥0 × ℝ≥0` with the
  semidirect law is exactly such a monoid. So the review's suggested rename to
  `CertifiedAction` would have been lateral, not corrective; declining it (as
  naming ahead of an instance) was right, and this instance shows why.
- **The interface asks only for `act_mul`, not standalone monoid associativity.**
  The Hölder `⋄` *is* associative, but the existence proof never needed that —
  composition of two bridges requires only the action-compatibility `act_mul`.
  Leaner than a monoid action.

## Tier 3 — the quantitative centre, built from scratch (`TransportKernel/DobrushinReceive.lean`)

Lipschitz and Hölder were *received*: mathlib already proves the contraction, and the
interface plugs it in with no new math. The Dobrushin instance is the opposite, and it is
the reason the whole interface exists — mathlib has **no** data-processing inequality, so
the contraction is proved here, over **finite state spaces**, and only then handed to the
interface. `M = ℝ≥0` (Dobrushin coefficients) acts on `D = ℝ` (TV distances) by
multiplication (`dobrushinGA`).

- `Dist S`, `Kernel S`, `Kernel.push` — finite probability distributions on a `Fintype`,
  stochastic matrices, and pushforward `(push μ)(t) = ∑ₛ μ(s) K(s,t)`.
- `tvd μ ν = ½∑|μ−ν|` — total-variation distance.
- **`dpi`** — the data-processing inequality: if every pair of rows is within TV `η`, then
  `tvd (push μ) (push ν) ≤ η · tvd μ ν`. Proved from scratch by the coupling / overlap
  argument (Jordan-split `μ − ν` into parts of equal mass `m`, couple by the outer product
  `dp ⊗ dm`, bound the pushed overlap below by `(1 − η)·m` via superadditivity of `min`).
  This is the genuine formalization — century-old, non-novel probability, but *absent from
  mathlib*, so built here. Axioms: `propext, Classical.choice, Quot.sound` — no `sorry`.
- `Bridge.ofKernel` — a kernel with coefficient `η` **is** a certified bridge: pushforward
  in the map slot, `η` in the certificate slot, `dpi` in `contracts`.
- **`comp_reconstructs_dobrushin`** — the reception as a theorem: the generic `Bridge.comp`
  applied to two kernel bridges yields the *submultiplicative* bound `η(K)·η(L)` on the
  composed pushforward. **Advanced composition is certificate accumulation.**
- `coeff_submul` — the same law at certificate level: `η(K∘L) ≤ η(K)·η(L)`, via `dpi`
  applied to the composed kernel's rows.

So the interface does not merely re-file objects mathlib already contracts; it **hosts a
contraction theorem mathlib does not have**, and reproduces its composition law generically.
This is the quantitative payload the qualitative order-theory line (in `transport-calculus`)
was scaffolding for.

## Tier 3b — the measure-theoretic generalization (`TransportKernel/DobrushinMeasureReceive.lean`)

The finite-state caveat, discharged. Mathlib has no total-variation distance between
measures and no data-processing inequality, so both are built here over **arbitrary
measurable state spaces**, stated against mathlib's own objects
(`MeasureTheory.Measure`, `ProbabilityTheory.Kernel`, the pushforward `κ ∘ₘ μ`):

- **`tvDist μ ν = ⨆ (A measurable), μ A − ν A`** — TV distance in `ℝ≥0∞` (truncated
  excess; for probability measures symmetric — `tvDist_comm` — and equal to the
  classical TV distance).
- **`tvDist_comp_le`** — the measure-theoretic DPI: if every pair of kernel measures is
  within TV `η`, then `tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ η · tvDist μ ν`. Same coupling
  argument as the finite case, in *additive* integral form: Hahn-decompose `(μ, ν)`,
  build the Jordan parts as genuine measures with `μ + ξ⁻ = ν + ξ⁺` (pure measure
  algebra, no truncated subtraction), then the averaging bound
  `m·(κ∘ₘξ⁺)A ≤ m·((κ∘ₘξ⁻)A + η·m)` — constant integrals and monotonicity only, no
  Fubini. Axioms: `propext, Classical.choice, Quot.sound` — no `sorry`.
- **`Bridge.ofMarkovKernel`** — the instance lands in the **same graded action as
  Lipschitz** (`lipGA`, ℝ≥0 acting on ℝ≥0∞), with `X = ProbabilityMeasure α`: one
  accumulation algebra now hosts mathlib's contractive maps *and* the from-scratch
  Dobrushin contraction.
- **`comp_reconstructs_dobrushin_measure`** — the generic `Bridge.comp` yields the
  submultiplicative bound `η(K)·η(L)` on the iterated pushforward; and
  `tvDist_kernel_comp_le` states the same law through mathlib's own kernel composition
  `∘ₖ` — advanced composition as certificate accumulation, on continuous state spaces.

The finite case (`DobrushinReceive.lean`) remains the combinatorial heart and is kept:
its `½∑|·|` form and explicit outer-product coupling are the readable proof; the
measure version is the same idea against mathlib's kernel infrastructure.

## Tier 3c — the discretization consistency lemma (`TransportKernel/DobrushinConsistency.lean`)

The loop between the two Dobrushin developments, closed. `Dist.toMeasure` embeds a
finite distribution as a sum of weighted Diracs (over any `DiscreteMeasurableSpace`),
and then:

- **`tvDist_toMeasure`** — the consistency lemma:
  `tvDist μ° ν° = ENNReal.ofReal (tvd μ ν)`. The `ℝ≥0∞`-valued sup and the real
  `½∑|·|` are the *same number* under the embedding; the sup is attained on
  `{s | ν s ≤ μ s}`, and the real side goes through the exposed overlap identity
  `tvd_eq_one_sub_sum_min` (so the two files share actual proof structure, not just
  a name).
- **`Kernel.toMKernel`, `toMeasure_push`** — a stochastic matrix is a mathlib Markov
  kernel, and the finite pushforward `K.push` commutes with the embedding into
  `κ ∘ₘ ·`.
- **`dpi_via_measure`** — the payoff: the finite DPI re-derived as a *corollary* of
  the measure-theoretic `tvDist_comp_le`, by transporting hypothesis and conclusion
  through the consistency lemma. The two developments provably agree where they
  overlap. Axioms: `propext, Classical.choice, Quot.sound` — no `sorry`.

## What this is *not* (kept honest)

- Not "the genus is correct" — four external/built instances are data points, not a
  characterization.
- `tvDist` is defined as the one-sided sup; symmetry and the classical-TV reading are
  proved *for probability measures* (`tvDist_comm`), which is the regime every theorem
  here uses. It is not developed as a metric on general finite measures.

## Tier 4 — the quantum tier (`TransportKernel/QuantumDobrushinReceive.lean`)

Physlib (leanprover-community; the March-2026 Lean-QuantumInfo + PhysLean merge) has
`TrDistance` with basic properties but **no channel contractivity and no Dobrushin
coefficient** (recon: `NOTES-quantum-tier4.md`) — the mathlib-had-no-DPI situation, one
level up. So the contraction is proved here, from scratch, and received:

- **`traceNorm_eq_trace_posPart_add_trace_negPart`** — the Jordan form of the trace
  norm, `‖A‖₁ = tr A⁺ + tr A⁻`, glued from Physlib's eigenvalue characterization and
  cfc trace formula.
- **`traceNorm_map_le`** — the quantum DPI at **positive trace-preserving generality**:
  complete positivity is *not* assumed (Ruskai) — positivity and trace preservation
  suffice. The honest minimal hypothesis, sharper than the CPTP textbook statement;
  CPTP follows via `CPTPMap.toPTPMap`.
- **`trDistance_apply_le`** — `T(Λρ, Λσ) ≤ T(ρ, σ)` for every `PTPMap` on states.
- **`QDobrushinBound`, `qDobrushinBound_one`** — the quantum Dobrushin coefficient as a
  bound hypothesis; the DPI is the universal `η = 1` instance.
- **`Bridge.ofPTPChannel`, `comp_reconstructs_quantum_dobrushin`** — the reception, in
  **`dobrushinGA`, the same graded action as the finite classical tier**: finite
  kernels (Tier 3), measure-theoretic kernels (Tier 3b), and quantum channels (Tier 4)
  now compose under the *same* generic `Bridge.comp`. Three physical regimes, one
  composition law — the strongest reuse evidence the interface has produced.

Axioms: `propext, Classical.choice, Quot.sound` — no `sorry`, checked against the full
Physlib import cone (the library carries `sorry`s elsewhere; none in this cone).
**Q3 (`TransportKernel/QuantumDobrushinConsistency.lean`) — the tower closes.**
`Dist.toMState` embeds distributions as diagonal states; `trDistance_toMState` proves
the quantum trace distance restricted to diagonals IS the classical `tvd` (Jordan
trace-norm lemma + `cfc_diagonal`); `Kernel.toQChannel` embeds stochastic matrices as
diagonal-output PTP channels; `toMState_push` intertwines; and
`classical_contraction_via_quantum` re-derives `tvd (K.push μ) (K.push ν) ≤ tvd μ ν`
from the quantum DPI. With Tier 3c: the finite development embeds consistently into
both the measure-theoretic and the quantum generalizations, all machine-checked to
agree. (Scope note: the quantum corollary transports the η = 1 contraction; the
pairwise-row-η refinement stays classical.) Axiom-clean.

**Q4 (research pass, recorded in `NOTES-quantum-tier4.md`)**: quantum (ε,δ)-DP is the
hockey-stick condition (Hirche–Rouzé–Stilck França); their sequential composition is a
product of channel contraction coefficients — exactly this tier's certificate
accumulation — but no general adaptive composition theorem exists and no tensorizing
f-DP analogue appears: either a literature gap or a genuine interface boundary;
deliberately left open. **Q5**: the five DPI-core declarations have zero TransportKernel
dependencies and are PR-shaped for Physlib upstreaming.

## Tier 5 — the reps theorem at actual ω₁ (`TransportKernel/OmegaOneCoherent.lean`)

The mathlib-free `transport-calculus` proves the set-theoretic hunt's four-step engine
over an abstract index (`reps_implies_trivial`); its intended model, ω₁, is not
constructible there. This file builds the model from mathlib and instantiates:

- **`OmegaOne := ω₁.ToType`** — the countable ordinals as a `Type 0` well order, with
  the `ToType.mk : Iio ω₁ ≃o ω₁.ToType` transfer API.
- **`wellIndexOmegaOne`** — least witnesses from well-foundedness;
  **`sigmaDirected_omegaOne`** — σ-directedness IS the regularity of ℵ₁
  (`Ordinal.iSup_lt_of_lt_cof` + `isRegular_aleph_one`); **`countableSegments_omegaOne`**
  — segments are countable via `#o.ToType = o.card` below ℵ₁;
  **`unbounded_omegaOne`** — countability is closed under successors.
- **`finiteP_iff_finite`** — the abstract list-coverage finiteness is `Set.Finite`, so
  the abstract coherence is the standard mod-finite notion.
- **`omega1_reps_implies_trivial`** — *every coherent sequence on ω₁ admitting a
  pointwise level-monotone system of representatives is trivial* — and its
  contrapositive **`nontrivial_coherent_no_reps`**: a nontrivial coherent sequence
  (e.g. Todorcevic's walk families, witnessing `H¹(ω₁; ℤ) ≠ 0`) admits no monotone
  representative system. To our knowledge the first machine-checked theorem about
  coherent sequences on ω₁. Axioms: `propext, Classical.choice, Quot.sound`; no `sorry`.

The dependency structure is the point: the four-step *combinatorial engine* is verified
in a mathlib-free package (`TransportCalculus`, required by path), and mathlib
contributes exactly the three index facts the abstract hypotheses isolate — regularity,
countable segments, no top. The proof of the engine and the construction of its model
are machine-checked *separately* and compose.

## Naming note

The structure is `GradedAction` and `cert` is its grade. The certificate need
not be numeric — the math requires only an associative composition, an action,
and monotonicity — so a non-numeric certificate (a policy, an effect) could
inhabit it. It is *not* renamed to `CertifiedAction` preemptively: that would be
naming ahead of an instance that forces it. Rename when one lands, not before.
