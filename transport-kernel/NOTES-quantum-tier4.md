# Tier 4 recon (Q0): the quantum slot — gap map

Date: recon against `leanprover-community/physlib` at master (shallow clone), July 2026.
Verdict: **gap confirmed, kill-criterion not triggered — the full Q1–Q5 plan stands.**

## What exists (reusable infrastructure)

- **Toolchain**: `leanprover/lean4:v4.31.0` — *identical to transport-kernel's*. Both build
  on mathlib. Integration friction is near zero; note Physlib uses the new module system
  (`module` / `public import`) headers.
- **States**: `MState d` (density matrices over a `Fintype`), `QuantumInfo/States/Mixed/`.
- **Trace distance**: `TrDistance (ρ σ : MState d) : ℝ` with `ge_zero`, `le_one`, `symm`,
  and `eq_abs_eigenvalues` (`½∑|eigenvalues|` form). **Nothing about channels.**
- **Trace norm**: solid API in `ForMathlib/MatrixNorm/TraceNorm.lean` — nonnegativity,
  unitary invariance, `traceNorm_Hermitian_eq_sum_abs_eigenvalues`, singular-value
  characterizations, submultiplicative-with-opNorm lemmas.
- **Channels**: unbundled property classes `IsTracePreserving`, `IsPositive`,
  `IsCompletelyPositive`, `Unital`, `IsHermitianPreserving` with composition lemmas;
  bundled hierarchy includes `PTPMap` and `CPTPMap`. **The PTP-vs-CPTP distinction is
  already first-class**, so the Ruskai-generality statement (positivity + trace
  preservation suffice; CP not needed) is directly expressible.
- **Jordan decomposition**: `HermitianMat` carries `posPart`/`negPart` (`A⁺`, `A⁻`) via
  continuous functional calculus (`ForMathlib/HermitianMat/Proj.lean`), with the
  cfc-characterization lemmas the Q1 proof needs.
- **Entropy DPI**: `Entropy/DPI.lean` is the *sandwiched Rényi* DPI
  (Leditzky–Rouzé–Datta route: trace functional, twirling, Frank–Lieb convexity,
  Stinespring) with quantum relative entropy as corollary — serious machinery, and
  **not** trace-distance contraction.
- Library health: ~84 QuantumInfo modules; 48 `sorry`s repo-wide (living project — any
  Tier-4 file must be checked axiom-clean against its actual imports).

## The gap (Tier 4 slot)

- **Trace-distance contractivity under PTP/CPTP maps: absent.** The only "contractive"
  results are operator-norm lemmas for (sub)unital maps (`Unbundled.lean:808,844`).
- **Dobrushin coefficient / submultiplicativity: absent** (no hits for
  contraction-coefficient machinery anywhere in `QuantumInfo`).

So the mathlib-had-no-DPI situation replays exactly one level up, with the proof
ingredients all present:

> **Q1 target.** `‖Λ(X)‖₁ ≤ ‖X‖₁` for Hermitian `X` and positive trace-preserving `Λ`
> (Jordan-decompose `X = X⁺ − X⁻`; positivity gives `‖Λ(X)‖₁ ≤ tr Λ(X⁺) + tr Λ(X⁻)`;
> trace preservation closes). Hence `TrDistance (Λ ρ) (Λ σ) ≤ TrDistance ρ σ`, at PTP
> generality with CPTP a corollary; then the quantum Dobrushin coefficient
> `η_tr(Λ) := sup over distinguishable pairs`, submultiplicative under composition.

## Plan status

- **Q0 (this file)**: done — gap confirmed.
- **Q1** (trace-distance DPI at PTP generality): open slot confirmed; ingredients listed
  above; estimate unchanged (~a week).
- **Q2** (`Bridge.ofChannel`, `comp_reconstructs_quantum_dobrushin`): lands in `lipGA`;
  headline — finite kernels, measure-theoretic kernels, and quantum channels in the
  *same* graded action under the *same* `Bridge.comp`.
- **Q3** (diagonal embedding; classical DPI as corollary of quantum): fifth
  agree-where-they-overlap instance; completes the tower finite ↪ measure ∧ finite ↪
  quantum, all machine-checked to agree.
- **Q4** (quantum DP two-row check, Hirche–Rouzé–Stilck França): research pass;
  outcome deliberately not pre-committed.
- **Q5** (upstream to Physlib): viable — community umbrella, same toolchain; decide
  after Q1 whether the DPI lives as a Physlib PR with a thin bridge in transport-kernel,
  or in-repo first.

Build note for Q1 session-planning: `lake exe cache get` covers the *mathlib*
dependency only; Physlib's own ~84 QuantumInfo modules compile locally (budget the
first-build time, or check Reservoir for a package cache before starting).

Scoping note, kept honest: quantum enters the transport line here and only here —
channel contraction fits the interface as-is; it does not touch dip-schedulability.
