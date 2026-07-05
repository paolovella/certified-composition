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
- **Q1+Q2: DONE** (same session as Q0+1 day — far under the week estimate; the Physlib
  API was exactly right-shaped). `QuantumDobrushinReceive.lean`, axiom-clean against the
  full import cone. Note for the estimate ledger: the recon's signature-pinning made the
  file compile with only three error classes (a notation `open`, a name ambiguity, a
  universe restriction on `Bridge`).
- **Q1** (trace-distance DPI at PTP generality): open slot confirmed; ingredients listed
  above; estimate unchanged (~a week).
- **Q2: DONE** (with Q1; landed in `dobrushinGA`, the finite classical tier's action —
  even better than the planned `lipGA` for the story).
- **Q3: DONE** (`QuantumDobrushinConsistency.lean`, axiom-clean): `Dist.toMState`
  (diagonal embedding), `trDistance_toMState` (trace distance on diagonals = classical
  `tvd`, via the Jordan trace-norm lemma + `cfc_diagonal`), `Kernel.toQChannel`
  (classical channel as diagonal-output PTP map), `toMState_push` (intertwining), and
  `classical_contraction_via_quantum` (`tvd (K.push μ) (K.push ν) ≤ tvd μ ν` as a
  corollary of the quantum DPI). Honest scope note: the quantum corollary transports the
  η = 1 *contraction*; the pairwise-row-η coefficient refinement stays with its
  classical proof (Tier 3) — quantifying `QDobrushinBound` over all states, including
  non-diagonal ones, would need measurement-contraction machinery the corollary doesn't
  buy. The tower is complete: finite ↪ measure (Tier 3c) and finite ↪ quantum (this),
  all machine-checked to agree.
- **Q4: research pass DONE (verdict at research-pass rigor, not formalized).** Against
  Hirche–Rouzé–Stilck França (arXiv 2202.10717, IEEE TIT 2023): quantum (ε,δ)-DP *is*
  the hockey-stick condition `sup_{ρ∼σ} E_{e^ε}(𝒜ρ‖𝒜σ) ≤ δ` — same shape as classical.
  But the classical two-row dichotomy does **not** simply replay: their parallel
  composition needs *product-input structure*, their sequential bound (Prop III.4) is a
  **product of channel contraction coefficients** — literally the Tier-4 Dobrushin
  certificate accumulation — and **no general adaptive/advanced composition theorem is
  proven**; no cleanly-tensorizing quantum PLD/f-DP analogue appears. Two readings, both
  recorded per the plan's no-pre-commitment: (a) the composable invariant exists but
  hasn't been found — a literature gap, classical-pattern intact; (b) quantum adaptive
  composition with adversarial entanglement is a **genuine boundary phenomenon** for the
  interface — a composite whose certificate is not a function of component certificates
  alone. Deciding between them requires reading their §V (Rényi) composition properties
  and the 2512.16778 non-linear SDPI line; deliberately left open. Either way the
  connection is real: their layered composition mechanism IS `comp_reconstructs_quantum_dobrushin`.
- **Q5: decision — upstream the DPI core to Physlib.** The five declarations
  `abs_eq_sup_add_sup`, `traceNorm_eq_trace_posPart_add_trace_negPart`,
  `traceNorm_eq_re_trace_of_posSemidef`, `traceNorm_map_le`, `trDistance_apply_le` have
  **zero TransportKernel dependencies** — pure Physlib+mathlib — and fill Physlib's
  stated trace-distance gap. Plan: PR them (likely as
  `QuantumInfo/States/Mixed/TraceDistance` additions or a new
  `Channels/TraceDistanceContraction.lean`, module-system headers, PTP-generality
  statement), keeping the Bridge reception in-repo. Opening the PR is a user-account
  action; the declarations are PR-shaped as they stand.

Build note for Q1 session-planning: `lake exe cache get` covers the *mathlib*
dependency only; Physlib's own ~84 QuantumInfo modules compile locally (budget the
first-build time, or check Reservoir for a package cache before starting).

Scoping note, kept honest: quantum enters the transport line here and only here —
channel contraction fits the interface as-is; it does not touch dip-schedulability.
