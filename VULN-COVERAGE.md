# Vulnerability coverage map — what "bulletproof" means here, exactly

The program's original goal is a framework for coding that is *inherently* free of
vulnerabilities. This document is the honest form of that claim: a map from real
vulnerability classes to the framework's property classes, with a **verdict per class**,
each verdict carrying its model, its assumptions, and its rigor grade. The map is the
first brick of the path from the proved meta-theory (`conf-typing/`,
`transport-calculus/`) back to the goal; its job is to convert "bulletproof" from a
slogan into a claim with a proved boundary.

Rigor grades, house style: **[proved]** — a Lean theorem is cited by name;
**[argued]** — derived in prose from proved parts; **[classified]** — taxonomic
placement only, no new mathematics; **[to prove]** — precise statement given,
scheduled (no row currently carries it).

## 0. The claim template — and its three irreducible gaps

The only honest form of "no vulnerabilities" is:

> Programs certified in this framework exhibit **no vulnerability of class X** —
> for each class X marked IN below — **relative to** the semantic model `M`, the
> stated policy/spec, and the trusted computing base; and the exclusion **survives
> composition** (the conformance gate `confidential_transport`, and `Bridge.comp`
> certificate accumulation).

Three gaps are irreducible and are *named*, not hidden:

- **Model gap.** A proof excludes leaks through channels *in* the model. The
  instrumented IMP semantics carries store, cost, and branch-trace outcomes
  (`Outcome := Store × Nat × List Bool`), so timing is inside; microarchitectural
  state is not. The recipe for growing coverage is the timing instance itself:
  put the channel in the semantics, then the same NI machinery applies.
- **Spec gap.** A proved release bound (`ReleasesAtMost`) is relative to the
  *declared* release `φ`; a wrong policy is proved-correct wrongness. The framework
  makes the declaration explicit and falsifiable (`result_full_not_bounded_by_bit`)
  — it cannot make it wise.
- **TCB.** Lean's kernel and the three standard axioms (`propext`,
  `Classical.choice`, `Quot.sound` — the central meta-theorems use none), plus
  compilation and hardware below the model. Nothing here shrinks that; it is stated.

## 1. The classification machinery (already proved — the map applies it)

The repo already contains the classifier; this map is its application:

| engine | Lean name | what it decides |
|---|---|---|
| admissibility test | `simA3_iff_respectsCoarsening` | a k-safety property is admissible ⟺ an up-set of the kernel-coarsening order Πₖ |
| 2-safety uniqueness | `qualitative_admissible_is_JNI` | among admissible properties the only nondegenerate 2-safety one is noninterference |
| kernel determination | `A3_factors_kernel`, `no_irreducible_admissible` | admissible properties depend only on pairwise-equality patterns — no genuinely k-ary atoms |
| region 2 inhabitant | `ksafety_above_twosafety` | proper k-safety (k>2) is inhabited above `J_NI` |
| separability boundary | `Rbad_nonseparable` | separable ⊊ 2-safety; per-channel reasoning is a theorem for `J_NI`, not a given |
| composability test | `summary_not_composable` | a certificate is composable iff it admits a `mul`; lossy summaries provably need not |
| the seam theorem | `confidential_transport`, `Bridge.comp` | guarantees survive the artifact→deploy gate and component composition, by construction |

The three property regions (conf-typing `TwoSafety.lean`): **(1)** admissible
2-safety = `J_NI`; **(2)** admissible k-safety, k>2 = up-sets of Πₖ over the 2-ary
atom basis; **(3)** genuine hyperproperties (`J_ε`-like; need distributions — the one
region behind the probabilistic layer, not yet mechanized).

Note the classifier is **role-agnostic**: `lowEq`, `J_NI`, `J_rel`, and all of §10 are
parametric in the partition `P` and observation `o`. Nothing hard-codes
"confidentiality"; relabeling the partition (High := untrusted) and pointing `o` at
trusted sinks yields integrity noninterference from the same theorems. The map uses
this repeatedly.

## 2. The verdict rubric

- **IN** — excluded by construction; end-to-end proved in the current model.
- **IN-WITH-MODEL** — excluded once the leak channel is in the semantics; proved for
  the channels currently modeled, with the extension recipe named.
- **REDUCIBLE** — excluded given a named reduction or assumption; the reduction is
  stated precisely (and proved where marked).
- **CARRIED** — the framework *transports* the class's certificate across
  composition seams but does not *generate* it; generation is an external engine.
- **LEDGER** — the class is assumption-shaped, not proof-shaped; the framework's
  contribution is that assumptions accumulate explicitly and never silently become
  evidence (`attest_is_not_J_evidence`).
- **OUT-INADMISSIBLE** — the popular formulation of the class fails admissibility
  (A2/A3), as a theorem; the framework *forces* a reformulation.
- **OUT-OF-MODEL** — the class's channel or execution structure is outside the
  current semantics; the needed model extension is named.
- **OUT-NONCOMPOSABLE** — the class's popular *summary* admits no `mul`, as a
  theorem; the composable invariant underneath is named.

## 3. The map

| # | class (CWE anchor) | semantic form | region | verdict | grade |
|---|---|---|---|---|---|
| 1 | direct confidentiality leaks (CWE-200) | 2-safety (NI) | 1 | IN | [proved] |
| 2 | timing side channels (CWE-208) | 2-safety over instrumented semantics | 1 | IN-WITH-MODEL | [proved] |
| 3 | injection: SQLi/XSS/command (CWE-89/79/78) | taint = integrity NI; blacklist = value predicate | 1 / — | IN as flow; OUT-INADMISSIBLE as blacklist | [proved: T1, T2] |
| 4 | improper declassification / overshare | bounded release (2-safety rel. φ) | 1 | IN | [proved] |
| 5 | privacy / differential privacy | hyperproperty (quantitative) | 3 | IN as f-DP invariant; OUT-NONCOMPOSABLE as (ε,δ) | [argued] / [proved in miniature] |
| 6 | memory safety (CWE-119/416) | 1-safety of a richer semantics | — | CARRIED (+ OUT-OF-MODEL for IMP) | [classified] |
| 7 | authz bypass (CWE-285); cross-tenant isolation | 1-safety rel. policy; isolation is 2-safety | — / 1 | CARRIED; isolation IN | [classified] / [argued] |
| 8 | races / TOCTOU (CWE-362/367) | 1-safety over interleavings | — | OUT-OF-MODEL | [classified] |
| 9 | speculative execution (Spectre-class) | 2-safety over microarchitectural model | 1* | OUT-OF-MODEL | [classified] |
| 10 | resource exhaustion / DoS (CWE-400) | quantitative safety bound | — | REDUCIBLE (graded certificate) | [classified] |
| 11 | crypto misuse (CWE-327) | assumption-shaped; leakage side is #2 | — | LEDGER | [classified] |
| 12 | composition seams / supply chain | certificate loss at boundaries | — | IN-BY-DESIGN | [proved, end-to-end] |

### 3.1 Direct confidentiality leaks — IN [proved]

Home turf. `J_NI` at partition `P` and adversary capability set; per-channel reasoning
legitimate by `JNI_separable`, joint completeness by `completeness_thm2`, and the
end-to-end witness is `pleak_confidential_deploy`: the *running* `P_leak` leaks at most
the declared bit on `result`, against the local adversary, through the deploy gate.
Model: instrumented IMP; adversary = subset of `𝒪` closed under post-processing and
tupling. This row is the exemplar all others are measured against.

### 3.2 Timing side channels — IN-WITH-MODEL [proved]

The `wall` observation (accumulated cost) is *in the outcome*, so timing NI is just
`J_NI` at a capability set containing `wall` — the local-adversary rows of the Pleak
development. The verdict is conditional in exactly one place: coverage extends to a
channel iff the channel is in the semantics. That is not a weakness to paper over; it
is the recipe (see #9 for its limit).

### 3.3 Injection — IN as taint-flow [proved: T1]; OUT-INADMISSIBLE as blacklist [proved: T2]

The industry's two formulations, separated by a theorem each
(`conf-typing/ConfTyping/Integrity.lean`, built, `no sorry`, axiom-audited):

- **T1 (taint duality) [proved].** Integrity noninterference — untrusted sources
  cannot influence trusted sinks — *is* `J_NI` at the relabeled partition
  (High := untrusted) with `o` = the trusted-sink observation: `taint_is_JNI` is an
  axiom-free `Iff.rfl`, and A3/separability transfer verbatim (`Jtaint_postproc`,
  `Jtaint_separable`, axiom-free). The uniqueness half (`admissible_taint_is_Jtaint`,
  standard axioms): any admissible, nondegenerate, inhabited 2-safety integrity
  judgment coincides with `J_taint` — **the taint form of injection-freedom is the
  unique admissible 2-safety formulation**. Sanitizers are the Policy stratum's dual:
  `InfluencedAtMost` is definitionally `ReleasesAtMost` at the relabeling, the const
  sanitizer is full taint-freedom (`sanitize_const_is_taint`), and the obligation has
  teeth both ways (`pleak_influenced_at_most_bit`, `full_flow_defeats_sanitizer`).
- **T2 (blacklist inadmissibility) [proved, axiom-free].** The formulation "output
  never contains the bad value" is a value predicate, and *no* nontrivial
  value-predicate judgment satisfies A3 (`value_predicate_not_admissible`): one
  post-processor — an encoder — breaks any of them. The concrete instance
  (`blacklist_not_admissible`) holds of a real channel and dies to the constant
  re-encoder. The security reading is the field's folklore as a theorem:
  **blacklist sanitization dies to encodings**, so the framework *forces* the flow
  formulation. This is the map's clearest example of the framework rejecting a
  popular-but-wrong property shape rather than failing to express it.

Scope honesty: IMP has no strings; row 3's [proved] is the property *shape*
(influence of untrusted sources on trusted sinks, with endorsement obligations),
made non-vacuous by the `P_leak` witnesses — not a model of SQL.

### 3.4 Improper declassification — IN [proved]

The Policy stratum: a discharge requires a declared release `φ` *plus* a proof
`ReleasesAtMost c o P φ`; Closure is the `φ = const` special case as a theorem
(`closure_is_const_policy`), the bound has teeth (`result_full_not_bounded_by_bit`),
and both strata transport through the gate (`confidential_transport`). The spec gap
lives here and is named: the framework proves "at most φ", not "φ was the right thing
to release."

### 3.5 Privacy / DP — IN as the f-DP invariant [argued]; OUT-NONCOMPOSABLE as (ε,δ) [proved in miniature]

Region 3: needs distributions, and the probabilistic layer is honestly not mechanized
(conf-typing's residue: `J_ε`). What *is* settled is the composition half, and it is
the map's sharpest negative verdict: `(ε,δ)` is a lossy projection admitting no `mul`
(`summary_not_composable` — two mechanisms with equal `(ε,δ)` compose to different
`(ε',δ')`), while the trade-off function / privacy-loss distribution is a composable
invariant (Dong–Roth–Su; advanced composition factors through it). The framework's
rule "when a summary does not compose, don't summarize" is the DP literature's own
conclusion, derived from the interface.

### 3.6 Memory safety — CARRIED [classified]

A 1-safety property of a semantics with a heap; IMP has none, so for this model it is
also OUT-OF-MODEL. The framework's honest contribution is transport, not generation:
"no undefined behavior relative to model M" is a Boolean certificate with trivial
`mul` (conjunction), so it rides `Bridge.comp` and the assumption ledger across
composition seams. Generating it is an ownership/separation-logic engine's job —
external, and *not* claimed. Carrying a certificate is plumbing, not memory safety.

### 3.7 Authz — CARRIED [classified]; cross-tenant isolation — IN [argued]

"All accesses mediated per policy π" is 1-safety relative to π: transportable,
accumulable, spec-gap-heavy (π's correctness is not a theorem anywhere). But the
economically load-bearing sub-case is better than that: **cross-tenant data
isolation — tenant A's response is independent of tenant B's data — is literally
noninterference** at the partition "other tenants' data := High", i.e. region 1, the
proved machinery. The reduction is the T1 relabeling pattern, and T1 proved that
pattern costs nothing (`taint_is_JNI` is an `Iff.rfl` — the apparatus is
`(P, o)`-parametric). [argued] remains only for want of a mechanized multi-tenant
instance; no new mathematics is missing.

### 3.8 Races / TOCTOU — OUT-OF-MODEL [classified]

The current semantics is sequential and deterministic, and determinism is
load-bearing: `conform_refl` (the gate's reflexivity) discharges through Sem-Det.
Adding interleavings is therefore not an add-on — it revisits the conformance
relation itself. Named extension: a nondeterministic small-step semantics with
demonic scheduling, `≅` rebuilt over trace sets. Until then this class is excluded
from the claim, explicitly.

### 3.9 Speculative execution — OUT-OF-MODEL [classified]

The channel is microarchitectural state; the property shape is timing-NI over a
speculative semantics (region 1 *in principle* — hence the asterisk in the table).
The recipe of #2 applies but the model is research-scale (speculation, caches,
predictors). The map's role is to keep the claim honest: nothing in this repo
excludes Spectre, and no verdict pretends otherwise.

### 3.10 Resource exhaustion — REDUCIBLE [classified]

The cost counter is already in the outcome, so "cost ≤ f(input)" is a safety-shaped
quantitative bound — a *graded certificate* in the transport sense (a monotone bound
on the distance/cost effect: `Bridge.ofModulus` territory), and bounds compose by
accumulation. Liveness-shaped availability ("eventually responds") is not expressible
and not claimed. Generation (amortized cost analysis) is external; the reduction of
the class to certificates over the instrumented model is the claim.

### 3.11 Crypto misuse — LEDGER [classified]

"IND-CPA holds for X" is an assumption, not a theorem of any program logic. The
framework's contribution is the discipline proved in miniature by
`attest_is_not_J_evidence`: attestations and assumptions coexist with obligations
but never silently discharge them, and composition accumulates them into a visible
ledger. The *leakage* side of crypto misuse (non-constant-time implementations) is
row #2 and inherits its IN-WITH-MODEL verdict.

### 3.12 Composition seams / supply chain — IN-BY-DESIGN [proved, end-to-end]

The differentiator, now proved at every level (brick 2, `conf-typing/ConfTyping/
Compose.lean` + `FlowBridge.lean`, both built, `no sorry`, axiom-audited):

- **The seam theorems** (`Compose.lean`): components carry *boundary certificates*
  — which are exactly channel claims (`boundaryNI_iff_resultNI`) — and certified
  components compose with the composite certificate *computed*: Closure form
  (`boundaryNI_seq`, `resultNI_seq` — axiom-free), total form (`outNI_seq` — Low
  store, cost, and branch trace jointly), all derivable channels
  (`seq_all_channels` — the seam adds no new obligations), integrity reading
  (`taint_result_seq`), and the headline Policy form (`releases_seq` —
  **axiom-free**): the composite releases at most `seqRelease c₁ φ₁ φ₂ =
  ⟨φ₁, φ₂ ∘ boundary⟩`, a non-scalar semidirect certificate algebra.
  Non-vacuity: `pleak_chain_releases`, a concrete certified seam.
- **The reception** (`FlowBridge.lean`): certified components live in the *same*
  `GradedAction` interface as Lipschitz/Hölder/Dobrushin/quantum — distance = the
  query distance `qd`, certificates = monotone transforms of it, and the reception
  is an *equivalence* (`bridge_iff_releases`): a `leakBound`-certified Bridge
  exists iff `BoundaryReleases`. The generic `Bridge.comp` **reconstructs the seam
  theorem** (`comp_reconstructs_seq_release`): its computed certificate is
  dominated by the seam certificate, with no security-specific reasoning.
- **The teeth** (both directions): `broken_seam` — an uncertified upstream poisons
  a perfectly certified downstream (the upstream hypothesis is load-bearing);
  `channel_certs_do_not_compose` — a wall-certificate is not a boundary
  certificate, and only boundary certificates compose (the granularity is forced).
- **The gate**: `confidential_transport` carries both strata across
  artifact→deploy, as before.

Still conditional in exactly one honest place: *if* each component carries a
certificate, composition preserves and accumulates it; generating per-component
certificates is the other rows' business. The assumption-*ledger* certificate
(composite TCB computed as the append of component ledgers) is deferred to the
next brick, where a real component vocabulary exists to name assumptions in.

## 4. What the map implies for brick 2

The IN column is: information flow (confidentiality, timing, taint,
declassification, isolation) + quantitative bounds + the composition seam. The
CARRIED/LEDGER rows show the framework acting as a *certificate bus*, not a universal
verifier. With T1/T2 landed as predicted, the fork is settled: the honest product
identity is **a certified composition framework — vulnerability classes excluded by
flow properties, everything else carried as explicit accumulated assumptions** — and
brick 2 targets *component boundaries* (the seam story, where the differentiator is
proved: `Bridge.comp` + `confidential_transport` + the T1 relabeling for per-boundary
partitions), not a general-purpose language frontend.

## 5. Session ledger

- **Session 1 (this document):** all twelve classifications placed; engine table;
  claim template with the three gaps; rubric. Grades as marked.
- **Session 2 (done):** T1 and T2 landed in `conf-typing/ConfTyping/Integrity.lean`
  (mathlib-free, `no sorry`). Axiom audit: `taint_is_JNI`, `Jtaint_postproc`,
  `Jtaint_separable`, `sanitize_const_is_taint`, `value_predicate_not_admissible`,
  `blacklist_not_admissible` — **no axioms**; `admissible_taint_is_Jtaint` and the
  two `P_leak` endorsement witnesses — the standard three. The predicted
  "near-instantiation" held exactly: T1's identity is an `Iff.rfl`. Row 3 upgraded
  to [proved].
- **Session 3 (done):** [argued] rows re-audited — row 7's isolation note now rests
  on the *proved* relabeling pattern (only a mechanized multi-tenant instance is
  wanting); rows 5, 6, 8–11 unchanged by T1/T2, as expected. `tools/check-claims.sh`
  extended with two guards: every Lean name the map cites must exist in the sources
  (1c), and row 3's [proved] is only valid while T1/T2 are present and imported
  (1d). §4's fork recorded as settled: brick 2 = component boundaries. **Brick 1
  complete.**

### Brick 2 ledger (the seam)

- **Session 1:** `Compose.lean` — writer decomposition (`rfl`), boundary
  certificates = channel claims, seam theorems in Closure/total/Policy forms;
  `releases_seq` axiom-free with the semidirect `seqRelease`.
- **Session 2:** `FlowBridge.lean` — the reception into the transport interface
  (`conf-typing` now path-depends on `transport-calculus`, both mathlib-free);
  `bridge_iff_releases` (an equivalence), `comp_reconstructs_seq_release` (the
  generic composition law recomputes the seam certificate). Lossiness recorded:
  abstraction bridges alone compose trivially — ship the boundary abstraction,
  not just the budget.
- **Session 3:** the negative space (`broken_seam`,
  `channel_certs_do_not_compose`, `pleak_not_boundaryNI`) — both seam hypotheses
  proved load-bearing; row 12 upgraded to end-to-end [proved]; guards extended
  (1c names, 1e row-12). Deferred, named: the assumption-ledger certificate; a
  mechanized multi-tenant isolation instance (row 7). **Brick 2 complete.**
