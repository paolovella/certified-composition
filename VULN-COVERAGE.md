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
  evidence (`attest_is_not_J_evidence`, and — brick 4 — the composable
  `CondBoundary` ledger with `ledger_no_silent_discharge`).
- **OUT-INADMISSIBLE** — the popular formulation of the class fails admissibility
  (A2/A3), as a theorem; the framework *forces* a reformulation.
- **OUT-OF-MODEL** — the class's channel or execution structure is outside the
  current semantics; the needed model extension is named.
- **OUT-NONCOMPOSABLE** — the class's popular *summary* admits no `mul`, as a
  theorem; the composable invariant underneath is named.

The **(generated)** annotation (brick 3) marks an IN verdict whose certificate is
now *manufactured by a syntactic checker* (`conf-typing/ConfTyping/SecTy.lean`,
`SecTyD.lean`), not proved by hand per component: `secCheck`/`secCheckD` return a
Boolean, and soundness turns a passing check into the semantic certificate — so a
concrete component earns its verdict by `decide`, and the certificate flows through
the seam theorems and Bridge reception untouched. Without the annotation, an IN
verdict is proved semantically but per-component by hand.

## 3. The map

| # | class (CWE anchor) | semantic form | region | verdict | grade |
|---|---|---|---|---|---|
| 1 | direct confidentiality leaks (CWE-200) | 2-safety (NI) | 1 | IN (generated) | [proved] |
| 2 | timing side channels (CWE-208) | 2-safety over instrumented semantics | 1 | IN-WITH-MODEL (generated) | [proved] |
| 3 | injection: SQLi/XSS/command (CWE-89/79/78) | taint = integrity NI; blacklist = value predicate | 1 / — | IN as flow (generated); OUT-INADMISSIBLE as blacklist | [proved: T1, T2] |
| 4 | improper declassification / overshare | bounded release (2-safety rel. φ) | 1 | IN (generated) | [proved] |
| 5 | privacy / differential privacy | hyperproperty (quantitative) | 3 | IN as f-DP invariant; OUT-NONCOMPOSABLE as (ε,δ) | [argued] / [proved in miniature] |
| 6 | memory safety (CWE-119/416) | 1-safety of a richer semantics | — | CARRIED (+ OUT-OF-MODEL for IMP) | [classified] |
| 7 | authz bypass (CWE-285); cross-tenant isolation | 1-safety rel. policy; isolation is 2-safety | — / 1 | CARRIED; isolation IN (generated) | [classified] / [proved] |
| 8 | races / TOCTOU (CWE-362/367) | 1-safety over interleavings | — | OUT-OF-MODEL | [classified] |
| 9 | speculative execution (Spectre-class) | 2-safety over microarchitectural model | 1* | OUT-OF-MODEL | [classified] |
| 10 | resource exhaustion / DoS (CWE-400) | quantitative safety bound | — | REDUCIBLE (graded certificate) | [classified] |
| 11 | crypto misuse (CWE-327) | assumption-shaped; leakage side is #2 | — | LEDGER (mechanized) | [proved] |
| 12 | composition seams / supply chain | certificate loss at boundaries | — | IN-BY-DESIGN | [proved, end-to-end] |

### 3.1 Direct confidentiality leaks — IN, generated [proved]

Home turf. `J_NI` at partition `P` and adversary capability set; per-channel reasoning
legitimate by `JNI_separable`, joint completeness by `completeness_thm2`, and the
end-to-end witness is `pleak_confidential_deploy`: the *running* `P_leak` leaks at most
the declared bit on `result`, against the local adversary, through the deploy gate.
Model: instrumented IMP; adversary = subset of `𝒪` closed under post-processing and
tupling. This row is the exemplar all others are measured against. **Generated** (brick
3): the store-boundary certificate is now checker output — `secCheck P false c = true`
yields `BoundaryNI c P` (`boundaryNI_of_check`), so a component earns this row by
`decide` (`pok_certified`). The honesty theorem `typed_but_wall_leaks` marks the
boundary: the checker certifies the store channel, not the timing channel (row 2).

### 3.2 Timing side channels — IN-WITH-MODEL, generated [proved]

The `wall` observation (accumulated cost) is *in the outcome*, so timing NI is just
`J_NI` at a capability set containing `wall` — the local-adversary rows of the Pleak
development. The verdict is conditional in exactly one place: coverage extends to a
channel iff the channel is in the semantics. That is not a weakness to paper over; it
is the recipe (see #9 for its limit). **Generated** (brick 5,
`conf-typing/ConfTyping/SecTyT.lean`): a *timing-sensitive* checker `secCheckT`
forbids High-guarded branches and certifies the **whole instrumented outcome** —
store, running time, and branch trace jointly (`secTyT_sound`, `outNI_of_checkT`:
`J_NI c (outO P) P` by `decide`). It refines the store checker
(`secCheckT_imp_secCheck`) and rejects the brick-3 leak witness `Ptime`
(`ptime_rejected_T`) — the program `typed_but_wall_leaks` proved leaks the clock.
So `secCheck` and `secCheckT` bracket the channel: store-safe vs. store-and-clock-
safe. Honest scope: this certifies timing-*insensitivity* (secret-dependent
branching is rejected, not repaired); declassified timing (a High branch whose
duration is declared released) is the Policy-stratum analogue, a later brick.

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
made non-vacuous by the `P_leak` witnesses — not a model of SQL. **Generated** (brick
3): since taint-freedom is `J_NI` at the untrusted relabeling and the checker
generates `J_NI`, the taint certificate is checker output at the relabeled partition
— the same `secCheck` under `P := untrusted`.

### 3.4 Improper declassification — IN, generated [proved]

The Policy stratum: a discharge requires a declared release `φ` *plus* a proof
`ReleasesAtMost c o P φ`; Closure is the `φ = const` special case as a theorem
(`closure_is_const_policy`), the bound has teeth (`result_full_not_bounded_by_bit`),
and both strata transport through the gate (`confidential_transport`). The spec gap
lives here and is named: the framework proves "at most φ", not "φ was the right thing
to release." **Generated** (brick 3, `SecTyD.lean`): the release is now *computed
from syntax* — a declared-permit checker (`secCheckD`) whose derivation yields the
ledger `relOf P c`, with `boundaryReleases_of_check` turning a passing check into the
bound. `checker_rederives_pleak_bound` reproduces the hand-proved Paper-1 bound
(`result_releases_at_most_bit`) from `decide` + soundness, choice-free — a *smaller*
axiom footprint than the original. Declaration is disclosure, not bypass: an
undeclared High flow is rejected (`pfull_rejected_undeclared`), and a declared one
appears in the ledger as a visible line item (`pfull_ledger`).

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

### 3.7 Authz — CARRIED [classified]; cross-tenant isolation — IN, generated [proved]

"All accesses mediated per policy π" is 1-safety relative to π: transportable,
accumulable, spec-gap-heavy (π's correctness is not a theorem anywhere). But the
economically load-bearing sub-case is better than that: **cross-tenant data
isolation — tenant A's response is independent of tenant B's data — is literally
noninterference** at the partition "other tenants' data := High", i.e. region 1, the
proved machinery. Now mechanized (brick 3, `Pipeline.lean`): a multiplexing
component is checked against each tenant's partition and proved isolated both ways
(`multiplex_isolates_A/B` — `J_NI` from a `decide`), the isolation survives
composition (`multiplex_pipeline_isolates_B`), and a cross-tenant leak is caught by
the checker *and* proved non-isolated (`leaky_rejected`, `leaky_not_isolated`). The
[argued] gap ("no mechanized instance") is closed; the isolation verdict is now
[proved] and generated. Authz-in-general stays CARRIED (π's correctness is the
spec gap, not a theorem).

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

### 3.11 Crypto misuse — LEDGER, mechanized [proved]

"IND-CPA holds for X" is an assumption, not a theorem of any program logic — so the
right verdict is never "proved secure" but "proved to *track the assumption
honestly*." Brick 4 (`conf-typing/ConfTyping/Ledger.lean`, `LedgerBridge.lean`,
`SupplyChain.lean`, all built, `no sorry`, axiom-audited) mechanizes exactly that:

- a **composable ledger** — a component's trusted base `Γ : List Prop` and a
  conditional certificate `CondBoundary c P Γ := Sat Γ → BoundaryNI c P`;
- **accumulation by the same law** — `condBoundary_seq` unions the bases, and
  `ledgerGA`/`ledgerBridge_comp_ledger` ride the ledger on `Bridge.comp` as a
  phantom grade, so the trusted base of a composed guarantee is *computed* (the
  SBOM as a theorem);
- **no silent discharge** — `ledger_no_silent_discharge` / `biz_needs_assumption`:
  a component whose security rests on an assumption cannot be certified with it
  dropped (the composition-level `attest_is_not_J_evidence`);
- **checker-generated** — `condBoundary_of_check_assuming`: checking a component
  under a declared trust assumption emits the conditional certificate directly, and
  the worked pipeline `supply_chain_ledger` carries exactly its one external
  assumption, dischargeable when the dependency is later verified.

Scope, honest: the external assumption ("the cipher/library is correct") *stays* an
assumption — mechanizing the LEDGER discipline is proving it is tracked, unioned,
and never laundered into evidence, not proving the crypto. The *leakage* side of
crypto misuse (non-constant-time implementations) is row #2 and inherits its
IN-WITH-MODEL verdict.

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
(composite trusted base computed as the append of component ledgers) — deferred here
in brick 2 — is **delivered in brick 4** (`Ledger.lean`, `LedgerBridge.lean`):
`CondBoundary`/`CondReleases` carry the base, `condBoundary_seq` and
`ledgerBridge_comp_ledger` accumulate it by the same composition law, and
`ledger_no_silent_discharge` proves it can never be laundered into evidence. See
row 11.

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

### Brick 3 ledger (the checker — certificates from syntax)

- **Session 1:** `SecTy.lean` — a syntax-directed flow type system whose
  derivations manufacture the boundary certificates. Confinement (axiom-free),
  soundness `secTy_boundaryNI` (choice-free), executable `secCheck`, certificates
  by `decide` (`boundaryNI_of_check`, `pok_certified`). Non-vacuity both ways:
  `pleak_rejected` (the checker rejects `P_leak`, matching the brick-2 semantic
  fact). Honesty theorem `typed_but_wall_leaks`: the checker certifies the store
  boundary, not the timing channel.
- **Session 2:** `SecTyD.lean` — declared releases and the computed ledger
  `relOf`, which composes by the brick-2 certificate algebra definitionally
  (`relOf_seq` is `rfl`). Soundness `secTyD_sound` (choice-free); the money
  theorem `checker_rederives_pleak_bound` reproduces the hand-proved Paper-1 bound
  from `decide`, with a *smaller* axiom footprint. Declaration is disclosure, not
  bypass (`pfull_rejected_undeclared`, `pfull_ledger`).
- **Session 3:** `Pipeline.lean` — multi-tenant isolation checked both ways
  (`multiplex_isolates_A/B`, with teeth: `leaky_rejected`/`leaky_not_isolated`),
  closing row 7 to [proved]/generated; and the pipeline theorem
  (`certified_pipeline`, `certified_pipeline_bridge`,
  `certified_pipeline_reconstruction`, `demo_pipeline`): two syntactic checks
  compose into one certified Bridge in the transport interface, the generic
  `Bridge.comp` reconstructing the seam certificate. Rows 1, 3, 4, 7 annotated
  **(generated)**; guard 1c extended, guard 1f added for the pipeline theorems.
  Still deferred, named: the **assumption/TCB ledger** (brick 4). **Brick 3
  complete.**

### Brick 4 ledger (the trusted base)

- **Session 1:** `Ledger.lean` — the trusted base as a composable certificate.
  `CondBoundary c P Γ := Sat Γ → BoundaryNI c P`; accumulation by union
  (`condBoundary_seq`, choice-free); explicit discharge (`condBoundary_nil`,
  `condBoundary_discharge`, axiom-free); no silent discharge
  (`ledger_no_silent_discharge` — a used assumption cannot be dropped, the
  composition-level `attest_is_not_J_evidence`).
- **Session 2:** `LedgerBridge.lean` — the ledger rides `Bridge.comp` as a phantom
  grade (`ledgerGA`, axiom-free; `ledgerBridge_comp_ledger` is `rfl`), so
  provenance accumulates by the same law as the guarantee. The SBOM as a theorem
  (`ledger_supply_chain_ledger`/`_map`/`_bound`).
- **Session 3:** `SupplyChain.lean` — the checker emits conditional certificates
  from declared assumptions (`condBoundary_of_check_assuming`); a worked trust
  pipeline carrying exactly one external assumption (`supply_chain_ledger`),
  dischargeable (`supply_chain_discharged`) and load-bearing
  (`biz_needs_assumption`). Row 11 upgraded [classified] → [proved], the brick-2
  row-12 deferral closed, guard 1c extended, guard 1g added. **Brick 4 complete.**

### Brick 5 ledger (timing-sensitive certification)

- `SecTyT.lean` — the timing-sensitive checker. Brick 3's `typed_but_wall_leaks`
  honesty theorem is closed: `SecTyT` forbids High-guarded branches, and
  `secTyT_sound`/`outNI_of_checkT` (choice-free) certify the *whole* instrumented
  outcome — Low store, running time, branch trace — as Low-determined
  (`J_NI c (outO P) P`), by `decide`. It refines the store checker
  (`secCheckT_imp_secCheck`) and rejects the brick-3 leak witness `Ptime`
  (`ptime_rejected_T`, axiom-free). Row 2 (timing) upgraded to **(generated)**,
  guard 1c extended, guard 1h added. Honest scope: certifies
  timing-*insensitivity* (secret-dependent branching rejected, not repaired);
  declassified timing is a later brick. **Brick 5 complete.**

### The security program, standing state (five bricks)

The original goal — a framework for coding inherently free of vulnerabilities —
now has: a **map** with a proved boundary (12 classes, brick 1); a **seam** so
guarantees survive composition in the transport interface (brick 2); a **checker**
so the certificates come from a decidable syntactic check, not hand proof (brick
3); a **ledger** so the assumptions a guarantee rests on are tracked, unioned
under composition, and never silently laundered into evidence (brick 4); and a
**timing-sensitive checker** so the clock is a certified channel, not just an
honesty caveat (brick 5). What "bulletproof" means is stated at proved strength,
the flow-property classes are excluded *by type-checking* (store and clock),
composition is certificate accumulation by the same law that composes contraction
estimates, and every guarantee carries its trusted base as an automatic bill of
materials. The honest edges are all named as theorems or deferrals:
microarchitecture stays OUT-OF-MODEL, `(ε,δ)`-DP stays OUT-NONCOMPOSABLE,
memory-safety/authz stay CARRIED, declassified timing is deferred, and the
spec/model/TCB gaps of §0 are unmovable by construction.
