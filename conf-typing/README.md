# Confidentiality Typing — Lean 4 mechanization

A machine-checked encoding of **Paper 1: the IMP timing instance** of the
confidentiality-typing framework. Every result below is proved in Lean 4
(v4.31.0), mathlib-free, with **no `sorry`** and only the three standard
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`) — the
central meta-theorems use none of them.

```
lake build          # builds all four layers
```

## Layout

| File | Doc section | Content |
|---|---|---|
| `ConfTyping/Imp.lean`    | §1–2 | syntax, instrumented semantics (relation **and** evaluator), `determinism` (Sem-Det) |
| `ConfTyping/Obs.lean`    | §3–5 | observations, parametric `J`, `J_NI`, A3 + separability, adversaries, generation (Lemma 1) |
| `ConfTyping/Pleak.lean`  | §7   | the `P_leak` worked example: `wall` constant, `result`/`branch` leak |
| `ConfTyping/Typing.lean` | §6–9 | strata, discharge judgment, T-Reject, conformance + transport, soundness |
| `ConfTyping/Joint.lean`  | framework §4,§8 | joint generation `𝒜̂`, completeness (Thm. 2), separability-equivalence |
| `ConfTyping/TwoSafety.lean` | framework §10 | abstract 2-safety lift; A3-collapse; corrected §10 conjecture |
| `ConfTyping/Integrity.lean` | `VULN-COVERAGE.md` row 3 | taint duality (T1), endorsement dual, blacklist inadmissibility (T2) |
| `ConfTyping/Compose.lean` | `VULN-COVERAGE.md` row 12 | the seam theorems: boundary certificates compose, releases compose non-scalarly |
| `ConfTyping/FlowBridge.lean` | `VULN-COVERAGE.md` row 12 | the reception: certified components are Bridges in the transport interface; `Bridge.comp` reconstructs the seam (path-dep: `../transport-calculus`, mathlib-free) |
| `ConfTyping/SecTy.lean` | brick 3 | the checker: a flow type system whose derivations manufacture the boundary certificates; executable, sound, honest about timing |
| `ConfTyping/SecTyD.lean` | brick 3 | the Policy checker: declared releases, the computed ledger `relOf` (composes by `seqRelease`, `rfl`), the Paper-1 bound rederived by `decide` |
| `ConfTyping/Pipeline.lean` | brick 3 / `VULN-COVERAGE.md` row 7 | multi-tenant isolation (checked both ways), and the pipeline theorem: two syntactic checks → one certified composed Bridge |
| `ConfTyping/Ledger.lean` | brick 4 / `VULN-COVERAGE.md` rows 11–12 | the assumption ledger: conditional certificates that accumulate their trusted base under composition, and never silently discharge it |
| `ConfTyping/LedgerBridge.lean` | brick 4 / `VULN-COVERAGE.md` row 12 | the ledger rides `Bridge.comp` as a phantom grade — provenance accumulates by the same law as the guarantee (the SBOM as a theorem) |
| `ConfTyping/SupplyChain.lean` | brick 4 / `VULN-COVERAGE.md` row 11 | the checker emits conditional certificates from declared assumptions; a worked trust pipeline, dischargeable and load-bearing |
| `ConfTyping/SecTyT.lean` | brick 5 / `VULN-COVERAGE.md` row 2 | the timing-sensitive checker: forbids High-guarded branches, certifies the whole instrumented outcome (store, cost, trace) |

## Result map

| Lean name | Paper claim |
|---|---|
| `determinism` | (Sem-Det), via `eval`/`Step` equivalence |
| `JNI_postproc` | (A3) post-processing monotonicity for `J_NI` |
| `JNI_separable` | Def. 5 separability holds for `J_NI` (Prop. 2, NI side) |
| `gen_mono` | Lemma 1 (𝒜-monotonicity) |
| `wall_closure` | §7.2 — `wall` discharged at Closure |
| `result_not_closable` | §7.3 — Closure unavailable, Policy *forced* |
| `ReleasesAtMost` / `result_releases_at_most_bit` | §5/§7.3 — the **bounded** Policy obligation: `result` reveals at most the bit `(b≠0)` |
| `result_full_not_bounded_by_bit` | non-vacuity: a full-leak program *fails* the bound (the policy stratum has teeth) |
| `closure_is_const_policy` | framework §5 — Closure is the `φ=const` special case, as a *lemma* not a definitional collapse |
| `branch_not_closable` | §7.4 — residual obligation |
| `reject_Jinvariant` | **Lemma 3** — rejection holds for *every* `J` |
| `Conform` / `transport_JNI` | §6 conformance relation + the §9 gate (Closure half) |
| `transport_releases` | the gate transports the **Policy** half — a proven release bound carries to `deploy` |
| `confidential_transport` | full-strength gate: the *whole* `Confidential` claim (both strata) transports `A → deploy` |
| `pleak_confidential_deploy` | end-to-end: the *running* P_leak leaks at most the bit on `result` |
| `attest_is_not_J_evidence` | §6.1 sharpened — valid attestation coexists with false obligation |
| `soundness` | §9 Boolean soundness |
| `pleak_confidential_local` | §7 end-to-end: `P_leak` confidential vs local adversary, declassifying `result` |
| `branch_residual` | §7.4 — `branch` dischargeable at no stratum |
| `wall_rejection` | §7.5 — attesting a closable obligation is ill-typed |

## The joint layer (Hole 1, localized)

`Joint.lean` mechanizes `𝒜̂ = foldr tup seedObs` and proves, all over `J_NI`,
mathlib-free:

| implication | Lean | mechanism | J_NI | J_ε |
|---|---|---|:--:|:--:|
| joint ⇒ per-channel | `joint_to_perchannel` | projection = A3 | ✓ | ✓ |
| per-channel ⇒ joint | `perchannel_to_joint` | `JNI_separable` | ✓ | **✗** |
| joint ⇒ all post-proc | `completeness_rel_O` (engine) | A3 | ✓ | ✓ |
| primitive factors through join | `mem_is_postproc` (Prop. 1) | projection | ✓ | ✓ |
| joint ⇒ all **derivable** | `completeness_thm2` (Thm. 2) | engine + Prop. 1 | ✓ | ✓ |

`completeness_rel_O` is the *engine* ("every post-processing of the join is
`J_NI`", `∀ f`); Thm. 2 proper needs Prop. 1 (`mem_is_postproc`: real
adversary channels factor through the join) to close the quantifier over
derivable channels rather than all functions. `completeness_thm2` is the
honest statement.

The footprint *is* the story: completeness routes through `JNI_postproc` (A3)
alone — **it never uses the forward direction.** Per-channel generation is
*only* forward, and forward *is* separability (`perchannel_to_joint`, the lone
`JNI_separable` user). So "is per-channel generation sound?" = "is `J`
separable?": yes for `J_NI` (proved), no for `J_ε`.

For *why* the break needs mathlib, and the corrected §10 statement, see the
2-safety characterization below — the naive "separable = 2-safety" coincidence
is **false**, and the corrected version is the actual result.

## The 2-safety characterization — §10 conjecture corrected (`TwoSafety.lean`)

Lift `J` to a binary trace-relation: `J_rel R c o P := ∀ σ≈_Lσ'. R (o⟦c⟧σ)
(o⟦c⟧σ')`, with `J_NI` = `J_rel (·=·)` (`JNI_is_rel`, axiom-free `Iff.rfl`).
Two relation properties: `PairClosed` (congruence for `Val.pair`) and
`PostClosed` (= A3). Then:

| result | Lean | content |
|---|---|---|
| forward over the class | `rel_perchannel_to_joint` | `PairClosed` ⇒ separable |
| backward over the class | `rel_joint_to_perchannel` | `PostClosed` (A3) ⇒ complete |
| **A3 collapse** | `postclosed_collapse` | `PostClosed R` ⇒ `R` total **or** `R ⊆ Eq` |
| **corrected §10** | `qualitative_admissible_is_JNI` | A2 ∧ A3 ⇒ the only nondegenerate 2-safety `J` is `J_NI` |
| **the refutation** | `Rbad_nonseparable` | a deterministic 2-safety `R`, non-`PairClosed`, **non-separable** |
| **k-safety above 2** | `ksafety_above_twosafety` | `notAllDistinct`: admissible (A2∧A3), deterministic, ≠ `J_NI` |
| **k-ary foundation** | `A3_factors_kernel` | simultaneous A3 ⇒ property determined by the *pairwise-equality pattern* (all k) |
| **probe settled** | `no_irreducible_admissible` | no admissible property depends on genuinely k-ary structure |
| **Πₖ characterization** | `simA3_iff_respectsCoarsening` | admissible (sim-A3) ⟺ **up-set of the kernel-coarsening order** (all k) |

**§10's conjecture "separable ⟺ 2-safety" is false.** `Rbad` (equal first
component when both pairs, else blind to non-pairs) is a 2-safety property that
is not `PairClosed`, and `branchO` — non-pair-valued, leaking — gives two
channels each satisfying `J_rel Rbad` whose tuple does not. So **separability
is the congruence-refinement of 2-safety: `separable ⊊ 2-safety`**, no
randomness used.

**The corrected result.** `postclosed_collapse` shows A3 is brutal *at arity 2*
— preservation under *all* unary functions forces a binary `R` to be total or
sub-diagonal (relate one off-diagonal pair, a relabeling drags `R` to total).
A2 (non-triviality) deletes the total relation, reflexivity (A3 again) lifts
`⊆ Eq` to `Eq`. Net (`qualitative_admissible_is_JNI`): **among admissible J, the
only nondegenerate _2-safety_ property is `J_NI`.**

**But this stops at arity 2 — the k-safety hierarchy lives strictly above it.**
A3 is *simultaneous* (one post-processor on the whole observation), and a
function can only *coarsen* a tuple's equality-pattern, never refine it — so A3
closes a property upward to the diagonal but is blind downward, and at arity ≥ 3
that gap is real. `notAllDistinct` (the canonical 3-safety-not-2-safety shape)
is admissible (A2 ∧ A3, `notAllDistinct_postclosed` axiom-free), deterministic,
and satisfied by `branchO` — which `J_NI` rejects. So `ksafety_above_twosafety`
witnesses **admissible 2-safety = `J_NI` ⊊ admissible k-safety (k>2)**, all
qualitative and mathlib-free.

**Three nested regions, not two:**

1. **admissible 2-safety = `J_NI`** (separable) — proved.
2. **proper k-safety, k > 2** (e.g. `notAllDistinct`) — deterministic,
   qualitative, mathlib-free; shown *inhabited* (one witness; not fully
   characterized).
3. **genuine hyperproperties** (not k-safety for any k) = `J_ε` — needs a
   distribution; the *only* region behind the mathlib wall.

So the mathlib boundary is **not** the qualitative boundary and **not** the
2-safety boundary — it is the **k-safety / hyperproperty boundary**, strictly
above both. `postclosed_collapse`, `Rbad`, and `notAllDistinct` are all concrete
relation algebra over `Val`, no distribution. The §10 conjecture is **retired**
(corrected + proved at the 2-safety level), with only "region 3 is inhabited" (a
concrete admissible `J_ε`) deferred to the probabilistic layer.

**What region 2 actually is (the k-ary structure).** It is tempting to call
region 2 "a proper k-safety tower of irreducible properties." That is *wrong*,
and `A3_factors_kernel` proves why: a simultaneous-A3 property of a k-tuple
depends only on the tuple's **kernel** — the pairwise-equality pattern. (The
relabeling sending `x i ↦ x' i` is well-defined exactly when the kernels agree;
A3 transports `P` along it.) So **no admissible property has genuinely k-ary
atoms** (`no_irreducible_admissible`) — everything is a function of the 2-ary
predicates `o_i = o_j`. Yet region 2 is *not* a finite stub: the up-sets of the
partition lattice Πₖ grow with k (`o₁=o₂ ∧ o₃=o₄` is a real k=4 property absent
at k=3), and the k-safety *refutation degree* is unbounded ("at most m distinct
values" needs m+1 traces). So region 2 = **up-sets of Πₖ**: an infinite,
properly-growing, unbounded-refutation-degree family over a **fixed 2-ary atom
basis**. *Mechanized:* admissible ⟹ kernel-determined, all arities
(`A3_factors_kernel`); **the up-set characterization itself** —
`simA3_iff_respectsCoarsening`: a k-safety property is admissible *iff* it is
closed upward under kernel coarsening (an up-set of Πₖ), all k, mathlib-free;
and the k=3 inhabitant (`notAllDistinct`).

*Argued, with the cardinality condition now explicit:* the characterization is
up-sets of the order on **realizable** kernels. For value-rich `Val` (infinitely
many `.int`) every partition of `Fin k` is realizable, so the order is the full
Πₖ and the family grows with k; for a **Boolean-valued channel** only ≤2-block
kernels are realizable and region 2 collapses to a finite stub. So the growth
claim is *conditional on observation cardinality* — "realizable kernels = full
Πₖ" needs `Finset.min'`-style combinatorics that would pull in mathlib, so it
stays argued, the condition pinned rather than hidden. The iff has no such
dependence.

## The integrity/taint module (`Integrity.lean`) — VULN-COVERAGE row 3

The vulnerability coverage map's injection row, proved. The module's content is
that the integrity side costs *nothing*: the whole §3–§10 apparatus is
parametric in `(P, o)`, so relabeling the partition (High := untrusted) and
pointing `o` at trusted sinks turns confidentiality machinery into taint
machinery — identities and instantiations, not new proofs.

| result | Lean | axioms | content |
|---|---|---|---|
| **T1, identity** | `taint_is_JNI` | none (`Iff.rfl`) | integrity NI *is* `J_NI` at the source/sink relabeling |
| T1, inheritance | `Jtaint_postproc`, `Jtaint_separable` | none | A3 and separability transfer verbatim |
| **T1, uniqueness** | `admissible_taint_is_Jtaint` | standard 3 | admissible nondegenerate 2-safety integrity = `J_taint` (via `qualitative_admissible_is_JNI`) |
| endorsement dual | `InfluencedAtMost`, `sanitize_const_is_taint` | none | sanitizers carry proof obligations; the const sanitizer is full taint-freedom |
| endorsement teeth | `pleak_influenced_at_most_bit`, `full_flow_defeats_sanitizer` | standard 3 | `P_leak` integrity-read passes the bit-sanitizer bound; the full-copy program fails it |
| **T2, general** | `value_predicate_not_admissible` | **none** | no nontrivial value-predicate judgment satisfies A3 — one encoder breaks it |
| **T2, instance** | `blacklist_not_admissible` | **none** | the blacklist judgment holds of a real channel (`wall_never_bits`) and dies to the constant re-encoder |

The security reading of T2 is the field's folklore as a theorem: post-processing
is exactly what adversarial contexts do to outputs, so blacklist sanitization
dies to encodings, and with T1's uniqueness the flow formulation of
injection-freedom is *forced* — the unique admissible 2-safety shape. Scope
honesty: IMP has no strings; row 3's claim is the property *shape* (influence of
untrusted sources on trusted sinks), with the `P_leak` witnesses for
non-vacuity, not a model of SQL.

## The seam module (`Compose.lean`) — certified composition of components

Brick 2 of the security program: nobody had ever composed two *certified
programs* in this repo — conf-typing certified whole programs, the transport
interface composed certified maps abstractly. `Compose.lean` proves the seam
theorems at the IMP instance. A *component* is a program with a **boundary
certificate** — a claim at the Low-boundary granularity, which is itself a
channel claim (`boundaryNI_iff_resultNI`: the boundary is the `resultO`
channel; components speak the adversaries' observation language). The writer
structure of `eval` (`eval_seq`, `rfl`: stores thread, costs add, traces
concatenate) does the semantic work.

| result | Lean | axioms | content |
|---|---|---|---|
| writer decomposition | `eval_seq`, `obs_seq` | none (`rfl`) | composite runs are glued component runs; composite observations factor through component outcomes |
| boundary = channel | `boundaryNI_iff_resultNI`, `boundaryReleases_iff` | `propext, Quot.sound` | boundary certificates are `resultO`-channel claims (Closure and Policy forms) |
| **seam, Closure form** | `boundaryNI_seq`, `resultNI_seq` | **none** | boundary certificates compose; `c₁`'s certified boundary is what `c₂`'s certificate consumes |
| **seam, total form** | `outNI_seq` (via `outO := tup (resultO P) (tup wall branchO)`) | choice-free | Low store, cost, and branch trace of the composite all certified from the two component certificates |
| all channels | `seq_all_channels` | choice-free | every A3-derivable composite channel is certified — the seam adds no new obligations |
| integrity reading | `taint_result_seq` | **none** | untrusted data crossing two components cannot reach the composite sink unless a certificate lets it (T1, applied) |
| **seam, Policy form — the headline** | `releases_seq` with `seqRelease c₁ φ₁ φ₂ = ⟨φ₁, φ₂ ∘ boundary⟩` | **none** | delimited release composes; the composite certificate is *computed*, threading `c₁`'s map through `φ₂` — the same non-scalar semidirect shape as the Hölder certificate |
| strata nest across seams | `releases_seq_const_consistency` | none | constant releases specialize the Policy seam to the Closure seam |
| non-vacuity | `pleak_boundary_releases`, `pleak_chain_releases` | standard 3 | two policy components in sequence: the composite releases at most the paired bits, computed — no re-verification of the composite |
| **the teeth** | `broken_seam`, `channel_certs_do_not_compose`, `pleak_not_boundaryNI` | standard 3 | an uncertified upstream poisons a certified downstream; a wall-certificate is not a boundary certificate — both seam hypotheses are load-bearing, the granularity is forced |

The `seqRelease` shape is the load-bearing observation: release certificates
compose by *pairing through the first component's map* — declassification
budgets accumulate across the seam and nothing is silently discharged, which
is the repo's through-line discipline appearing at the security seam.

## The flow Bridge (`FlowBridge.lean`) — security received into the transport interface

The reception (brick 2, session 2): certified components live in the *same*
`GradedAction` interface as Lipschitz maps, Hölder maps, Markov kernels, and
quantum channels. The package now path-depends on `../transport-calculus`
(itself mathlib-free; the pattern `transport-kernel` already uses), so the
build stays instant and mathlib-free.

The instance: distance = `qd`, the **query distance** (which observations
`Store → Val` separate two stores — a distinguishability metric valued in the
lattice `QD` under pointwise implication); map = the component's boundary map;
certificates = monotone self-maps of `QD` in the `universalGA` (Cayley) form.
Two certificates per component: the **exact transform** `pull` (query
precomposition — composes definitionally, axiom-free) and the **leak bound**
`leakBound P φ` ("an output query separates only if it is non-Low, or a Low
input atom or the declared release already separated the inputs").

| result | Lean | axioms | content |
|---|---|---|---|
| exact bridge | `Bridge.ofComponent`, `ofComponent_cert` | **none** | every component is a Bridge, definitionally |
| **the reception equivalence** | `bridge_iff_releases`, `Bridge.ofRelease` | standard 3 | a `leakBound P φ`-certified Bridge exists **iff** `BoundaryReleases c P φ` — the security certificate and the transport certificate are the same datum |
| seam at the boundary | `boundaryReleases_seq` | choice-free | `releases_seq` restated at boundary granularity through the channel equivalences |
| **the reconstruction** | `comp_reconstructs_seq_release`, `comp_map_is_seq` | standard 3 | the *generic* `Bridge.comp` of (exact `c₁`-bridge, certified `c₂`-bridge) yields a certificate dominated by `leakBound P (seqRelease c₁ φ₁ φ₂)` — the seam theorem, computed by the interface with no security-specific reasoning |

Lossiness, recorded deliberately: composing two *abstraction* bridges
(`leakBound φ₂ ∘ leakBound φ₁`) is sound but trivial — the second bound cannot
know `φ₂` is evaluated at the boundary. The informative composition threads
the first component's *map* (`pull`), exactly as `seqRelease` threads `c₁`.
The supply-chain moral, as mathematics: **ship the boundary abstraction, not
just the budget.** With this module the repo's through-line closes at the
security end: security composition *is* certificate accumulation in the same
interface as the quantitative tiers.

## The checker (`SecTy.lean`) — certificates from syntax

Brick 3, session 1: the step from "prove your component's certificate" to
"type-check your component". `SecTy P pc c` is the classic pc-label flow
discipline (Volpano–Smith shape) over the four `Cmd` constructors; `secCheck`
is its executable shadow; soundness turns the decidable check into the
semantic `BoundaryNI` certificate — the input to every seam theorem and the
Bridge reception. Concrete components are certified by `decide`, not proof.

| result | Lean | axioms | content |
|---|---|---|---|
| expression labels | `exprLow`, `evalE_lowEq` | `propext` | Low expressions are functions of the Low store |
| **confinement** | `confinement` | **none** | High-context programs write no Low variable |
| **soundness** | `secTy_boundaryNI` | `propext` (choice-free) | a typed component carries the boundary certificate; the seam cases reuse brick 2 |
| the checker | `secCheck`, `secCheck_sound` | `propext` | executable; sound for the judgment (completeness not claimed — the usual price of decidability) |
| **certificates by `decide`** | `boundaryNI_of_check`, `resultNI_of_check`, `pok_certified`, `pok_seq_certified` | `propext`-ish | one decidable check yields the certificate; checker output composes through the seam with zero per-composite reasoning |
| the rejection | `pleak_rejected` | **none** | the checker rejects `P_leak` — and brick 2 proved that rejection semantically correct (`pleak_not_boundaryNI`): checker and semantics point at the same culprit |
| **the honesty theorem** | `typed_but_wall_leaks` | standard 3 | a well-typed program whose *running time* reveals the secret: session-1 soundness certifies the store boundary only; the timing channel needs the Policy stratum (session 2) or a padding discipline (out of scope) |

## The Policy checker (`SecTyD.lean`) — declared releases and the ledger

Brick 3, session 2. `SecTyD P Δ pc c` adds declared releases to the checker: a
policy budget `Δ` of permits (expression values, guard bits), demanded by the
check and *visible in what it certifies*. What a typed program reveals is the
**computed ledger** `relOf P c`, read off the syntax — and the ledger composes
by the brick-2 certificate algebra **definitionally**:
`relOf P (c₁; c₂) = seqRelease c₁ (relOf P c₁) (relOf P c₂)` is `rfl`.

| result | Lean | axioms | content |
|---|---|---|---|
| **the ledger law** | `relOf_seq` | **none** (`rfl`) | the checker's pipeline output *is* the seam theorem's computed certificate |
| soundness | `secTyD_sound`, `ite_aux` | choice-free | a typed component reveals at most its ledger (`BoundaryReleases c P (relOf P c)`); the `seq` case is literally `boundaryReleases_seq` |
| the checker | `secCheckD`, `secCheckD_sound`, `boundaryReleases_of_check` | choice-free | executable, budget-gated; certificates by `decide` |
| **the teeth** | `pfull_rejected_undeclared`, `pfull_accepted_declared`, `pfull_ledger` | `propext` / none | undeclared High flow rejected; declared, it passes *with the full release as a visible line item* — declaration is not a bypass |
| **the money theorem** | `pleak_checksD`, `checker_rederives_pleak_bound` | **choice-free** | `P_leak` checks under one guard permit, and the checker rederives the hand-proved Paper-1 bound (`result_releases_at_most_bit`'s exact statement) — with a *smaller* axiom footprint than the hand proof |

Honesty carried forward: `relOf` is deliberately coarse for undeclared High
guards (a weaker, still-sound claim), and the instrumented channels stay at
session-1 honesty — the ledger certifies the store boundary.

## The product (`Pipeline.lean`) — multi-tenant isolation and the pipeline theorem

Brick 3, session 3: the two demos closing the security program's
component-boundary fork.

**Multi-tenant isolation is noninterference, checked** (VULN-COVERAGE row 7,
now [proved]). Two tenants share a multiplexer; each tenant's data and output
channel are classified together. The checker proves isolation both ways, and
it survives composition.

| result | Lean | axioms | content |
|---|---|---|---|
| isolation each way | `multiplex_isolates_A`, `multiplex_isolates_B` | choice-free | cross-tenant isolation *is* `J_NI` at the tenant's partition — the T1 relabeling made concrete, from a `decide` |
| isolation composes | `multiplex_pipeline_isolates_B` | `propext` | two multiplexer stages stay isolated, zero per-composite reasoning |
| **teeth** | `leaky_rejected`, `leaky_not_isolated` | none / standard 3 | a component routing B's data into A's channel is rejected by the checker *and* proved non-isolated — they agree |

**The pipeline theorem: syntax in, certified composed Bridge out.**

| result | Lean | axioms | content |
|---|---|---|---|
| composed certificate | `certified_pipeline` | choice-free | a Closure-checked then Policy-checked pair composes into one `BoundaryReleases` certificate, computed — no semantic reasoning about the composite |
| **the product** | `certified_pipeline_bridge`, `certified_pipeline_reconstruction` | choice-free / standard 3 | the pipeline is a Bridge in the transport interface, and the *generic* `Bridge.comp` reconstructs its seam certificate — security composition by the same law that composes contraction estimates |
| concrete demo | `demo_pipeline`, `demo_pipeline_bridge` | choice-free | `P_ok` then `P_leak`: the whole stack certified from two `decide`s |

## The assumption ledger (`Ledger.lean`) — the trusted base as a composable certificate

Brick 4, session 1: the deferral bricks 2 and 3 both named. A real component
relies on things it does not verify — an upstream's data classification, a
library's correctness, a crypto primitive's security. Those are *assumptions*,
not evidence. A **ledger** `Γ : List Prop` records a component's trusted base; a
**conditional certificate** `CondBoundary c P Γ := Sat Γ → BoundaryNI c P` is a
guarantee relative to it.

| result | Lean | axioms | content |
|---|---|---|---|
| ledger satisfaction | `Sat`, `sat_append` | `propext` | a ledger holds when all its assumptions do; append splits |
| **accumulation** | `condBoundary_seq`, `condReleases_seq` | choice-free | the composite's trusted base is the *union* (`Γ₁ ++ Γ₂`) — every part's assumptions carried, none dropped |
| discharge is explicit | `condBoundary_nil`, `condBoundary_discharge`, `condBoundary_discharge_head` | **none** | empty ledger = unconditional certificate; collapsing a conditional one requires *proving* the ledger |
| over-approximation | `condBoundary_of_unconditional`, `condBoundary_weaken` | **none** | unused assumptions are always sound to add |
| **no silent discharge** | `ledger_no_silent_discharge` (`cx_cond`, `cx_not_unconditional`) | standard 3 | a component secure *only if* input `x` is classified Low: the conditional certificate holds for every classification, but the unconditional one is **false** where `x` is High — the ledger entry is load-bearing, dropping it unsound |

`ledger_no_silent_discharge` is the composition-level analogue of
`attest_is_not_J_evidence` (§6.1): an assumption coexists with an obligation but
never becomes its proof.

### The ledger rides the interface (`LedgerBridge.lean`)

Session 2: the trusted base accumulates by the *same* composition law as every
other certificate. `ledgerGA` is the flow `GradedAction` with a **phantom ledger
grade** — certificate `(Mono QD qle × Ledger)`, `mul` composing the flow
transform *and appending the ledgers*, `act` ignoring the ledger.

| result | Lean | axioms | content |
|---|---|---|---|
| the graded action | `ledgerGA`, `ledger_act_phantom` | **none** | a valid `GradedAction` (`act_mul` is `rfl`); flow behaviour is exactly `flowGA`'s, the ledger rides as provenance |
| **accumulation law** | `ledgerBridge_comp_ledger`, `ledgerBridge_comp_flow` | **none** (`rfl`) | `Bridge.comp` appends the trusted base — the same law that composes flow certificates, Lipschitz constants, and Dobrushin coefficients |
| components as ledger-Bridges | `Bridge.ofComponentL`, `Bridge.ofReleaseL` | none / standard 3 | `ofReleaseL` *demands* `Sat Γ` — no certified Bridge without discharging the base it carries |
| **the SBOM as a theorem** | `ledger_supply_chain_ledger`, `_map`, `_bound` | standard 3 | composing a released downstream with an exact upstream: the composite's ledger is the union `Γ₂ ++ Γ₁`, its map is the composite boundary, and its flow certificate is the brick-2 seam certificate — provenance and guarantee by one `Bridge.comp` |

The bill of materials (what a composed guarantee assumes) and the security proof
are literally the same composition — computed, not maintained by hand.

### The worked supply chain (`SupplyChain.lean`)

Session 3: the checker *generates* conditional certificates, and a concrete
trust pipeline (VULN-COVERAGE row 11).

| result | Lean | axioms | content |
|---|---|---|---|
| **checker emits conditional certs** | `condBoundary_of_check_assuming` | choice-free | check the component pretending untrusted input `x` is Low; success yields a certificate conditional on `x` actually being Low — the trust assumption made explicit |
| `Biz` conditional cert | `biz_check`, `biz_cond` | standard 3 | business logic copying an upstream library's output is certified relative to the one assumption "the library output is Low" — generated, not hand-proved |
| **pipeline carries one assumption** | `supply_chain_ledger` | standard 3 | `Biz; Log` is certified relative to `[P "safe" = false]` — the union of ledgers, accumulated automatically |
| discharge | `supply_chain_discharged` | standard 3 | verify the library later → the pipeline's certificate collapses to unconditional |
| **load-bearing** | `biz_needs_assumption` | standard 3 | without the assumption `Biz` provably leaks — the ledger entry is exactly as strong as the trust it names |

Scope, honest: this is row 11 at IMP granularity — the *assumption-tracking
mechanism* is proved; the external assumption ("the library/cipher is correct")
stays an assumption, which is the entire content of a LEDGER verdict.

## The timing-sensitive checker (`SecTyT.lean`) — certifying the clock

Brick 5. Brick 3's `typed_but_wall_leaks` was an honesty theorem: the store-only
checker accepts programs that leak through the instrumented channels (a
High-guarded branch with unequal branch costs leaks its running time). `SecTyT`
closes that gap by **forbidding High-guarded branches** — only Low guards
(`iteL`) survive, so two Low-equal runs always take the same branch and agree on
cost and trace as well as the store.

| result | Lean | axioms | content |
|---|---|---|---|
| the judgment | `SecTyT`, `SecTyT.toSecTy` | — | `SecTy` at `pc=false` minus `iteH`; refines the store discipline |
| **soundness** | `secTyT_outNI`, `outNI_to_JNI`, `secTyT_sound` | choice-free | the *whole* instrumented outcome — Low store, running time, branch trace — is Low-determined (`J_NI c (outO P) P`) |
| executable | `secCheckT`, `secCheckT_sound`, `outNI_of_checkT` | choice-free | certificates by `decide`; `secCheckT_imp_secCheck` — certifying the clock implies certifying the store |
| **teeth** | `ptime_rejected_T` | **none** | the checker rejects the brick-3 leak witness `Ptime` — correctly, since `typed_but_wall_leaks` proved it leaks the clock. `secCheck` = store-safe, `secCheckT` = store- and clock-safe: the two bracket the timing channel |

Honest scope: this certifies timing-*insensitivity* (no secret-dependent
branching); a program that must branch on a secret is rejected, not repaired — the
channel closed by construction, the price being expressiveness. The declassified
case (a High branch whose timing is *declared* released) is the Policy-stratum
analogue, for a later brick.

## §11 pre-mechanization checklist (framework doc)

What this instance encodes from the framework's checklist:

- **Item 6 — no `T-Conf-discharges-J`.** The `Discharge` inductive has *only*
  `clo` and `pol` constructors. There is no constructor producing a
  `conformance` discharge or consuming `Ev_attest`. The absence is the
  encoding of "no coercion"; `reject_Jinvariant` proves it holds for all `J`.
- **Policy carries a proof obligation, not a permit.** `pol` requires *both* a
  declared release `φ` (`Pi o φ`, the normative act) *and* a proof
  `ReleasesAtMost c o P φ` that the channel reveals at most `φ`. Declaring a
  channel is **not** a free pass — `result_full_not_bounded_by_bit` shows the
  bound is falsifiable. (v0.1 had the pre-bulletproofing unbounded form
  `o ∈ Π`; that was checklist-item-3 unsound and is fixed in v0.2.)
- **Closure vs Policy is not a signature split.** Both are Σ_sem; the framework
  nests them (`closure_is_const_policy`). We keep three `Stratum` tags anyway,
  so the derivation records *whether a declassification was claimed* — and so
  that nothing tempts folding the genuinely-disjoint Conformance stratum "for
  symmetry".
- **`Admissible` is a property of `J`, used à la carte.** `J` is a bare
  parameter `JTy`; `JNI_postproc` (A3) and `JNI_separable` (Def. 5) are proved
  *about* the `J_NI` instance, never assumed of an abstract `J`.
- **`≅` is 𝒪-observational equivalence; bit-identity ⟹ ≅ needs Sem-Det/Closed.**
  `conform_refl` is exactly that implication, discharged by `eval` being a
  pure total function.
- **The gate transports *both* strata.** `transport_JNI` (Closure) and
  `transport_releases` (Policy) compose into `confidential_transport`, so the
  bounded guarantee proven about `A` holds of the running `deploy` — no
  artifact/deploy asymmetry for the joint layer to inherit.

## Not yet mechanized (the honest residue)

- **`J_ε` and non-separability (Prop. 2).** Mutual information `I(o;High|Low)`
  needs a *distribution over High inputs*, which the deterministic semantics
  here does not have — so the `H⊕r` witness is not a mathlib addendum but a
  probabilistic layer over inputs (entropy, data-processing as a theorem):
  Paper 2 proper. The mathlib-free `Joint.lean` already states *where* it
  fails (the forward cell) without needing any of it.
