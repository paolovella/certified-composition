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
| `ConfTyping/SecTyTD.lean` | brick 6 / `VULN-COVERAGE.md` row 2 | declassified timing: a secret branch is allowed when its bit is declared released; the outcome reveals at most the declared bits |
| `ConfTyping/WhileImp.lean` | brick 7 / `VULN-COVERAGE.md` row 13 | loops: a fuel-indexed semantics, the termination channel, termination-sensitive soundness, and the faithful embedding of the loop-free fragment |
| `ConfTyping/WhileCompose.lean` | brick 8 / `VULN-COVERAGE.md` rows 12–13 | the seam over loops: certified looping components compose, divergence threading through the boundary in lockstep |
| `ConfTyping/WhileLedger.lean` | brick 9 / `VULN-COVERAGE.md` rows 11–13 | the assumption ledger over loops: conditional termination-sensitive certificates whose no-silent-discharge witness guards the halting channel |
| `ConfTyping/WhileBridge.lean` | brick 10 / `VULN-COVERAGE.md` rows 12–13 | the Bridge reception over loops: looping components land in the transport interface with termination a first-class coordinate of the distance |
| `ConfTyping/MemSafe.lean` | brick 11 / `VULN-COVERAGE.md` row 6 | heap and memory safety: a machine that can get stuck on a wild dereference, and a flow-sensitive checker whose programs provably never do |
| `ConfTyping/MemFree.lean` | brick 12 / `VULN-COVERAGE.md` row 6 | free and use-after-free: a liveness-tracking machine and a linearity checker that rules out use-after-free and double-free by construction |
| `ConfTyping/HeapFlow.lean` | brick 13 / `VULN-COVERAGE.md` rows 1, 6 | information flow through the heap: noninterference over a labeled heap — the unification of the confidentiality and memory halves |
| `ConfTyping/InjectionReal.lean` | brick 14 / `VULN-COVERAGE.md` row 3 | injection made real: a tokenizer with quote-breaking, parameterization injection-safe by construction, concatenation injectable |
| `ConfTyping/QueryProgram.lean` | brick 15 / `VULN-COVERAGE.md` row 3 | injection in a running program: a taint-flow checker over a string-manipulating language, proved sound (accepted programs are injection-free) |
| `ConfTyping/DbInjection.lean` | brick 16 / `VULN-COVERAGE.md` row 3 | stored / second-order injection: per-cell taint over a persistent store; the per-request shortcut proved unsound |
| `ConfTyping/PathTraversal.lean` | brick 17 / `VULN-COVERAGE.md` row 14 | path traversal (CWE-22): the `..` attack and the leaf-name fix, proved — the injection method generalized to a second class |
| `ConfTyping/LatticeFlow.lean` | brick 18 / `VULN-COVERAGE.md` row 1 | a security label lattice: noninterference for an arbitrary lattice + observer, with a non-binary (diamond) witness |
| `ConfTyping/AliasSafe.lean` | brick 19 / `VULN-COVERAGE.md` row 6 | pointer aliasing: exact-address tracking rules out use-after-free through an alias — dropping brick 12's no-copy linearity |
| `ConfTyping/HeapLoop.lean` | brick 20 / `VULN-COVERAGE.md` rows 6, 13 | heap safety under loops: a fixed-point checker (loop invariant), sound by fuel induction — brick 11's heap meets brick 7's loops |
| `ConfTyping/ParseSource.lean` | brick 21 / `VULN-COVERAGE.md` row 3 | a real parser: recursive descent + round-trip correctness, so the injection guarantee attaches to source *text* not a hand-built AST |
| `ConfTyping/LexSource.lean` | brick 22 / `VULN-COVERAGE.md` row 3 | a lexer: characters → tokens with round-trip correctness — the full string → lex → parse → check → theorem pipeline |
| `ConfTyping/FreeLoop.lean` | brick 23 / `VULN-COVERAGE.md` row 6 | free under loops: linearity (brick 12) carried as a loop invariant through fuel induction (brick 20) — the last hard combination |
| `ConfTyping/AliasLoop.lean` | brick 24 / `VULN-COVERAGE.md` row 6 | may-alias under loops: a may-alias partition makes `copy` + `free` + loops sound — the depth follow-on brick 23 named |
| `ConfTyping/LexReal.lean` | brick 25 / `VULN-COVERAGE.md` row 3 | a richer alphabet: multi-character keywords and digit-run identifiers under a maximal-munch scanner with a proved round trip |
| `ConfTyping/QueryGrammar.lean` | brick 26 / `VULN-COVERAGE.md` row 3 | a fuller query grammar: parameterization proved injection-safe over a template with `n` literal slots |
| `ConfTyping/CmdInjection.lean` | brick 27 / `VULN-COVERAGE.md` row 3 | a second real sink: OS command injection (CWE-78) by the same data-not-structure discipline |
| `ConfTyping/DecimalId.lean` | brick 28 / `VULN-COVERAGE.md` row 3 | decimal identifiers: a verified decimal codec (`ofDigits_toDigits`) + a maximal-munch decimal reader — closes brick 25's run-length residual |
| `ConfTyping/LogInjection.lean` | brick 29 / `VULN-COVERAGE.md` row 3 | a third real sink: log injection / log forging (CWE-117) — the newline record-separator metacharacter, structured logging immune by construction |
| `ConfTyping/AliasFix.lean` | brick 30 / `VULN-COVERAGE.md` row 6 | fixpoint may-alias: infers a coarsening loop invariant (`ALInv_coarsen`, `loopFix_correct`), accepting alias-maintaining loops brick 24's one-pass rule rejected |

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

## Declassified timing (`SecTyTD.lean`) — the Policy analogue of the clock

Brick 6. Brick 5 closed the timing channel by *forbidding* secret-dependent
branching; a program that must branch on a secret was rejected, not certified.
`SecTyTD` adds the declassification stratum to the clock: a High guard is allowed
**when its branch bit is declared released** (`iteD`, the brick-3 policy budget
`Δ` over the timing checker), and the outcome is then certified to reveal at most
the declared bits.

| result | Lean | axioms | content |
|---|---|---|---|
| the judgment | `SecTyTD` | — | `SecTyT` + declared guards (`iteD`) and writes (`assignD`); still no *undeclared* secret branch |
| **soundness** | `secTyTD_outReleases`, `iteTD_aux`, `secTyTD_sound` | choice-free | the whole outcome (store, running time, trace) reveals at most the ledger `relOf P c` — `ReleasesAtMost c (outO P) P (relOf P c)`; the declared bit forces same-branch, bounding the timing |
| executable | `secCheckTD`, `secCheckTD_sound`, `releasesAtMost_of_checkTD` | choice-free | certificates by `decide` |
| **money theorem** | `ptime_rejected_TD`, `ptime_checksTD`, `ptime_timing_released`, `ptime_wall_of_bit` | choice-free | `Ptime` (secret branch, unequal costs): rejected under an empty budget (brick 5), but under one declared permit its running time is certified to reveal *at most* the secret bit — a rejected leak becomes a bounded, declared release |

The ledger `relOf` (brick 3) already carries each non-Low guard's branch bit, so
the released quantity *is* the declassified timing — no new bookkeeping. Together
with brick 5: `secCheckT` closes the clock by construction, `secCheckTD` opens it
exactly as far as declared and no further.

## Loops and the termination channel (`WhileImp.lean`) — the model grows

Brick 7, the frontier: bricks 1–6 worked over loop-free `Cmd`, where `eval` is a
total structural recursion. Loops break that totality and open a genuinely new
channel — **termination**: a `while` on a secret guard loops forever iff a secret
bit is set, leaking it through *whether the program halts*, invisible to any
analysis of terminating runs. This module adds loops additively (a fresh `WCmd`,
so the 22 existing modules are untouched) with a **fuel-indexed** evaluator.

| result | Lean | axioms | content |
|---|---|---|---|
| the semantics | `wexec : Nat → WCmd → Store → Option Outcome` | — | total by recursion on fuel; `none` = fuel exhausted, which is how non-termination appears |
| outcome low-eq | `optLowEq`, `optLowEq_bind`, `optLowEq_map` | — | agree on *whether* they halt and, if so, on Low store, cost, trace — the `none`/`some` mismatch being `False` **is** the termination channel |
| **termination-sensitive soundness** | `wsecTy_sound` | choice-free | a Low-guarded discipline (`WSecTy`, no `iteH`/`whileH`) makes two Low-equal runs lockstep at every fuel — same halting, store, time, trace |
| executable | `wcheck`, `wcheck_sound`, `optLowEq_of_wcheck` | choice-free | certificates by `decide` |
| **the termination leak** | `wleak_leaks`, `wleak_rejected` | standard 3 / **none** | `while b skip` halts iff `b=0`; at one fuel one run halts and the other spins, so NI fails — and the checker rejects it. Checker and semantics agree the channel is real |
| a certified loop | `wok_certified` | choice-free | a Low-guarded loop, certified from one `decide` |
| **faithful embedding** | `embed`, `wexec_mono`, `wexec_embed_eq` | choice-free | every loop-free `Cmd` embeds into `WCmd`, and with enough fuel `wexec` computes exactly the total `eval` — the prior six-brick program is this one's loop-free fragment. The model **grew**, it did not fork |

Honest scope: `WSecTy` certifies termination-*insensitivity* (secret-guarded
loops rejected, not repaired). A declassified-termination stratum (a secret loop
whose halting is *declared* released) is the Policy analogue, a later brick.

## The seam over loops (`WhileCompose.lean`)

Brick 8: the composition differentiator, ported from loop-free `Cmd` (brick 2) to
the looping language. The boundary certificate `WOutNI c P` — at every fuel,
Low-equal runs are `optLowEq` (halt together, agree on Low store / time / trace) —
is exactly what brick 7's soundness produces, so a `wcheck`-passing component earns
it by `decide`.

| result | Lean | axioms | content |
|---|---|---|---|
| boundary cert from the checker | `wsecTy_WOutNI`, `WOutNI_of_wcheck` | choice-free | a typed/checked looping component carries the full-outcome termination-sensitive certificate |
| **the seam over loops** | `WOutNI_seq`, `WOutNI_seq_of_check` | choice-free | two certified looping components compose; the new clause the loop-free seam never had: **if `c₁` diverges the composite diverges in lockstep** — divergence composes, the termination channel stays closed across the boundary |
| certified pipeline | `wok_pipeline_certified` | choice-free | two Low-guarded loops in sequence, certified from two `decide`s, termination included |
| **teeth** | `wleak_poisons_seam` (`skip_WOutNI`) | standard 3 | a divergence-leaking upstream (`Wleak`) wired into a certified `skip` makes the composite leak termination — the seam's upstream hypothesis is load-bearing, the looping analogue of `broken_seam` |

## The assumption ledger over loops (`WhileLedger.lean`)

Brick 9: the trusted-base discipline of brick 4, ported to the looping language
(reusing the `Sat`/`Ledger` infrastructure verbatim — only the certificate
changes from `BoundaryNI` to the termination-sensitive `WOutNI`).

| result | Lean | axioms | content |
|---|---|---|---|
| conditional cert | `WCondBoundary c P Γ := Sat Γ → WOutNI c P` | — | a looping component's termination-sensitive guarantee relative to a trusted base |
| **accumulation** | `WCondBoundary_seq` | choice-free | the composite's base is the union `Γ₁ ++ Γ₂` — via the looping seam, so the divergence guarantee accumulates with the base |
| discharge | `WCondBoundary_nil`, `WCondBoundary_discharge`, `WCondBoundary_weaken` | choice-free | empty base = unconditional; collapsing requires proving the base |
| checker-generated | `WCondBoundary_of_check_assuming` | choice-free | check under a declared trust assumption about an untrusted input |
| **no silent discharge — termination form** | `wledger_no_silent_discharge` (`wcx_cond`, `wcx_not_unconditional`) | standard 3 | `while x skip` guarded by an untrusted `x`: termination-safe *assuming* `x` is Low, but if `x` is High the loop's *halting* depends on the secret — the ledger entry guards the **termination channel itself**, the sharpest form of the discipline |

## The Bridge reception over loops (`WhileBridge.lean`)

Brick 10, the last unported piece — and the one with genuine design content.
A looping component's boundary is a *partial* map (it may diverge), so the
transport carrier lifts from `Store` to `OStore := Option Store` (`none` =
diverged), and the query distance gains a **halting query** `haltQ` that observes
whether a run terminated. Termination becomes an observable *in the metric*.

| result | Lean | axioms | content |
|---|---|---|---|
| the halting coordinate | `haltQ`, `haltQ_wlow` | choice-free | the query that only loops have — "did it terminate?" — is a Low observable, so divergence is visible in the distance |
| **the exact reception** | `Bridge.ofWComponent`, `ofWComponent_comp_map`, `ofWComponent_comp_cert` | **none** | any looping component is a Bridge at any fuel, definitionally, and composes by the generic `Bridge.comp` |
| **the reception equivalence** | `wbridge_iff_sound` | classical | on halting inputs, the `wNIBound` contraction holds **iff** the component is store-and-halting noninterferent — the halting query makes "iff" mean *termination-sensitive* |
| checked ⟹ contracts | `WOutNI_imp_haltNI`, `wOutNI_contracts` | choice-free / classical | a `WOutNI` component (brick 7/8, from the checker) contracts in the interface at every fuel |

Honest scope: the security contraction is stated on *halting* input pairs
(`some σ, some σ'`); a diverged-upstream input (`none`) is a distinct regime not
bounded by the downstream's input Low-atoms, so it is not folded into a single
leak-bound Bridge — the exact Bridge covers all inputs, the leak-bound
equivalence covers the halting ones. **With this the looping language has the
full discipline: soundness, seam, ledger, and reception.**

## Heap and memory safety (`MemSafe.lean`) — a new *kind* of property

Brick 11, the first brick of the memory-safety sub-project. Every prior brick
certified a *confidentiality* channel (store, timing, termination); memory safety
is a **safety property of a richer machine** — the semantics can get *stuck* on a
wild dereference. The map carried memory safety as CARRIED (transported, not
generated) since brick 1; this generates it.

The machine (additive: fresh `MCmd`/`MState`) has a heap and an allocation
high-water mark `n` — addresses `[0, n)` are live, the rest wild. `mexec` returns
`Option MState`, and `none` is a **memory error** (a load/store through a wild
address). Memory safety is "never `none`".

| result | Lean | axioms | content |
|---|---|---|---|
| **safety by construction** | `mcheck_safe` | standard 3 | a checked program never hits a memory error, and its tracked pointers stay valid — proved by induction on an invariant tying the flow-sensitive tracked set to the heap's live region |
| certified by `decide` | `msafe_of_check`, `mpsafe_memsafe` | standard 3 | from the empty tracked set a checked program runs to a real state, never stuck |
| **teeth** | `mwild_store_errors`, `mwild_rejected` | choice-free | a store through an unallocated pointer errors at runtime *and* is rejected by the checker — the two agree the access is unsafe |

The checker `mcheck` is flow-sensitive: it threads the set of variables known to
hold in-bounds addresses (`alloc` grows it, `assign`/`load` drop the reassigned
variable, `ite` intersects the branches), and permits a load/store only through a
tracked variable. This is the first step from CARRIED to generated for row 6.

## Free and use-after-free (`MemFree.lean`)

Brick 12, the sub-project's sharpest witness. Brick 11's machine could only *grow*
the live region; the real prize — **use-after-free** (CWE-416) — needs a machine
that can *shrink* it, so the state gains a **liveness map** `L : Int → Bool` and a
`free` operation, and `fexec` returns `none` on a use-after-free *or* a
double-free. Freeing is sound only under **linearity**: the checker's tracked
pointers must hold *distinct* live addresses, so freeing one cannot dangle another.

| result | Lean | axioms | content |
|---|---|---|---|
| **safety with free** | `fcheck_safe` | standard 3 | a checked program never hits a use-after-free or double-free; the linearity invariant `FInv` (tracked ⟹ live, in-bounds, pairwise distinct) is preserved |
| certified by `decide` | `fsafe_of_check`, `fpsafe_memsafe` | standard 3 | `alloc; store; free` runs clean |
| **use-after-free teeth** | `uaf_errors`, `uaf_rejected` | choice-free | `alloc p; free p; store p` dereferences a freed cell — a runtime error, and rejected by the checker (which drops `p` at the `free`) |
| **double-free teeth** | `double_free_errors`, `double_free_rejected` | choice-free | the second `free` of the same cell errors and is rejected |

Since pointers are produced only by `alloc` (never copied into another tracked
variable), the mark keeps every tracked address distinct for free — that is why the
linearity clause holds inductively. Follow-on: pointer copying with alias tracking,
heap loops, and information flow through the heap.

## Information flow through the heap (`HeapFlow.lean`) — the unification

Brick 13, where the two halves of the program meet. Bricks 1–10 certified
*confidentiality* (noninterference) over the store; bricks 11–12 certified
*memory safety* over a heap. This brick proves **noninterference over a heap**:
the observable is the store *and* the Low region of the heap, and the leak it
rules out is a secret in a High heap cell reaching a Low variable through a load
(or High data reaching a Low cell through a store).

The machine is a store plus a heap with a static address partition
`Q : Int → Bool` (a "labeled memory" — each access's region is statically known).
`iLowEq P Q` is Low-equivalence of the whole state: Low variables and Low cells
equal. The type system `HSecTy` is the pc-label discipline plus heap rules —
`storeL` (a Low cell takes only Low data in a Low context), `loadL` (a Low
variable is loaded only from a Low cell in a Low context), and `storeH`/`loadH`
(High cells and variables absorb anything).

| result | Lean | axioms | content |
|---|---|---|---|
| confinement | `hconfine` | choice-free | a High-context command leaves Low variables *and* Low cells unchanged |
| **noninterference** | `hsecTy_ni` | choice-free | a typed program maps Low-equivalent states to Low-equivalent states — no High variable or High cell leaks into the Low observation |
| executable | `hcheck`, `hcheck_sound`, `ni_of_check` | choice-free | certificates by `decide` |
| **the heap leak** | `heap_leak`, `leak_rejected` | standard 3 / **none** | loading a High cell into a Low variable leaks the secret (two heaps differing only on the secret cell give different Low output) and is rejected by the checker — the two halves agree |

Orthogonality, recorded not re-proved: memory *safety* (bricks 11–12) and this
*information-flow* property are independent invariants of the same heap — one
keeps accesses in bounds, the other keeps them non-leaking — and compose. This
brick is the natural culmination: the confidentiality discipline of the first ten
bricks and the memory discipline of bricks 11–12, over one machine.

## Injection, for real (`InjectionReal.lean`) — the property shape becomes a query

Brick 14, making one channel *real*. Brick 1 handled injection as a property
shape (T1: taint-freedom is integrity NI; T2: blacklists fail A3) — honest, but
there was no query, no parser, no quote. This brick models the actual mechanism.

A query is a character string tokenized the way a database does it: a quote `'`
toggles in/out of a string literal, so the string splits into alternating
**structural** segments (the command) and **data** segments (literal contents).
The *skeleton* — the structural segments — is the executed command; **injection
is untrusted data changing the skeleton.**

| result | Lean | axioms | content |
|---|---|---|---|
| tokenizer lemmas | `segs_qfree`, `segs_append_q` | choice-free | a quote-free run is one segment; a quote-free prefix splits cleanly |
| **parameterization is immune** | `param_immune`, `param_noninterference` | **none** | the executed structure is independent of the untrusted value — injection-freedom *by construction* (the value is never re-tokenized) |
| parameterization is correct | `param_correct` | `propext` | for a benign (quote-free) value it computes the intended structure — not cheating |
| **concatenation is injectable** | `concat_injectable`, `concat_leaks` | **none** | with the same template, a benign value and an injection payload `' R` give different skeletons — SQL injection (`' OR …`) as a theorem |
| the fix as integrity NI | `param_sink_trusted` | **none** | the parameterized sink factors through the trusted template alone — T1's unique admissible 2-safety form, on a real query |

This is the depth step: injection stops being an abstract 2-safety shape and
becomes a concrete query with a real tokenizer, the real attack (quote-breaking),
and the real industrial fix (prepared statements) **proved correct by
construction** — connected back to T1's `taint_is_JNI` as the property it
satisfies.

## Injection in a running program (`QueryProgram.lean`) — the taint-flow linter

Brick 15 connects brick 14's real query mechanism to an actual program. A
string-manipulating language (`input`, `lit`, `concat`, `emitC` = emit a built
query, `emitP` = emit a parameterized query) runs against an untrusted input; a
flow-sensitive taint checker `qcheck` tracks which variables the input reaches
and rejects `emitC` of a tainted query. This is the shape of a real SQL-injection
static analyzer — flag `q = tmpl + name; exec(q)`, bless `exec_param(tmpl, name)`
— with the flagging **proved sound**.

| result | Lean | axioms | content |
|---|---|---|---|
| **soundness** | `qcheck_ni` | choice-free | two-run noninterference: a checked program on any two inputs yields related states, so the emitted queries agree — the taint set precisely bounds the input's reach |
| top-level guarantee | `injection_free_of_check`, `safe_injection_free` | choice-free | an accepted program emits the identical query structure for *every* untrusted input — injection-free, by `decide` on the check |
| **the caught bug** | `unsafe_rejected`, `unsafe_leaks` | choice-free / **none** | `input; concat into template; emit` is rejected *and* genuinely leaks (a benign input vs. an injection payload `' R` emit different skeletons) — the warning is warranted |
| the blessed fix | `safe_accepted` | choice-free | `input; emit-parameterized` passes |

This is the closest the artifact gets to a real tool: a linter for a running
program, with a machine-checked proof that what it accepts cannot be injected.
Honest limit: the language is small (string variables, one concat, two emit
sinks) and the query mechanism is brick 14's single quote-delimited literal.

## Stored / second-order injection (`DbInjection.lean`) — taint that persists

Brick 16, a sharp named class brick 15 could not see. **Stored (second-order)
injection**: untrusted data is written to the database in one request, read back
in a later one, and concatenated into a query — where a per-request analysis has
forgotten it was ever tainted. The machine gains a **persistent store** (`db`)
with `dbwrite`/`dbread`.

| result | Lean | axioms | content |
|---|---|---|---|
| **soundness across persistence** | `dbcheck_ni`, `db_injection_free_of_check` | choice-free | the sound checker tracks taint *per database cell* (a cell is tainted once tainted data is written; a read of a tainted cell taints the variable) — a checked program emits the same queries for every input, even through the database |
| **the per-request shortcut is unsound** | `naive_accepts_stored` | choice-free | a naive checker that treats reads as clean *accepts* the stored-injection program |
| **and it really leaks** | `stored_injection_leaks` | **none** | routed through the database, a benign input and an injection payload emit different skeletons — the naive acceptance is genuinely wrong |
| the sound checker catches it | `sound_rejects_stored` | choice-free | per-cell taint rejects the same program |

The moral, as a theorem: **injection-freedom does not survive persistence unless
taint does.** The discipline that catches second-order injection is exactly
per-cell taint tracking, and the per-request shortcut is proved unsound — a
concrete demonstration that the framework's soundness catches a class real
analyzers routinely miss.

## Path traversal (`PathTraversal.lean`) — the method generalizes

Brick 17 shows the "make a channel real" method is not injection-specific.
Injection is one instance of *untrusted data changing the meaning of a
structured sink*; **path traversal** (CWE-22) is another — an untrusted filename
containing `..` escapes the intended base directory. A path input is a list of
steps (`down n` = enter a subdirectory, `up` = `..`); resolving it against a base
either stays under it (contained) or pops above it (escape).

| result | Lean | axioms | content |
|---|---|---|---|
| **the attack** | `traversal_escapes`, `dotdot_escapes` | choice-free | `foo/../../` (and a bare `..`) escapes the base — the resolver returns `none`, `../../etc/passwd` as a theorem |
| **safe when flat** | `flat_contained` | choice-free | a `..`-free input always stays contained — untrusted *names* can't escape, only untrusted *structure* (`..`) can |
| **the fix by construction** | `openLeaf`, `openLeaf_contained` | **none** | an API taking a *leaf name* (not a path) never traverses, whatever the name — the path-analog of a bound query parameter |
| **the check is sound** | `pathCheck_sound`, `pathCheck_rejects` | choice-free / none | "reject inputs containing `..`" is sound (accepted ⟹ contained) and rejects the traversal witness |

Same pattern as parameterized queries: keep the untrusted value in a data
position (a leaf), never a structural one (a `..`), and containment is a theorem.
This is breadth of the *depth method* — a second real, named vulnerability class
made real, reusing the injection line's structure.

## A security label lattice (`LatticeFlow.lean`) — past binary High/Low

Brick 18 generalizes the *foundational* abstraction. Every confidentiality brick
(1–13) rests on a binary `Partition : String → Bool` — the two-point lattice. The
classic Denning generalization is an arbitrary **security lattice**: levels
ordered by "may flow to", with a join, and noninterference stated *for every
observer level* `ℓ`. This matters because binary cannot express *mutually
incomparable* compartments; a lattice can.

| result | Lean | axioms | content |
|---|---|---|---|
| **lattice noninterference** | `latSecTy_ni` | standard 3 | for any lattice `𝓛` and observer `ℓ`, a typed program maps states agreeing below `ℓ` to states agreeing below `ℓ` — information at a level `⋢ ℓ` never reaches an `ℓ`-observer |
| confinement | `latConfine` | `propext` | a command whose context is not below `ℓ` leaves the `ℓ`-observable state unchanged |
| the diamond lattice | `dmdLat` | `propext` | `⊥ < a, b < ⊤` with `a`, `b` incomparable — a lattice that is not a chain, impossible in `Bool` |
| **the non-binary witness** | `crosscompartment_untypable`, `crosscompartment_leaks` | `propext` | a flow from compartment `a` to a compartment-`b` observer is untypable *and* really leaks — a guarantee the binary High/Low model cannot even state |

Binary High/Low is the two-point instance of `latSecTy_ni`; the diamond witness
shows the generalization is real — two compartments each secret to the other,
which needs two incomparable labels that do not exist in `Bool`. This is the
deepest single generalization of the confidentiality core.

## Pointer aliasing (`AliasSafe.lean`) — use-after-free through an alias

Brick 19, the hard memory extension. Brick 12's `free` was sound only under
**linearity**: tracked pointers held distinct addresses and copying was *banned*,
so freeing one could not dangle another. Real code copies pointers (`q = p`),
and then `free p` dangles `q`. Ruling out the resulting use-after-free needs an
alias analysis — which linearity dodged by forbidding the copy.

The insight that makes it tractable *and precise*: in a loop-free program the
allocation addresses are **statically determined** (the k-th `alloc` returns
address `k`), so the checker tracks the *exact* address each pointer holds — a
must-alias analysis. `copy x y` gives `x` the same tracked address as `y`;
`free x` marks that address freed; an access through *any* variable holding a
freed address is rejected.

| result | Lean | axioms | content |
|---|---|---|---|
| **aliasing-sound safety** | `acheck_safe` | choice-free | a checked program never accesses a freed or unallocated cell *through any alias* — the invariant ties the checker's tracked addresses exactly to the runtime store |
| certified by `decide` | `asafe_of_check`, `alias_ok_runs` | choice-free | |
| **the witness brick 12 could not state** | `alias_uaf_errors`, `alias_uaf_rejected` | standard 3 / choice-free | `alloc p; copy q p; free p; access q` dangles `q` through the alias — errors at runtime *and* is rejected (exact aliasing catches it) |
| **copying is allowed** | `alias_ok_accepted` | choice-free | unlike linearity: `alloc p; copy q p; access q; free p` (use before free) is accepted and runs |

The advance over brick 12: `copy` is a first-class operation, and freeing a cell
invalidates *every* alias of it — the use-after-free-through-an-alias that
linearity could not even express is caught, precisely, for straight-line code.

## Heap safety under loops (`HeapLoop.lean`) — the fixed-point checker

Brick 20, the last hard structural direction: combining a heap with loops. Brick
19's memory safety was precise because allocation addresses are static in
*straight-line* code; a `while` allocates a runtime-variable number of cells, so
no static tracking survives. The discipline that does survive is a **loop
invariant**: the set of valid-pointer variables must be a *fixed point* of the
loop body. This combines brick 11's heap (high-water mark, wild access = error)
with brick 7's fuel semantics (`HRes = to | err | ok`; `to` = fuel-out/divergence,
`err` = memory error).

| result | Lean | axioms | content |
|---|---|---|---|
| **soundness by fuel induction** | `hlcheck_safe` | standard 3 | a checked program never returns `err` at any fuel (it may `to`), and every `ok` result preserves the invariant; the `while` case reuses the smaller-fuel IH for the body *and* the loop continuation, carrying the loop invariant across iterations |
| the fixed-point rule | `hlcheck` (`.loop` case) | — | `while e c` checks the body from `V` and requires `V ⊆ hlcheck V c` (the body preserves the tracked set), returning `V` |
| certified by `decide` | `safe_of_check`, `loopalloc_safe` | standard 3 | a loop that allocates and accesses fresh cells is accepted and never errors, at any fuel |
| **teeth** | `loop_wild_errors`, `loop_wild_rejected` | choice-free | a loop accessing an unallocated pointer errors and is rejected |

The technical crux is the `while` case: fuel induction with the loop continuation
applying the fuel-`k` IH to the *same* `while` command, at the *same* invariant
set `V` (because the checker's fixed-point rule returns `V`) — so the loop
invariant holds after any number of iterations. Honest limit: a high-water-mark
heap (no `free` under loops — combining `free`/aliasing with loops would need a
may-alias abstraction, a further brick).

## A real parser (`ParseSource.lean`) — from source text to a checked guarantee

Brick 21, a different kind of step: every prior brick analyzed a *hand-built*
AST; a real tool analyzes *source text*. A recursive-descent **parser** takes a
token stream (concrete syntax) and produces the AST, with the classic
parser-correctness theorem — parsing the printed form of any program recovers it
exactly. Composed with the taint checker's soundness, the injection guarantee
finally attaches to written source, not to a term the prover constructed.

The surface language is the injection/taint one: `input x`, `const x`,
`cat x y z`, `emit x`, `;`-separated.

| result | Lean | axioms | content |
|---|---|---|---|
| **parser correctness** | `parse_print` | choice-free | `parse (printS c) = some c` — the parser is a left inverse of the printer (round trip), by induction on the AST with `parseAtom_print` and a fuel bound |
| checker soundness | `scheck_ni` | choice-free | the taint checker's two-run noninterference (emitted output independent of untrusted input) |
| **end to end, on text** | `source_injection_free` | choice-free | *if a token stream parses and the checker accepts it, the emitted output is a function of the trusted program alone* — the security claim attaches to `parse toks`, not a hand-built AST |
| real-source witnesses | `unsafe_parses`/`unsafe_src_rejected`, `safe_parses`/`safe_src_injection_free` | choice-free | an injectable source token stream parses and is rejected; a safe one parses, is accepted, and is proved injection-free |

This is the bridge the whole security program was missing: a claim about *source
text*. Honest limit: the concrete syntax is a token list (no character lexer),
the grammar is small (fixed-arity atoms, `;`-sequencing) — a real recursive-descent
parser with a proved round trip, not a full language front-end.

## A lexer (`LexSource.lean`) — the source pipeline reaches characters

Brick 22 completes the front-end. Brick 21's parser starts from *tokens*; a real
front-end starts from a *character string*. The lexer adds the missing layer —
characters → tokens — with its own round-trip correctness, chaining
lexer + parser + checker into an end-to-end guarantee about an actual character
source.

| result | Lean | axioms | content |
|---|---|---|---|
| **lexer correctness** | `lex_print` | `propext` | `lex (toks.map printCh) = toks` — the lexer is a left inverse of the per-token printer (round trip) |
| whitespace | `lex_skip_space`, `spaced_lexes_same` | propext / **none** | spaces are skipped; the spaced and unspaced sources lex identically |
| **end to end, on characters** | `source_string_injection_free` | choice-free | a character source that lexes, parses, and checks is injection-free — the claim attaches to source *characters*, through `lex`/`parse`/`scheck` |
| real-character witnesses | `unsafe_chars_parse`/`unsafe_chars_rejected`, `safe_chars_*` | choice-free | `i0;t210;e2` lexes+parses to an injectable program and is rejected; `i0;c2;e2` is accepted and proved injection-free |

Together with brick 21 the whole chain **string → lex → parse → check → theorem**
is machine-checked, so the security claim attaches to source characters. Honest
limit: a small one-char-per-token alphabet (keywords `i c t e ;`, digit ids,
skipped spaces) — a clean lexer with a proved round trip, not a production
tokenizer.

## Free under loops (`FreeLoop.lean`) — the last hard combination

Brick 23 combines the two memory disciplines that never met: brick 12's
`free`-with-linearity and brick 20's fuel-indexed fixed-point loops. A `while`
whose body may `alloc` *and* `free` cells each iteration. Under loops the exact
addresses of brick 19 are gone, so `free` soundness rests entirely on brick 12's
**linearity** (distinct addresses ⟹ freeing one can't dangle another) — carried
now as a *loop invariant* through fuel induction.

| result | Lean | axioms | content |
|---|---|---|---|
| **soundness** | `flsafe` | standard 3 | fuel induction with a four-clause invariant (tracked ⟹ live, in-bounds, pairwise-distinct; freed ⟹ once-allocated); a checked program never hits a use-after-free, double-free, or wild access at any fuel |
| the `alloc; use; free` loop | `allocfree_loop_safe` | standard 3 | the realistic pattern — a loop that allocates a fresh cell, uses it, and frees it each iteration — is accepted and never errors |
| **use-after-free in the body** | `usefree_loop_errors`, `usefree_loop_rejected` | choice-free | `alloc; free; access` inside the loop errors and is rejected |
| **double-free across iterations** | `doublefree_loop_rejected` | choice-free | freeing an *invariant* pointer each iteration double-frees — the fixed-point rule rejects it (the body can't preserve the tracked set), exactly the cross-iteration double-free |

The `doublefree_loop_rejected` witness is where the two disciplines interlock:
the fixed-point rule (brick 20) is *precisely* what catches the double-free that
free (brick 12) introduces under loops — freeing a loop-invariant pointer means
the body shrinks the tracked set, so `V ⊆ flcheck V body` fails. Honest limit:
linearity forbids pointer *copying* — combining this with brick 19's aliasing
under loops would need a may-alias abstraction (a further brick).

## May-alias under loops (`AliasLoop.lean`) — the depth follow-on brick 23 named

Brick 24 lands the aliasing/free/loop intersection brick 23 deferred. Brick 19's
exact-address tracking dies under loops, so the checker abstracts the heap by a
**may-alias partition** of the live pointer variables (`List (List Var)` — no
addresses, no allocation counter, which could never be a loop fixed point).

| result | Lean | axioms | content |
|---|---|---|---|
| **soundness** | `alsafe` | standard 3 | fuel induction with a four-clause invariant whose core is the may-alias over-approximation *different class ⟹ different address*; `alloc` opens a fresh singleton class, `copy x y` puts `x` in `y`'s class, `free x` drops `x`'s whole class, the loop rule is the one-pass fixed point |
| **copy under loops, safe** | `alias_free_loop_safe` | standard 3 | the witness brick 23 could not state — a loop that allocates, *copies* (aliases), uses the alias, and frees — is accepted and never errors; linearity forbade the copy |
| **use-after-free via alias** | `alias_uaf_loop_rejected` | choice-free | free-then-access through the alias is a use-after-free, rejected |
| **double-free across iterations** | `doublefree_aliasloop_rejected` | choice-free | freeing an invariant pointer drops its class, so the body can't preserve the entry partition — rejected by the fixed point |

`free x` drops `x`'s *whole class*, killing every alias at once — sound because
any actual alias of `x` is in `x`'s class. Honest limit: the loop rule is
one-pass (a surviving alias across the back-edge is rejected, not iterated to a
fixed point).

## A richer alphabet (`LexReal.lean`) — multi-character tokens and maximal munch

Brick 25 closes brick 22's one-character-per-token limit: real two-letter keywords,
digit-run identifiers, whitespace separators, and a **maximal-munch** scanner.
The round trip (`lexR_printReal`) is re-proved against a printer that is no longer
injective on characters, and the same `parse`/`scheck` pipeline runs on top, so
`rich_source_injection_free` re-derives injection-freedom over the richer source.
Honest limit: identifier values are read as a run length, not yet decimal.

## A fuller query grammar (`QueryGrammar.lean`) — beyond one literal

Brick 26 generalizes brick 14's single-literal tokenizer argument to a template
with `n` literal slots parameterized by a value *vector*. `param_correct_N` (the
skeleton of the concatenated query equals the `n+1` structural pieces),
`param_immune_N` (skeleton independent of every value), and `concat_injectable_N`
(a quote in an arbitrary slot displaces the structure) — the same
data-not-structure discipline, now n-ary.

## A second real sink (`CmdInjection.lean`) — OS command injection (CWE-78)

Brick 27 re-runs brick 14/17's "make a channel real" method for a third sink with
a different metacharacter: a command string splits into an argv vector on the
**argument separator**, and `argv_correct`/`argv_immune` show argv-binding
(`execv(prog,[v])`) keeps the executed structure a function of the program alone,
while `cmd_concat_injectable` shows a separator inside a concatenated value injects
structure (`system("prog "+v)`). Command injection joins SQL injection and path
traversal as a made-real channel.

## Decimal identifiers (`DecimalId.lean`) — the codec brick 25 deferred

Brick 28 closes brick 25's one named residual: identifier *values* were read as a
run length, not decimal. The core is a **verified mathlib-free decimal codec** —
`toDigits` (well-founded on `n / 10`) and `ofDigits` (a base-10 fold) — with the
round trip `ofDigits_toDigits` (`ofDigits (toDigits n) = n`) proved by the
definition's own induction principle. The scanner reads a maximal run of decimal
digit characters and folds it (`spanDigits` + `ofDigits`); `lexD_printD` re-proves
the lexer round trip over the decimal alphabet, and `decimal_source_injection_free`
re-derives injection-freedom through the same `parse`/`scheck` pipeline. Witnesses
use genuine multi-digit ids (`12`, `45`), read as single numbers, not digit runs.

## Log injection (`LogInjection.lean`) — a third real sink (CWE-117)

Brick 29 adds a fourth made-real channel (after SQL injection, path traversal, and
command injection) with a fourth metacharacter: the **record separator** (a
newline). A log splits into records on newlines; the executed structure is the even
(structural) records. `field_correct`/`field_immune` show structured logging
(`log.info(event, field=value)`) keeps the executed structure a function of the
trusted preamble alone, while `log_concat_injectable` shows a newline inside a
concatenated field forges a record (`log.write(preamble+"\n"+field)`). Log injection
joins SQL injection, path traversal, and command injection under one discipline.

## Fixpoint may-alias (`AliasFix.lean`) — closing brick 24's one-pass loop rule

Brick 30 closes brick 24's named residual: its loop rule was *one-pass*, rejecting
alias-maintaining loops (`while (…) copy 1 0` with two live pointers) because one
body pass merges the entry classes. This brick infers a **coarsening invariant** by
iterating the body transfer to a fixed point. The semantic heart is `ALInv_coarsen`
(axiom-free): merging classes only weakens the may-alias over-approximation, so
`ALInv P → ALInv Q` for any coarsening `Q`. `loopFix` iterates, merging classes
until a preserved fixed point, `loopFix_correct` proves its partial correctness
(whatever it returns coarsens the entry and is preserved), and `loopFix_terminates`
proves convergence — each merge strictly shrinks the class count, so the search
reaches its final answer within `|P|+1` fuel and never diverges. `coarsen_loop_safe`
proves the loop safe
from the inferred invariant, reusing brick 24's `alsafe` for the body. The witness
`while (…) copy 1 0` is accepted (`maintain_loopFix` infers `[[1,0]]` by `decide`)
where brick 24 returns `none` (`brick24_rejects`). Completeness is **narrowed**, not
abandoned: the fully-merged partition (the lattice top) is always a valid coarsening
(`Coarsens_collapse`) and a fixed point exactly for alias-maintaining loops, so
`coarsen_loop_complete` proves any loop whose top is preserved is safe (heuristic-
independent) and `loopSearch_complete` proves the search — widened to the top — then
succeeds. Finally the **result is uncaged**: `alcheck2`/`alsafe2` fold the coarsening
loop rule into a full recursive checker, so a loop composed into a real program
(`seq`, code before and after) is checked and proved safe end to end — `prog_safe`
proves the whole program `alloc 0; alloc 1; while (…) copy 1 0` safe, not the loop in
isolation — and the checker is **mutually recursive** with the fixpoint iterator, so
nested loops get the fixpoint at arbitrary depth (`nested_prog_safe` proves
`… while (…) ( while (…) copy 1 0 )` safe). The mutual definition terminates on
`(sizeOf body, which-function, iteration-fuel)`; soundness is structural induction on
the command. Residual: loops whose *only* fixed point is a strict intermediate
coarsening.

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
