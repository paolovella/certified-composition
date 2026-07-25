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
| 3 | injection: SQLi/XSS/command (CWE-89/79/78) | taint = integrity NI on a real query skeleton; blacklist = value predicate | 1 / — | IN as flow (generated, real query); OUT-INADMISSIBLE as blacklist | [proved: T1, T2, + real] |
| 4 | improper declassification / overshare | bounded release (2-safety rel. φ) | 1 | IN (generated) | [proved] |
| 5 | privacy / differential privacy | hyperproperty (quantitative) | 3 | IN as f-DP invariant; OUT-NONCOMPOSABLE as (ε,δ) | [argued] / [proved in miniature] |
| 6 | memory safety (CWE-119/416) | safety of a richer (heap) semantics | — | IN-WITH-MODEL (generated); CARRIED cross-language | [proved] |
| 7 | authz bypass (CWE-285); cross-tenant isolation | 1-safety rel. policy; isolation is 2-safety | — / 1 | CARRIED; isolation IN (generated) | [classified] / [proved] |
| 8 | races / TOCTOU (CWE-362/367) | 1-safety over interleavings | — | OUT-OF-MODEL | [classified] |
| 9 | speculative execution (Spectre-class) | 2-safety over microarchitectural model | 1* | OUT-OF-MODEL | [classified] |
| 10 | resource exhaustion / DoS (CWE-400) | quantitative safety bound | — | REDUCIBLE (graded certificate) | [classified] |
| 11 | crypto misuse (CWE-327) | assumption-shaped; leakage side is #2 | — | LEDGER (mechanized) | [proved] |
| 12 | composition seams / supply chain | certificate loss at boundaries | — | IN-BY-DESIGN | [proved, end-to-end] |
| 13 | termination / progress leaks (CWE-385-adjacent) | 2-safety over a fuel-indexed semantics with loops | 1 | IN-WITH-MODEL (generated) | [proved] |
| 14 | path traversal (CWE-22) | untrusted structure in a filesystem-path sink | 1* | IN (real; safe-by-construction) | [proved] |

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
**Extended to the heap** (brick 13, `HeapFlow.lean`): noninterference now covers a
labeled heap — the observable is the store *and* the Low heap region, and
`hsecTy_ni` (choice-free) proves a typed program never leaks a High cell into a
Low variable. This is the unification point with the memory-safety sub-project
(rows 6, 11–12): confidentiality and memory safety as two independent, composable
invariants of one heap machine. Witness `heap_leak`/`leak_rejected`: a Low load of
a High cell leaks and is rejected. **Generalized past binary** (brick 18,
`LatticeFlow.lean`): the whole confidentiality core rests on a binary
`Partition : String → Bool` — the two-point lattice. `latSecTy_ni` proves
noninterference over an *arbitrary* security lattice for *every* observer level
(the classic Denning model); the diamond lattice `⊥ < a, b < ⊤`
(`dmdLat`) and the cross-compartment witness (`crosscompartment_leaks` /
`_untypable`) exhibit two mutually-incomparable secret compartments — a guarantee
the binary model cannot even state. Binary High/Low is the two-point instance.

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
safe. And declassified timing is now covered too (brick 6, `SecTyTD.lean`): a
secret branch whose bit is *declared released* type-checks (`iteD`), and
`secTyTD_sound` certifies the whole outcome reveals at most the ledger `relOf P c`
— `ReleasesAtMost c (outO P) P (relOf P c)`. The money theorem `ptime_timing_released`
turns the brick-5-rejected `Ptime` into a bounded, declared release: under one guard
permit its running time reveals at most the secret bit (`ptime_wall_of_bit`).
`secCheckT` closes the clock by construction; `secCheckTD` opens it exactly as far as
declared. No open honesty gap remains on this row — the only uncovered timing is
*microarchitectural* (row 9, OUT-OF-MODEL).

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

**Generated** (brick 3): since taint-freedom is `J_NI` at the untrusted relabeling
and the checker generates `J_NI`, the taint certificate is checker output at the
relabeled partition — the same `secCheck` under `P := untrusted`.

**Made real** (brick 14, `InjectionReal.lean`): the earlier caveat "IMP has no
strings; this is the property shape, not a model of SQL" is now closed for the core
mechanism. A query is a character string with a real tokenizer where a quote `'`
toggles in/out of a string literal (the actual SQLi mechanism); the *skeleton*
(structural segments) is the executed command, and injection is untrusted data
changing it. `concat_injectable` (axiom-free) proves string concatenation is
injectable — a benign value and an injection payload `' R` give different skeletons
(`' OR …` as a theorem); `param_immune`/`param_noninterference` (axiom-free) prove
**parameterization is injection-safe by construction** — the executed structure is
independent of the untrusted value — and `param_correct` proves it computes the
intended structure for benign input. This is exactly T1's integrity-NI form, now on
a real query construction, with the industrial fix (prepared statements) proved
correct. Still short of a full SQL grammar (one quote-delimited literal, not the
whole language), but the channel is no longer a shape — the real attack and the
real defense are theorems.

**Connected to a running program** (brick 15, `QueryProgram.lean`): a
flow-sensitive **taint checker** over a string-manipulating language (input,
literals, concatenation, and query-emit sinks). `qcheck_ni` (choice-free) proves
soundness as two-run noninterference — a checked program emits the same query
structure for *every* untrusted input (`injection_free_of_check`) — and
`unsafe_rejected`/`unsafe_leaks` witness a concatenated-tainted query being both
rejected and genuinely leaking, while the parameterized program passes
(`safe_accepted`). This is the shape of a real SQL-injection static analyzer, with
what it accepts proved un-injectable. Honest limit: a small language and brick
14's single-literal query mechanism.

**Attached to source text** (brick 21, `ParseSource.lean`): the analyses so far
ran on hand-built ASTs. A recursive-descent **parser** with a proved round-trip
correctness theorem (`parse_print`: `parse (printS c) = some c`) takes a token
stream to the AST, so the injection guarantee attaches to *written source* —
`source_injection_free`: if a token stream parses and the taint checker accepts
it, the emitted output is a function of the trusted program alone. Witnesses
(`unsafe_parses`/`unsafe_src_rejected`, `safe_parses`/`safe_src_injection_free`)
run the whole pipeline on real source token streams. **Down to characters** (brick
22, `LexSource.lean`): a **lexer** with its own round-trip correctness (`lex_print`:
`lex (toks.map printCh) = toks`, skipping whitespace) completes the front-end, so
the full chain **string → lex → parse → check → theorem** is machine-checked.
`source_string_injection_free` attaches the guarantee to source *characters*;
witnesses (`unsafe_chars_parse`/`_rejected`, `safe_chars_*`) run the whole pipeline
on a character string like `i0;t210;e2`. Honest limit: a one-char-per-token
alphabet, not a production tokenizer.

**Stored / second-order injection** (brick 16, `DbInjection.lean`): the sharpest
missed class. Untrusted data written to the database in one request, read back in
a later one, concatenated into a query. The machine gains a persistent store, and
the result is a *soundness* statement about the analysis itself: a **naive**
checker treating database reads as clean *accepts* a stored-injection program that
genuinely leaks (`naive_accepts_stored` + `stored_injection_leaks`, the latter
axiom-free) — it is unsound — while the **sound** checker tracks taint *per cell*
and rejects it (`sound_rejects_stored`), with `dbcheck_ni` (choice-free) proving
acceptance means injection-free across the persistence boundary. The moral as a
theorem: injection-freedom does not survive persistence unless taint does — the
framework catches a class real analyzers routinely miss.

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

### 3.6 Memory safety — IN-WITH-MODEL, generated [proved]; CARRIED cross-language

Brick 1 filed this CARRIED: loop-free IMP has no heap, so memory safety could only
be *transported* (a Boolean certificate with trivial `mul` riding `Bridge.comp` and
the ledger), never *generated*. Brick 11 (`conf-typing/ConfTyping/MemSafe.lean`,
built, `no sorry`, axiom-audited) grows the model and generates it. The machine has
a heap and an allocation high-water mark `n`; `mexec` returns `Option MState` with
`none` a **memory error** (a wild dereference), and a flow-sensitive checker
`mcheck` tracks which variables hold in-bounds addresses. Soundness `mcheck_safe`
is memory-safety *by construction*: a checked program **never** hits a memory
error, proved by induction on an invariant tying the tracked set to the heap's live
region. Teeth: a store through an unallocated pointer errors at runtime
(`mwild_store_errors`) and is rejected by the checker (`mwild_rejected`) — they
agree. So "no undefined behavior" is now checker-generated for the heap model, not
merely carried; the cross-language transport story (an *external* engine's
certificate riding the seam) remains for models this machine does not cover.
Brick 12 (`MemFree.lean`) adds the sharpest case — **use-after-free** (CWE-416):
a richer machine with a liveness map and a `free` operation, and a **linearity**
checker (tracked pointers hold distinct live addresses) whose soundness
`fcheck_safe` rules out use-after-free *and* double-free by construction. Teeth:
`alloc p; free p; store p` errors and is rejected (`uaf_errors`/`uaf_rejected`),
as is a double-free (`double_free_errors`/`double_free_rejected`). **Pointer
aliasing** (brick 19, `AliasSafe.lean`) drops brick 12's linearity restriction:
brick 12 kept `free` sound only by *banning* pointer copies (so no two tracked
pointers aliased). Real code copies pointers, and freeing one dangles the others.
The tractable-and-precise fix: in a loop-free program the allocation addresses are
statically determined, so the checker tracks the *exact* address each pointer
holds (a must-alias analysis); `copy` propagates the address, `free` marks it
freed, and an access through *any* alias of a freed address is rejected.
`acheck_safe` (choice-free) is the soundness; `alias_uaf_errors`/`alias_uaf_rejected`
witness `alloc p; copy q p; free p; access q` — a use-after-free *through the alias
`q`*, which brick 12 could not even express — caught, while `copy` is now allowed
(`alias_ok_accepted`). **Heap safety under loops** (brick 20, `HeapLoop.lean`):
combining brick 11's heap with brick 7's fuel-indexed loops (`HRes = to | err |
ok`). Under `while`, allocation addresses are no longer static, so exact tracking
gives way to a **fixed-point** discipline: the loop body must preserve the
valid-pointer set (`V ⊆ hlcheck V c`). `hlcheck_safe` (fuel induction — the
`while` case reuses the smaller-fuel IH for body and continuation) proves a checked
program never memory-errors at any fuel; `loop_wild_errors`/`_rejected` witness a
loop accessing an unallocated pointer. **Free under loops** (brick 23,
`FreeLoop.lean`): the last hard combination — brick 12's `free`-with-linearity
meets brick 20's fixed-point loops. Under loops the exact addresses of brick 19
are gone, so `free` soundness rests on linearity (distinct addresses), carried as
a loop invariant through fuel induction (`flsafe`, four-clause invariant). The
realistic `alloc; use; free` loop is safe (`allocfree_loop_safe`); use-after-free
in the body is caught (`usefree_loop_errors`/`_rejected`); and — the interlock —
the fixed-point rule catches the **double-free across iterations**
(`doublefree_loop_rejected`): freeing a loop-invariant pointer shrinks the tracked
set, so the body can't preserve it. Follow-on: aliasing (`copy`) *under* loops
needs a may-alias abstraction.

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
- **Over loops** (brick 8, `WhileCompose.lean`): the seam holds for the looping
  language too — `WOutNI_seq` (choice-free) composes certified looping components,
  with divergence threading through the boundary in lockstep (a clause the
  loop-free seam did not need), and `wleak_poisons_seam` proving the upstream
  hypothesis load-bearing there as well. The ledger is ported too (brick 9,
  `WhileLedger.lean`: `WCondBoundary_seq` accumulates trusted bases over the
  looping seam, and `wledger_no_silent_discharge` witnesses an assumption that
  guards the *termination* channel), and so is the **Bridge reception** (brick
  10, `WhileBridge.lean`): the exact reception `Bridge.ofWComponent` is
  axiom-free and composes by the generic `Bridge.comp`, and `wbridge_iff_sound`
  shows termination-sensitive security *is* a contraction with the halting query
  a first-class coordinate of the distance. The looping language now carries the
  full discipline — soundness, seam, ledger, reception.

Still conditional in exactly one honest place: *if* each component carries a
certificate, composition preserves and accumulates it; generating per-component
certificates is the other rows' business. The assumption-*ledger* certificate
(composite trusted base computed as the append of component ledgers) — deferred here
in brick 2 — is **delivered in brick 4** (`Ledger.lean`, `LedgerBridge.lean`):
`CondBoundary`/`CondReleases` carry the base, `condBoundary_seq` and
`ledgerBridge_comp_ledger` accumulate it by the same composition law, and
`ledger_no_silent_discharge` proves it can never be laundered into evidence. See
row 11.

### 3.13 Termination / progress leaks — IN-WITH-MODEL, generated [proved]

The channel that only exists once the language has loops. A `while` on a secret
guard loops forever iff a secret bit is set, so the *fact of halting* leaks the
bit — invisibly to any analysis that only inspects terminating runs (store,
timing, everything in bricks 1–6). Brick 7 (`conf-typing/ConfTyping/WhileImp.lean`,
built, `no sorry`, axiom-audited) grows the model to cover it:

- a **fuel-indexed semantics** `wexec : Nat → WCmd → Store → Option Outcome`
  (total by recursion on fuel; `none` is how non-termination appears), with
  `optLowEq` making a `none`/`some` mismatch — divergent halting — a leak;
- **termination-sensitive soundness** `wsecTy_sound` (choice-free): a Low-guarded
  discipline (no secret-guarded loops or branches) makes two Low-equal runs
  lockstep at every fuel — same halting, store, time, and trace;
- **the witness** `wleak_leaks`/`wleak_rejected`: `while b skip` halts iff `b=0`,
  and at one fuel one run halts while the other spins — noninterference genuinely
  fails, and `wcheck` rejects the program (axiom-free). Checker and semantics
  agree the channel is real;
- **the model grew, it did not fork** — `wexec_embed_eq` (choice-free): every
  loop-free `Cmd` embeds into `WCmd` and, with enough fuel, `wexec` computes
  exactly the total `eval`; the whole six-brick program is this one's loop-free
  fragment.

Honest scope: this certifies termination-*insensitivity* (secret-guarded loops
rejected, not repaired); declassified termination is the Policy analogue, a later
brick. The **seam is now ported to loops** (brick 8, `WhileCompose.lean`):
certified looping components compose (`WOutNI_seq`, choice-free), with the clause
the loop-free seam never had — if the upstream diverges, the composite diverges in
lockstep, so the termination channel stays closed across the boundary — and the
teeth (`wleak_poisons_seam`) show the upstream hypothesis load-bearing. The ledger
and Bridge reception over `WCmd` remain follow-on (the query-distance metric needs
a termination coordinate).

### 3.14 Path traversal — IN, real, safe-by-construction [proved]

Added by brick 17 (`PathTraversal.lean`) to show the depth *method* generalizes:
injection (rows 3, 14 in the arc) is one instance of "untrusted data changing the
meaning of a structured sink"; path traversal (CWE-22) is another — an untrusted
filename with `..` escapes the base directory. A path input is a list of steps
(`down`/`up`); resolution against a base either stays contained or escapes.
`traversal_escapes` (choice-free) proves `foo/../../` escapes — `../../etc/passwd`
as a theorem. `flat_contained` proves a `..`-free input stays contained (untrusted
*names* can't escape, only untrusted *structure* can). The by-construction fix is
`openLeaf` (an API taking a leaf name, not a path — the path-analog of a bound
parameter, `openLeaf_contained` axiom-free), and the runtime check "reject `..`"
is sound (`pathCheck_sound`). Same shape as parameterized queries; this is breadth
of the depth method — a second real, named class made real. Honest limit: an
abstract step-list, not a real filesystem/OS path parser.

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

### Brick 6 ledger (declassified timing)

- `SecTyTD.lean` — the Policy analogue of the clock. A secret branch is allowed
  when its bit is *declared released* (`iteD`, the brick-3 budget `Δ` over the
  timing checker), and `secTyTD_sound` (choice-free) certifies the whole outcome
  reveals at most the ledger `relOf P c` — `ReleasesAtMost c (outO P) P (relOf
  P c)`. Money theorem: `ptime_timing_released`/`ptime_wall_of_bit` — the
  brick-5-rejected `Ptime`, under one declared permit, has its running time bounded
  to the secret bit. Executable `secCheckTD` by `decide`; `ptime_rejected_TD`
  matches brick 5 under an empty budget. Row 2's honesty gap fully closed (only
  microarchitectural timing, row 9, stays OUT-OF-MODEL); guard 1c extended.
  **Brick 6 complete.**

### Brick 7 ledger (loops and the termination channel)

- `WhileImp.lean` — the model grows past loop-free IMP. A fuel-indexed evaluator
  `wexec` (total on fuel, `none` = non-termination), the termination channel
  (`optLowEq`), termination-sensitive soundness `wsecTy_sound` (choice-free),
  the executable `wcheck`, and the termination-leak witness
  `wleak_leaks`/`wleak_rejected` (`while b skip`, halting = the secret bit). The
  loop-free fragment embeds faithfully (`wexec_embed_eq`, choice-free): the prior
  six bricks are this development's loop-free part. New map row 13 (termination
  leaks), IN-WITH-MODEL (generated); guard 1c extended, guard 1i added. Follow-on,
  named: porting the seam/ledger/Bridge reception to `WCmd`, and declassified
  termination. **Brick 7 core complete.**

### Brick 8 ledger (the seam over loops)

- `WhileCompose.lean` — the composition differentiator, ported from loop-free
  `Cmd` to the looping language. Boundary certificate `WOutNI c P` (full fuelled
  outcome, termination-sensitive), manufactured by the checker
  (`WOutNI_of_wcheck`); the seam `WOutNI_seq` (choice-free) composes certified
  looping components with **divergence threading through the boundary in
  lockstep** — the clause the loop-free seam never had; `wok_pipeline_certified`
  a two-`decide` certified pipeline; teeth `wleak_poisons_seam`. Guard 1c
  extended, guard 1j added. Follow-on, named: the ledger and Bridge reception
  over `WCmd`. **Brick 8 complete.**

### Brick 9 ledger (the assumption ledger over loops)

- `WhileLedger.lean` — brick 4's trusted-base discipline ported to the looping
  language (reusing the `Sat`/`Ledger` infrastructure; the certificate becomes
  the termination-sensitive `WOutNI`). `WCondBoundary_seq` (choice-free)
  accumulates bases by union through the looping seam; discharge is explicit; and
  `wledger_no_silent_discharge` is the sharpest form of the discipline — its
  witness `while x skip` rests on a trust assumption about its guard `x`, so
  dropping the assumption is a *halting* leak. Guard 1c extended, guard 1k added.
  Follow-on, named: the Bridge reception over `WCmd`. **Brick 9 complete.**

### Brick 10 ledger (the Bridge reception over loops)

- `WhileBridge.lean` — the last unported piece, with real design content. The
  looping boundary is *partial*, so the carrier lifts to `OStore := Option Store`
  (`none` = diverged) and the distance gains a **halting query** `haltQ` — making
  termination an observable *in the metric*. The exact reception
  `Bridge.ofWComponent` is **axiom-free** and composes by the generic
  `Bridge.comp` (`ofWComponent_comp_map`/`_cert`); the equivalence
  `wbridge_iff_sound` proves termination-sensitive security = the `wNIBound`
  contraction on halting inputs; and `wOutNI_contracts` lands every checked
  looping component in the interface. Guard 1c extended, guard 1l added. Honest
  scope: the security contraction is on halting input pairs; the diverged-upstream
  (`none`) regime is covered only by the exact Bridge. **Brick 10 complete — the
  looping language now has soundness, seam, ledger, and reception.**

### Brick 11 ledger (heap and memory safety — a new kind of property)

- `MemSafe.lean` — the first brick of the memory-safety sub-project, and the
  first *safety* property (vs. the confidentiality channels of bricks 1–10). A
  heap machine whose `mexec` can get stuck (`none` = memory error), and a
  flow-sensitive checker `mcheck` tracking in-bounds pointer variables. Soundness
  `mcheck_safe`: a checked program never errors, by induction on a heap invariant.
  Teeth `mwild_store_errors`/`mwild_rejected` (choice-free). Row 6 moved CARRIED →
  IN-WITH-MODEL (generated). Guard 1c extended, guard 1m added. Follow-on:
  `free`/use-after-free, heap loops, information flow through the heap. **Brick 11
  complete.**

### Brick 12 ledger (free and use-after-free)

- `MemFree.lean` — the memory-safety sub-project's sharpest witness. A machine
  with a liveness map that can *shrink* the live set (a `free` operation), and a
  **linearity** checker (`FInv`: tracked pointers live, in-bounds, pairwise
  distinct) whose soundness `fcheck_safe` rules out use-after-free and double-free
  by construction. Teeth: `uaf_errors`/`uaf_rejected` and
  `double_free_errors`/`double_free_rejected` (choice-free). Row 6's generated
  verdict now covers UAF. Guard 1c extended, guard 1n added. Follow-on: pointer
  copying with alias tracking, heap loops, heap information flow. **Brick 12
  complete.**

### Brick 13 ledger (information flow through the heap — the unification)

- `HeapFlow.lean` — where the two halves meet. Noninterference over a labeled
  heap: the observable is store + Low heap region, and `hsecTy_ni` (choice-free)
  proves a typed program never leaks a High cell into a Low variable. The type
  system `HSecTy` adds heap rules (`storeL`/`loadL` for Low regions,
  `storeH`/`loadH` for High) to the pc-label discipline; confinement `hconfine`
  handles the High-context case. Teeth `heap_leak`/`leak_rejected`. Memory
  *safety* (rows 6, 11–12) and this *information-flow* property are independent,
  composable invariants of one heap. Rows 1 and 6 both cite it. Guard 1c
  extended, guard 1o added. **Brick 13 complete — the confidentiality and memory
  disciplines unified over one machine.**

### Brick 14 ledger (injection made real)

- `InjectionReal.lean` — the depth step: one channel made real. A query is a
  character string with a real quote-toggling tokenizer; the skeleton (structural
  segments) is the executed command. `concat_injectable` (axiom-free) — string
  concatenation is injectable (`' OR …` as a theorem); `param_immune` /
  `param_noninterference` (axiom-free) — parameterization is injection-safe by
  construction; `param_correct` — it computes the intended structure for benign
  input. The real attack and the real fix (prepared statements), proved,
  connected to T1's integrity-NI. Row 3 → "+ real". Guard 1c extended, guard 1p
  added. Honest limit: one quote-delimited literal, not a full SQL grammar.
  **Brick 14 complete.**

### Brick 15 ledger (injection in a running program)

- `QueryProgram.lean` — the taint-flow linter, connecting brick 14's query
  mechanism to an actual program. A string-manipulating language with a
  flow-sensitive taint checker `qcheck`; soundness `qcheck_ni` (choice-free) is
  two-run NI of the emitted queries, `injection_free_of_check` the top-level
  guarantee. Witnesses `unsafe_rejected`/`unsafe_leaks` (a concatenated tainted
  query caught and shown to leak) and `safe_accepted` (parameterized passes).
  The closest the artifact gets to a real static analyzer, with acceptance proved
  sound. Guard 1c extended, guard 1q added. Honest limit: small language,
  single-literal query mechanism. **Brick 15 complete.**

### Brick 16 ledger (stored / second-order injection)

- `DbInjection.lean` — persistent taint. A machine with a database (`dbwrite`/
  `dbread`) and a per-cell taint checker. The centerpiece is a soundness
  statement about the *analysis*: `naive_accepts_stored` (a per-request checker
  accepts the stored-injection program), `stored_injection_leaks` (axiom-free — it
  leaks through the DB), `sound_rejects_stored` (per-cell taint catches it), and
  `dbcheck_ni` (choice-free — the sound checker is injection-free across
  persistence). Proves the per-request shortcut unsound and the per-cell
  discipline necessary. Guard 1c extended, guard 1r added. **Brick 16 complete.**

### Brick 17 ledger (path traversal — the method generalizes)

- `PathTraversal.lean` — the "make a channel real" method applied to a *second*
  named class (CWE-22), not another injection variant. `traversal_escapes`
  (choice-free, the `../../` attack), `flat_contained` (safe when `..`-free),
  `openLeaf`/`openLeaf_contained` (axiom-free, the leaf-name fix — path-analog of
  a bound parameter), `pathCheck_sound` (the "reject `..`" check is sound). New
  map row 14; the map now covers 14 classes. Guard 1c extended, guard 1s added.
  Honest limit: abstract step-list, not a real OS path parser. **Brick 17
  complete.**

### Brick 18 ledger (a security label lattice — past binary High/Low)

- `LatticeFlow.lean` — generalizes the foundational abstraction from binary
  `Partition` to an arbitrary `SecLat`. `latSecTy_ni` (standard axioms):
  noninterference for any lattice and any observer level (Denning); `latConfine`
  (propext) the confinement lemma; `dmdLat` the diamond lattice (not a chain);
  and the cross-compartment witness (`crosscompartment_untypable`/`_leaks`,
  propext) — two mutually-incomparable secret compartments, unstatable in the
  binary model. Binary High/Low = the two-point instance. Guard 1c extended,
  guard 1t added. **Brick 18 complete — the deepest single generalization of the
  confidentiality core.**

### Brick 19 ledger (pointer aliasing — use-after-free through an alias)

- `AliasSafe.lean` — the hard memory extension, dropping brick 12's no-copy
  linearity. Exact-address tracking (allocation addresses are static in
  straight-line code → a must-alias analysis): `copy` propagates the address,
  `free` marks it freed, and access through *any* alias of a freed address is
  rejected. `acheck_safe` (choice-free) the aliasing-sound soundness;
  `alias_uaf_errors`/`alias_uaf_rejected` the use-after-free-through-an-alias
  witness brick 12 could not state; `alias_ok_accepted` shows `copy` is now
  allowed. Guard 1c extended, guard 1u added. Honest limit: exact tracking is
  precise for straight-line code; loops would need weaker may-alias. **Brick 19
  complete.**

### Brick 20 ledger (heap safety under loops — the fixed-point checker)

- `HeapLoop.lean` — the last hard structural direction: brick 11's heap meets
  brick 7's fuel-indexed loops. Under `while` the allocation addresses aren't
  static, so exact tracking is replaced by a loop-invariant **fixed point**: the
  body must preserve the valid-pointer set (`V ⊆ hlcheck V c`). `hlcheck_safe`
  (fuel induction, the `while` case reusing the smaller-fuel IH for body and
  continuation, carrying the invariant across iterations) — a checked program
  never memory-errors at any fuel; `loopalloc_safe` (a loop allocating fresh
  cells is safe), `loop_wild_errors`/`_rejected` (an unallocated access caught).
  Guard 1c extended, guard 1v added. Honest limit: high-water-mark heap (no `free`
  under loops yet). **Brick 20 complete.**

### Brick 21 ledger (a real parser — source text to a checked guarantee)

- `ParseSource.lean` — the bridge the program was missing: a claim about *source
  text*, not a hand-built AST. A recursive-descent parser with the classic
  round-trip correctness theorem `parse_print` (`parse (printS c) = some c`,
  choice-free), the taint checker's `scheck_ni`, and the end-to-end
  `source_injection_free` chaining them: a token stream that parses and checks is
  injection-free. Witnesses run the whole pipeline on real source token streams.
  Guard 1c extended, guard 1w added. Honest limit: token-list concrete syntax (no
  character lexer), small grammar. **Brick 21 complete.**

### Brick 22 ledger (a lexer — the pipeline reaches characters)

- `LexSource.lean` — completes the front-end: characters → tokens. `lex_print`
  (propext) the lexer round trip, `lex_skip_space`/`spaced_lexes_same` (whitespace
  skipped), and `source_string_injection_free` (choice-free) attaching the
  guarantee to a character source through the full `lex`/`parse`/`scheck`
  pipeline. Witnesses run the whole chain on a character string. With brick 21 the
  chain string → lex → parse → check → theorem is machine-checked. Guard 1c
  extended, guard 1x added. Honest limit: one-char-per-token alphabet. **Brick 22
  complete.**

### Brick 23 ledger (free under loops — the last hard combination)

- `FreeLoop.lean` — the two memory disciplines that never met: brick 12's
  `free`-with-linearity and brick 20's fixed-point loops. `flsafe` (fuel
  induction, four-clause linearity invariant) — a checked program never hits a
  use-after-free/double-free/wild access at any fuel. `allocfree_loop_safe` (the
  `alloc; use; free` loop), `usefree_loop_errors`/`_rejected` (UAF in body), and
  the interlock `doublefree_loop_rejected` — the fixed-point rule catches the
  cross-iteration double-free that free introduces under loops. Guard 1c
  extended, guard 1y added. Honest limit: linearity forbids pointer copying
  (aliasing-under-loops needs may-alias). **Brick 23 complete — every hard
  combination landed.**

### Brick 24 ledger (may-alias under loops — the depth follow-on brick 23 named)

- `AliasLoop.lean` — the aliasing/free/loop intersection brick 23 deferred by
  name. Brick 19's exact-address tracking dies under loops, so the checker
  abstracts the heap by a **may-alias partition** of the live pointer variables
  (a `List (List Var)` — no addresses, no allocation counter that could never be
  a loop fixed point). `alsafe` (fuel induction, four-clause invariant whose core
  is the may-alias over-approximation *different class ⟹ different address*) — a
  checked program never hits a use-after-free/double-free/wild access at any
  fuel. `alloc` opens a fresh singleton class, `copy x y` puts `x` in `y`'s
  class, `free x` drops `x`'s **whole class** (killing every alias at once),
  `access x` needs `x` classed; the loop rule is the one-pass fixed point (the
  body must preserve every entry class). `alias_free_loop_safe` — the witness
  brick 23 could not state: a loop that allocates, **copies**, uses the alias,
  and frees is accepted and safe (linearity forbade the copy).
  `alias_uaf_loop_rejected` (free-then-access an alias) and
  `doublefree_aliasloop_rejected` (invariant-pointer free) are the interlocks.
  Honest limit: the loop rule is one-pass (a surviving alias across the back-edge
  is rejected, not iterated to a fixed point). **Brick 24 complete — the last
  memory-safety follow-on landed.**

### Brick 25 ledger (a richer alphabet — multi-character tokens, maximal munch)

- `LexReal.lean` — brick 22's honest limit was one character per token. This
  brick makes lexemes multi-character: real two-letter keywords, identifiers as
  digit *runs*, whitespace separators, and a **maximal-munch** scanner, with the
  round trip (`lexR_printReal`) re-proved against a printer that is no longer
  injective on characters (the separators and run lengths carry the boundaries).
  The security claim survives the richer surface: the same `parse`/`scheck`
  pipeline runs on top, so `rich_source_injection_free` re-derives injection-
  freedom over a real, whitespace-delimited character source. Honest limit:
  identifier values are read as a run length, not yet decimal. **Brick 25
  complete.**

### Brick 26 ledger (a fuller query grammar — beyond one literal)

- `QueryGrammar.lean` — brick 14 made injection real on the smallest grammar
  (one quote-delimited literal). This brick generalizes the tokenizer argument to
  a template with **`n` literal slots** parameterized by a value *vector*.
  `param_correct_N` (skeleton of the concatenated query equals the `n+1`
  structural pieces, proved by induction over the interleaving with brick 14's
  `segs_append_q`) and `param_immune_N` (skeleton independent of every value);
  `concat_injectable_N` — a quote in an arbitrary slot displaces the structure.
  Same data-not-structure discipline, now n-ary. **Brick 26 complete.**

### Brick 27 ledger (a second real sink — OS command injection, CWE-78)

- `CmdInjection.lean` — brick 17 showed "make a channel real" is not injection-
  specific by re-running it for path traversal; this adds a third real sink with
  a different metacharacter. A command string splits into an argv vector on the
  **argument separator**; the executed structure is the even (structural) argv
  positions. `argv_correct`/`argv_immune` — argv-binding (`execv(prog,[v])`) keeps
  the executed structure a function of the program alone; `cmd_concat_injectable`
  — a separator inside a concatenated value injects structure (`system("prog "+v)`).
  Integrity NI with a real command sink, closing one of the "more sink classes"
  follow-ons. **Brick 27 complete — command injection joins SQL and path
  traversal as a made-real channel.**

### Brick 28 ledger (decimal identifiers — the codec brick 25 deferred)

- `DecimalId.lean` — brick 25's named residual: identifier values were a run
  length, not decimal. This brick adds a **verified decimal codec** — `toDigits`
  (well-founded on `n / 10`) and `ofDigits` (a base-10 fold), with the round trip
  `ofDigits_toDigits` (`ofDigits (toDigits n) = n`) proved by the definition's own
  induction principle — and a maximal-munch scanner that reads a run of decimal
  digit characters and folds it (`spanDigits` + `ofDigits`). `lexD_printD`
  re-proves the lexer round trip over the decimal alphabet, and
  `decimal_source_injection_free` re-derives injection-freedom through the same
  `parse`/`scheck` pipeline over a multi-digit-identifier source (witness ids
  `12`, `45`, read as single numbers, not digit-by-digit). Brick 25's residual is
  closed. **Brick 28 complete.**

### The security program, standing state (twenty-eight bricks, fifteen classes)

The original goal — a framework for coding inherently free of vulnerabilities —
now has: a **map** with a proved boundary (13 classes, brick 1 + brick 7's new
channel); a **seam** so guarantees survive composition in the transport interface
(brick 2); a **checker** so the certificates come from a decidable syntactic
check, not hand proof (brick 3); a **ledger** so the assumptions a guarantee rests
on are tracked, unioned under composition, and never silently laundered into
evidence (brick 4); a **timing-sensitive checker** so the clock is a certified
channel (brick 5); **declassified timing** so a secret branch can be
declared-and-bounded rather than only forbidden (brick 6); and **loops with a
termination channel** so a language with unbounded iteration is covered and the
halting-leak class is closed by construction (brick 7); and **the seam ported to
loops** so certified looping components compose with divergence threading through
the boundary (brick 8); and **the assumption ledger ported to loops** so a
looping guarantee's trusted base accumulates under composition and its
no-silent-discharge witness guards the halting channel (brick 9); and **the
Bridge reception ported to loops** so termination-sensitive security is a
contraction in the transport interface with halting a coordinate of the distance
(brick 10) — the looping language now carries the full discipline; and **heap
memory safety generated** so the first non-confidentiality property — a safety
property of a stuck-able machine — is proved by construction, not merely carried
(brick 11); **use-after-free ruled out** so the sharpest heap bug — a dereference
of a freed cell — is closed by a linearity checker (brick 12); and **information
flow unified with memory** so noninterference now holds over a labeled heap and
the confidentiality and memory disciplines meet on one machine (brick 13); and
**injection made real** so the property shape becomes an actual query with a real
tokenizer, the real attack (quote-breaking) and the real fix (prepared statements)
proved (brick 14); and **injection caught in a running program** so a
flow-sensitive taint checker over a string-manipulating language rejects the
injectable sink with acceptance proved sound (brick 15); and **stored injection
caught** so per-cell taint over a persistent store rejects second-order injection
and the per-request shortcut is proved unsound (brick 16); and **the method
generalized** so path traversal (CWE-22) is made real with the same
attack/safe-by-construction shape, showing "make a channel real" is not
injection-specific (brick 17); and **the confidentiality core generalized past
binary** so noninterference holds over an arbitrary security lattice with
mutually-incomparable compartments, not just High/Low (brick 18); and **pointer
aliasing handled** so use-after-free through an alias is caught by exact-address
tracking, dropping brick 12's no-copy restriction (brick 19); and **heap safety
under loops** so a fixed-point (loop-invariant) checker keeps memory safety sound
when allocation addresses stop being static (brick 20); and **a real parser** so
the injection guarantee attaches to source *text* — a recursive-descent parser
with a proved round trip, chained through the checker to an end-to-end source-level
theorem (brick 21); and **a lexer** so the front-end reaches characters — the full
chain string → lex → parse → check → theorem is machine-checked (brick 22); and
**free under loops** so `free` and unbounded iteration coexist soundly via
linearity carried as a loop invariant, with the fixed-point rule catching the
cross-iteration double-free (brick 23); and **may-alias under loops** so `copy`
and `free` and unbounded iteration coexist soundly via a may-alias partition, the
depth follow-on brick 23 named (brick 24); and **a richer alphabet** so lexemes
span several characters under a maximal-munch scanner with a proved longest-match
round trip (brick 25); and **a fuller query grammar** so parameterization is
proved injection-safe over a template with `n` literal slots (brick 26); and **a
second real sink** so OS command injection (CWE-78) joins SQL injection and path
traversal as a made-real channel by the same data-not-structure discipline (brick
27). What "bulletproof" means is stated at
proved strength, the flow-property classes are excluded *by type-checking* (store,
clock, termination, and heap — closed, declared, or non-leaking), noninterference
holds over an arbitrary label lattice, memory safety (including use-after-free
through aliases, double-free, wild access under loops, free under loops, and
aliasing via `copy` under loops) is
generated for the heap model, injection is proved on a real query (single- and
multi-literal), caught in a
running program (first- and second-order) by a sound taint checker, and attached to
a parsed and lexed character source over a multi-character alphabet with real
decimal identifiers (a verified codec), path traversal
and OS command injection are closed by the same
data-not-structure discipline, composition is certificate accumulation by the same
law that composes contraction estimates, and every guarantee carries its trusted
base as an automatic bill of materials. The honest edges are all named as theorems
or deferrals: microarchitecture stays OUT-OF-MODEL, `(ε,δ)`-DP stays
OUT-NONCOMPOSABLE, authz stays CARRIED, the may-alias loop rule is one-pass (a
surviving alias across the back-edge is rejected, not iterated to a fixed point),
string literals with escapes and further grammar richness remain depth follow-ons,
and the spec/model/TCB gaps of §0 are unmovable by construction.
