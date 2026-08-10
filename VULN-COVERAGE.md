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
  put the channel in the semantics, then the same NI machinery applies — and
  bricks 32 and 33 run that recipe a second and third time, adding a scheduling
  channel (a demonic-scheduling small-step machine, races/TOCTOU) and a
  transient-execution channel (demonic misprediction, Spectre-class).
  `sequential_model_misses_races` is this gap's own witness: a program provably
  safe under every sequential schedule and unsafe under an interleaving, so a
  proof in a too-small model is true and beside the point.
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

## 2½. How classes are counted

The standing-state heading below carries a class count, so the convention is stated here
rather than left to be reverse-engineered. **A class is counted once for each numbered row
of the §3 map, plus once for each made-real sink class that is carried *inside* an existing
row rather than given a row of its own.** The extras, exhaustively:

- CLASS-EXTRA: **OS command injection** (CWE-78) — made real in brick 27, carried in row 3.
- CLASS-EXTRA: **log injection / log forging** (CWE-117) — brick 29, carried in row 3.

So the count is `|rows| + |extras|`, currently `14 + 2 = 16`, and `tools/check-claims.sh`
enforces the arithmetic against the spelled-out numeral in the heading.

Two things the convention deliberately does **not** do. It does not count *verdict changes*:
a row moving from OUT-OF-MODEL to IN (as row 8 did in brick 32) improves coverage without
adding a class, and the count is an inventory of the map, not a score. And it does not count
sub-formulations within a row (row 3's blacklist-versus-flow split, row 5's f-DP-versus-(ε,δ)
split), which are *verdicts about one class*, not classes.

*(Correction of record: brick 32 raised this number to "seventeen" on the reasoning that
races/TOCTOU had entered the model. That was wrong — races is row 8 and was always counted;
what brick 32 changed was its verdict. Caught by the full audit, which flagged the number as
the one claim it could not independently verify. Restored to sixteen.)*

## 3. The map

| # | class (CWE anchor) | semantic form | region | verdict | grade |
|---|---|---|---|---|---|
| 1 | direct confidentiality leaks (CWE-200) | 2-safety (NI) | 1 | IN (generated) | [proved] |
| 2 | timing side channels (CWE-208) | 2-safety over instrumented semantics | 1 | IN-WITH-MODEL (generated) | [proved] |
| 3 | injection: SQLi/XSS/command (CWE-89/79/78) | taint = integrity NI on a real query skeleton; blacklist = value predicate; escaping = escaper/tokenizer agreement | 1 / — | IN as flow (generated, real query); OUT-INADMISSIBLE as blacklist; REDUCIBLE as escaping (ledgered) | [proved: T1, T2, + real, + escape] |
| 4 | improper declassification / overshare | bounded release (2-safety rel. φ) | 1 | IN (generated) | [proved] |
| 5 | privacy / differential privacy | hyperproperty (quantitative) | 3 | IN as f-DP invariant; OUT-NONCOMPOSABLE as (ε,δ) | [argued] / [proved in miniature] |
| 6 | memory safety (CWE-119/416) | safety of a richer (heap) semantics | — | IN-WITH-MODEL (generated); CARRIED cross-language | [proved] |
| 7 | authz bypass (CWE-285/306); cross-tenant isolation | complete mediation is a path property; isolation is 2-safety; policy correctness is spec-shaped | — / 1 | mediation IN (generated); isolation IN (generated); policy correctness CARRIED | [proved] |
| 8 | races / TOCTOU (CWE-362/367) | safety over *all* interleavings, demonic scheduling | — | IN-WITH-MODEL (generated) | [proved] |
| 9 | speculative execution (Spectre-class) | trace-safety over a transient-execution model, demonic misprediction | 1* | IN-WITH-MODEL (generated) | [proved] |
| 10 | resource exhaustion / DoS (CWE-400) | uniform cost budget over the instrumented semantics | — | IN-WITH-MODEL (generated) on the bounded fragment; REDUCIBLE in general | [proved] |
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

**Escaping is a ledger entry; parameterization is a theorem** (brick 31,
`QueryEscape.lean`). Bricks 14/26 tokenized without an escape mechanism, so the
only safe value was a quote-free one — and every real database disagrees. Adding
escapes to the model separates the industry's two answers by a theorem each. The
escape-aware tokenizer `segsE` (backslash convention) is a **conservative
extension**: it agrees with brick 14's `segs` on every backslash-free string
(`segsT_noBS`, `skeletonE_eq_skeleton`), so bricks 14 and 26 re-derive inside it
(`param_correct_esc`, `concat_injectable_esc`). Then:

- **Complete escaping works, and is faithful.** `segsE_buildEsc` proves the
  escaped query tokenizes to exactly `[pre, v, suf]` for **every** value `v` —
  no hypothesis at all, brick 14's quote-freeness restriction lifted — hence
  `esc_immune` (integrity NI: the skeleton is constant) and `esc_faithful` (the
  value delivered is `v` unchanged, so safety is not bought by corrupting data).
- **The classic bug is located, not merely exhibited.** `escBad` escapes the
  quote but not the escape character; `escBad_injectable` (axiom-free) is the
  real attack — a payload `\'` whose backslash eats the escaper's backslash, so
  the quote arrives unescaped and breaks out — and `escBad_noBS_ok` proves the
  same escaper *is* sound on backslash-free values. The defect is exactly the
  unhandled escape character, in both directions.
- **The point: escaping's soundness is a property of the escaper/tokenizer
  *pair*.** Against the SQL-standard doubled-quote tokenizer `segsD`, the
  backslash escaper is injectable (`esc_mismatch_injectable`); against the
  backslash tokenizer, the doubling escaper is injectable
  (`escDouble_mismatch_injectable`) — while each is sound for its own convention
  (`esc_skeleton`, `escDouble_skeleton`). `escaping_is_convention_relative`
  bundles all four: "the value is escaped" is not a security property.
- **So it is a LEDGER/REDUCIBLE verdict, mechanized against brick 4.**
  `esc_cond_immune` gives the conditional certificate for *every* sink tokenizer
  relative to the one-entry ledger "the sink uses the backslash convention"
  (`Sat [T = segsE]`, brick 4's `Sat`), and `esc_not_unconditional` shows the
  unconditional certificate is false at a sink that does not. Together:
  `escaping_no_silent_discharge` — the injection-channel instance of
  `ledger_no_silent_discharge`. Parameterization, by contrast, needs the
  **empty** ledger (`param_immune_no_ledger`), because no value ever reaches the
  tokenizer. `escaping_reducible_parameterization_in` is the verdict as one
  theorem: the gap between "escape your inputs" and "use prepared statements" is
  exactly one load-bearing ledger entry, and it cannot be discharged by
  inspecting the application.

Honest limit: two escape conventions are modeled (backslash and doubled-quote),
not the full matrix of dialect quirks, and the no-go is exhibited on that pair
rather than proved for all escapers.

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


**Complete mediation, generated** (brick 35, `Mediation.lean`). The CARRIED verdict above
is right about *policy correctness* and was silently swallowing a second, different
property. CWE-285's actual defect — and CWE-306's — is almost never "the policy was
wrong"; it is **missing mediation**: some path reaches the protected operation without
passing the check. That is a property of the program, on every path, and it is decidable.
Brick 35 separates them.

The machine is small: `check r` consults the policy and *aborts* if refused, `access r`
performs the protected read, and `branch` offers two routes with the path taken as a data
parameter — the same demonic device as bricks 32 and 33, so "on some path" is decidable on
a witness and "on every path" quantifies over all of them.

- **The attack [proved, axiom-free].** `victimMed` checks on one branch and forgets on the
  other. `med_victim_bypasses`: under the unguarded path and a policy that *denies* the
  resource, the read happens anyway; `victim_not_mediated` turns that into the property
  failure. Note the shape — the program *contains* a correct check, just not on every
  route, and `victim_guarded_path_is_fine` confirms the other path aborts cleanly. This is
  why mediation is a whole-program, all-paths property and not a local one.
- **The fix, generated [proved].** `medCheck` is a decidable flow-sensitive analysis
  carrying the authorized set and **intersecting** at joins. `medCheck_sound`: a checked
  program reads only what the policy permits, on every path and under every policy. Its
  invariant is three-part (everything authorized is permitted, everything read is
  permitted, the static set under-approximates the dynamic one).
- **The split, as a theorem.** `policy_correctness_not_witnessed` exhibits two policies
  under which the *same* checked program is mediated and yet reads different things — so
  no program analysis can prefer one. That is the CARRIED half, now demonstrated rather
  than asserted, and `mediation_generated_policy_carried` states both halves together.

**And the CARRIED half is now typed** (composable core, stage 1e, `BundleLedger.lean`).
The bundle's mediation certificate says every read is *π-permitted*, which is a security
statement only if π is the policy the specification intended — exactly what
`policy_correctness_not_witnessed` says no program can decide. That gap was a paragraph in
this section; it is now a ledger entry that appends under composition
(`UCertL.seq`) and is provably load-bearing: `handler_intended_reads` discharges the
security reading *from* the assumption, and `handler_needs_the_policy_assumption` shows the
same fully-certified program reads something unintended when the assumption fails.
`row7_carried_is_a_ledger_entry` is both halves. CARRIED is no longer a caveat; it is an
obligation with a type.

Honest limits. Branch bodies are a separate instruction type, so nesting is excluded **by
the syntax** rather than dropped by the semantics. The analysis intersects at joins, so it
is sufficient, not necessary. And the model has no *subject*: this is "was the resource
authorized", not "was it authorized *for this principal*" — binding subject to object is
IDOR (CWE-639), a named follow-on. Two list operations (`memStr`, `interStr`) are defined
and proved locally rather than imported, since the package is mathlib-free.

### 3.8 Races / TOCTOU — IN-WITH-MODEL, generated [proved]

Held OUT-OF-MODEL from brick 1 to brick 31, with a named extension: *a
nondeterministic small-step semantics with demonic scheduling*. Brick 32
(`Race.lean`) builds it, by §0's recipe — put the channel in the semantics, then
the same machinery applies.

The machine is fine-grained on purpose, because fine grain *is* the phenomenon: a
thread is a list of instructions, each one indivisible, over a shared store with
thread-private registers. A **schedule** is a list of thread indices, so the
nondeterminism is a data parameter — "under some interleaving" is an existential a
witness discharges by `decide`, and "under every interleaving" quantifies over all
index lists: unfair, repetitive and adversarial ones included, which is the
strongest form a safety claim can take.

- **The race [proved, axiom-free].** Two threads run the textbook check-then-act
  withdrawal (`load` balance, `guard` it covers 60, `decsh` debit 60) against a
  balance of 100. `toctou_interleaving_unsafe`: under the schedule
  `[0,0,1,1,0,1]` the balance ends at **−20** — both threads read 100, both pass
  the guard, both debit. CWE-367 as a theorem, on a machine where check and act
  are separate steps because they are separate steps.
- **Why the class was out of model, exactly [proved, axiom-free].**
  `sequential_model_misses_races`: every *sequential* schedule of the same program
  is safe (the second thread's guard sees the debited balance and abandons), and
  one interleaving is not. So a proof in the sequential semantics is true — of a
  machine the program does not run on. What row 8 recorded as a caveat is now a
  theorem, and it is the sharpest statement in the map of what "relative to the
  semantic model `M`" in §0 actually costs.
- **The fix, by construction [proved].** Wrapping the critical section in an
  `atom` makes it one scheduling step. `atomic_all_schedules_safe`: the invariant
  holds under **every** schedule — proved by induction over the interleaving, not
  sampled.
- **Generated.** `racefree` is a decidable syntactic check — no bare shared write
  outside a critical section — with `racy_rejected`/`atomic_accepted` by `decide`.
  Its soundness `racefree_all_schedules` is the brick's centrepiece because it is
  a **reduction**: for a checked pool, "the invariant survives every interleaving"
  follows from "each critical section preserves the invariant" — an ordinary
  sequential obligation in which no schedule appears (`racefree_poolPreserves`
  proves the syntactic half: a step that does not write shared state provably
  cannot break a shared-state invariant). Concurrency verification collapses to
  per-section sequential verification, gated by a Boolean.
  `race_rejected_atomic_safe` bundles attack and defense.

Honest limits, and they are real. This is **safety** under demonic scheduling:
fairness, liveness and deadlock are not modeled, and an `atom` is an idealized
critical section, not a lock-acquisition protocol. The memory model is
sequentially consistent — no store buffers, no reordering. And the check *reduces*
the obligation rather than discharging it: `bad_atom_not_preserving` +
`bad_atom_accepted` witness an atomic-but-wrong critical section that the checker
accepts and that breaks the invariant, so the per-section proof is a genuine
residual, visible and unautomated. Also unchanged: determinism remains
load-bearing for the *confidentiality* gate (`conform_refl` discharges through
Sem-Det), so this brick adds a concurrent safety channel beside that development
rather than rebuilding `≅` over trace sets — the 2-safety-over-interleavings
question (secure information flow under scheduling) stays open.

### 3.9 Speculative execution — IN-WITH-MODEL, generated [proved]

Held OUT-OF-MODEL from brick 1 to brick 32, with the honest note that "nothing in this
repo excludes Spectre, and no verdict pretends otherwise" and the caveat that the model
is research-scale. Brick 33 (`Speculate.lean`) runs §0's recipe a third time — after
timing (brick 2) and scheduling (brick 32) — at the scale that caveat allows: not a
microarchitecture, but a genuine transient-execution machine carrying the one channel
that matters, with the bounds-check bypass on it.

The machine splits state in two: an **architectural** part that rolls back, and a
**microarchitectural** trace of touched addresses that does not. A `brLt` branch may be
mispredicted, running its body transiently for a bounded window; the registers are
discarded, the addresses are not. That asymmetry is the whole of Spectre. A
**misprediction schedule** is a list of window budgets, so speculation is a data
parameter exactly as the interleaving was in brick 32.

- **The attack [proved, axiom-free].** The victim `if i < 4 then (x := mem[i]; y :=
  mem[x])` is the textbook gadget: the second load's *address* is the first load's
  *value*. With `i` out of bounds the guard is false, yet a mispredicting schedule runs
  the body anyway — `spectre_trace_is_the_secret` pins the traces at `[8,42]` and
  `[8,99]` for two memories differing only at the secret, so `spectre_leaks`. The
  channel has measurable depth: `leak_needs_window_two` shows a one-instruction window
  leaks only the public index, and the secret needs the second load.
- **Why the class was out of model, exactly [proved, axiom-free].**
  `arch_indistinguishable`: architecturally the guard is false, nothing runs, and the
  two memories give *identical* traces. `speculative_model_misses_it` is the pair — the
  program is secure on the machine the earlier bricks describe and insecure on the
  machine it runs on. Third instance of §0's model gap made concrete, and the sharpest,
  since here the architectural semantics is not merely coarse but *silent*.
- **The fix, generated and composable [proved].** `specCheck` is a decidable rule:
  every branch body begins with a `fence`. Its soundness is the strong form —
  `specCheck_sound`/`spec_inert`: on a checked program the speculative registers *and*
  trace **equal** the architectural ones, under **every** schedule. So speculation is
  observationally inert, and `arch_ni_transfers` carries any architectural
  noninterference over verbatim — which is what makes this row compose with the rest of
  the map rather than sit beside it. `victim_rejected`/`fixed_accepted` decide the
  check; `fixed_secret_independent` is the end-to-end statement.

Honest limits, and they are substantial. The microarchitectural state is an *address
trace*: cache-line granularity, eviction, timing and contention are not modelled, so
what is excluded is the address-visible channel, not every physical side channel. Only
conditional-branch misprediction (v1) is modelled — no indirect branches (v2), no
store-to-load forwarding (v4) — and rollback is perfect. Nested speculation is excluded
**by the syntax** (branch bodies are a separate instruction type with no branch in it)
rather than silently dropped by the semantics. And the check is *sufficient, not
necessary*: `benign_rejected` with `benign_transient_is_constant` exhibits a body it
rejects whose transient trace is provably constant, so lifting the rule to "no
address-dependent load before the fence" is a named follow-on, not a soundness gap.

### 3.10 Resource exhaustion — IN-WITH-MODEL (generated) on the bounded fragment; REDUCIBLE in general [proved]

Brick 34 (`CostBound.lean`) proves what brick 1 asserted, and corrects the one part of
the assertion that does not hold.

The property is **uniformity**. `CostAtMost c k` says that *whatever* the input and
*whatever* the fuel, a halting run of `c` costs at most `k`. Algorithmic-complexity DoS
is exactly the failure of uniformity — a bound exists per input but not across inputs —
so the quantifier order is the whole definition.

- **Accumulation is a `GradedAction` [proved].** `costGA : GradedAction Nat Nat`, grade
  composition `+`, action `+`, order `≤` — the three fields `Bridge.comp` consumes,
  checked. `cost_seq` is the law and `cost_seq_is_mul` states it as `costGA.mul` on the
  nose. "Bounds compose by accumulation" is now a theorem in the repo's own algebra,
  alongside `cost_skip`, `cost_assign`, `cost_ite`.
- **The attack [proved].** `spinU_cost_lb` shows the canonical countdown's cost grows
  with its counter, so `dos_unbounded`: a loop whose trip count is read from untrusted
  input satisfies `CostAtMost` for **no** `k`. Note what it costs the rest of the map
  nothing to miss: the victim is memory-safe, injection-free and noninterferent, and
  every earlier brick certifies it.
- **The fix, generated [proved].** `costCheck` computes budgets for the loop-free
  fragment (`costCheck_sound`), and `budget_cost` restores uniformity for a countdown
  whose counter is initialised from a **constant** and whose body never touches it
  (`noAssign_preserves`) — a bounded work unit, the real mitigation.
  `dos_unbounded_budget_bounded` is the pair.

**Correction of record.** The brick-1 text called this "a *graded certificate* in the
transport sense (a monotone bound on the distance/cost effect: `Bridge.ofModulus`
territory)". The `GradedAction` half is right and is now proved. The `Bridge` half is
**wrong**: a `Bridge` certifies a *binary* quantity — `dist (map x) (map y) ≤ act cert
(dist x y)` — whereas a cost budget is **unary**, a bound on one run, not a modulus
relating two. What transfers is the accumulation algebra; what does not transfer is the
contraction. (Cost *sensitivity* — how much an input change can change the cost — would
be binary and Bridge-shaped, and is a different, unproved property.)

Honest limits. `CostAtMost` bounds halting runs: availability ("eventually responds") is
liveness-shaped, still not expressible and still not claimed. The loop rule covers the
canonical countdown; general ranking-function analysis remains external, exactly as
brick 1 said — hence "REDUCIBLE in general" stays in the verdict. And cost is the
instrumented step count, not wall clock, so §0's model gap applies unchanged.

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

### Brick 29 ledger (a third real sink — log injection / log forging, CWE-117)

- `LogInjection.lean` — the fourth made-real channel (after SQL injection, path
  traversal, command injection), with a fourth metacharacter: the **record
  separator** (a newline). A log splits into records on newlines; the executed
  structure is the even (structural) records. `field_correct`/`field_immune` —
  structured logging (`log.info(event, field=value)`) keeps the executed structure
  a function of the trusted preamble alone; `log_concat_injectable` — a newline
  inside a concatenated field forges a record (`log.write(preamble+"\n"+field)`).
  Integrity NI with a real log sink, adding a class to the "more sink classes"
  axis. **Brick 29 complete — log injection joins the made-real channels.**

### Brick 30 ledger (fixpoint may-alias — closing brick 24's one-pass loop rule)

- `AliasFix.lean` — the hard follow-on brick 24 named: its loop rule is *one-pass*,
  so an alias-maintaining loop (`while (…) copy 1 0`, two pointers live on entry)
  is rejected because one body pass merges the entry classes. This brick infers a
  **coarsening invariant** by iterating the body transfer to a fixed point.
  `ALInv_coarsen` (axiom-free) is the semantic heart: merging classes only weakens
  the may-alias over-approximation, so `ALInv P → ALInv Q` for any coarsening `Q`.
  `mergeOne` + `ALInv_of_setSub` give order-insensitive (set-equality) class
  comparison. `loopFix` iterates, merging classes until a preserved fixed point;
  `loopFix_correct` proves its **partial correctness** — whatever it returns
  coarsens the entry and is preserved — and `loopFix_terminates` proves
  **convergence**: each merge strictly shrinks the class count
  (`findMerge_mergeOne_length`), so the search reaches its final answer within
  `|P| + 1` fuel and never diverges. `coarsen_loop_safe` proves the loop
  memory-safe from the inferred invariant (fuel induction reusing brick 24's
  `alsafe`). `maintain_loopFix` shows the fixpoint infers `[[1, 0]]` by `decide`,
  `brick24_rejects` shows brick 24's one-pass rule returns `none` on the same loop,
  and `alias_maintain_loop_safe` proves it safe. Completeness is **narrowed**, not
  abandoned: the fully-merged partition (the top of the may-alias lattice) is always
  a valid coarsening (`Coarsens_collapse`) and is a fixed point exactly for alias-
  maintaining loops, so `coarsen_loop_complete` proves any loop whose top is
  preserved is safe (heuristic-independent) and `loopSearch_complete` proves the
  search — widened to the top — then succeeds. And the **result is uncaged**:
  `alcheck2` / `alsafe2` fold the coarsening loop rule into a full recursive checker,
  so a loop composed into a real program (`seq`, code before and after) is checked
  and proved safe end to end — and the checker is **mutually recursive** with the
  fixpoint iterator, so a loop's body is checked by the same fixpoint checker: nested
  loops get the fixpoint at arbitrary depth (the mutual definition terminates on
  `(sizeOf body, which-function, iteration-fuel)`; soundness is structural induction
  on the command). `prog_safe` proves `alloc 0; alloc 1; while (…) copy 1 0` safe and
  `nested_prog_safe` proves `… while (…) ( while (…) copy 1 0 )` — a loop nested
  inside another loop's body — safe end to end. The merge is **body-guided**
  (`findMerge2`): it merges the two classes the body's transfer *unified* — the
  genuine join — landing on strict-intermediate fixed points the blind first-two
  heuristic missed. `weak_accepted` / `weak_prog_safe` are the witness that pinned
  the residual, now accepted and proved safe end to end. Residual: loops with no
  coarsening fixed point reachable by iterated body-guided merging — a narrow class.
  **Brick 30 complete — the may-alias loop rule iterates to a fixed point, provably
  terminates, is complete for the top of the lattice, composes into whole programs
  with loops nested to any depth, and merges the classes the body actually aliased.**

### Brick 31 ledger (string literals with escapes — escaping is a ledger entry)

- `QueryEscape.lean` — the last named depth follow-on on the injection axis, and
  the one where the real CVEs live: not "they forgot to escape" but "they escaped
  against the wrong convention". Escapes enter the model as a three-state scanner
  over brick 14's own alphabet (the backslash is the character at code 92), and
  `segsT_noBS`/`skeletonE_eq_skeleton` prove it a **conservative extension** —
  identical to brick 14's tokenizer on backslash-free strings, so bricks 14 and 26
  re-derive inside it (`param_correct_esc`, `concat_injectable_esc`). `segsT_esc`
  is the heart: scanning a completely-escaped value inside a literal consumes
  exactly that value and stays inside, with **no hypothesis on the value** — so
  `segsE_buildEsc` gives `[pre, v, suf]` for every `v`, lifting brick 14's
  quote-freeness restriction, and yields `esc_immune` (integrity NI) and
  `esc_faithful` (the delivered value is `v`, uncorrupted). The classic bug is
  bracketed on both sides: `escBad_injectable` (axiom-free) is the `\'` attack on
  an escaper that misses the escape character, `escBad_noBS_ok` proves that same
  escaper sound on backslash-free values. The brick's point is the pair of
  mismatches — `esc_mismatch_injectable` (backslash escaper, doubled-quote sink)
  and `escDouble_mismatch_injectable` (doubling escaper, backslash sink), both
  axiom-free, against `escDouble_skeleton`'s soundness for its own convention,
  bundled as `escaping_is_convention_relative`. That makes escaping
  assumption-shaped, so it is mechanized against **brick 4's ledger**:
  `esc_cond_immune` (conditional on `Sat [T = segsE]`, for every tokenizer),
  `esc_not_unconditional` (false at a mismatched sink), and
  `escaping_no_silent_discharge` — `ledger_no_silent_discharge` on the injection
  channel. `param_immune_no_ledger` puts parameterization at the empty ledger, and
  `escaping_reducible_parameterization_in` states the verdict as one theorem. No
  `sorry`, no `Classical.choice` anywhere in the module; every attack witness is
  axiom-free. Honest limit: two conventions modeled, and the no-go is exhibited on
  that pair rather than proved for all escapers. **Brick 31 complete — escaping is
  REDUCIBLE with a load-bearing, ledgered assumption; parameterization stays IN
  with an empty trusted base, and the distance between them is a theorem.**

### Brick 32 ledger (races and TOCTOU — the class the map called OUT-OF-MODEL)

- `Race.lean` — row 8's named extension, built: a nondeterministic small-step
  semantics with demonic scheduling. Threads are lists of indivisible
  instructions over a shared store with private registers; a schedule is a list
  of thread indices, so nondeterminism is *data* — `∃ interleaving` is decidable
  on a witness and `∀ interleaving` ranges over every index list (unfair,
  repetitive, adversarial). `toctou_interleaving_unsafe` (axiom-free) drives the
  balance to −20 with two concurrent 60-withdrawals from 100: both read, both
  pass the guard, both debit — CWE-367 as a theorem.
  `sequential_model_misses_races` (axiom-free) is the honest half: both
  *sequential* schedules of the same program are safe, so the sequential proof is
  true of a different machine — the §0 model gap made concrete rather than
  asserted. The fix is an `atom` (the critical section as one scheduling step),
  and `atomic_all_schedules_safe` proves the invariant under **every** schedule by
  induction over the interleaving. `racefree` is the decidable rule — no bare
  shared write outside a critical section — with `racy_rejected`/`atomic_accepted`
  by `decide`, and `racefree_all_schedules` its soundness: a **reduction** from
  the concurrent obligation to a sequential one per critical section
  (`racefree_poolPreserves` supplies the syntactic half — a step that does not
  write shared state cannot break a shared-state invariant;
  `poolPreserves_step`/`rrun_preserves` carry it across the schedule).
  `race_rejected_atomic_safe` bundles attack and defense. No `sorry`, no
  `Classical.choice`; every attack witness axiom-free. Honest limits stated as
  such: safety only (no fairness, liveness or deadlock), `atom` is an idealized
  critical section rather than a lock protocol, the memory model is sequentially
  consistent, the per-section obligation is a real residual
  (`bad_atom_not_preserving` + `bad_atom_accepted`: atomic-but-wrong is accepted
  and unsafe), and 2-safety *over* interleavings — information flow under
  scheduling — stays open, since determinism is still load-bearing for the
  confidentiality gate. **Brick 32 complete — the last wholly-unmodelled common
  class enters the model, with the attack, the by-construction fix, and a
  decidable check whose soundness reduces concurrency to sequential reasoning.**

### Brick 33 ledger (speculative execution — the last OUT-OF-MODEL row)

- `Speculate.lean` — row 9's named extension, at the scale its caveat allowed. A
  transient-execution machine: architectural state that rolls back, a
  microarchitectural **address trace** that does not, and a `brLt` branch that may be
  mispredicted, running its body transiently for a window drawn from a **misprediction
  schedule** (a data parameter, as the interleaving was in brick 32; `∀ schedule`
  ranges over unbounded windows). `spectre_trace_is_the_secret` (axiom-free) pins the
  gadget's traces at `[8,42]`/`[8,99]` for two memories differing only at the secret,
  so `spectre_leaks`; `leak_needs_window_two` shows the channel has real depth — a
  one-instruction window leaks only the public index. `arch_indistinguishable`
  (axiom-free) is the other half: architecturally the guard is false and nothing runs,
  so the two memories are *identical*, and `speculative_model_misses_it` is the pair —
  §0's model gap in its sharpest form yet, the architectural semantics not merely
  coarse but silent. The fix is a `fence`, and the soundness is the strong form:
  `specCheck_sound`/`spec_inert` prove the speculative registers **and** trace equal
  the architectural ones under every schedule, so speculation is observationally inert
  and `arch_ni_transfers` carries any architectural noninterference over verbatim —
  the property that makes the row compose rather than sit beside the map.
  `victim_rejected`/`fixed_accepted` decide the check; `fixed_secret_independent`
  closes it end to end. No `sorry`, choice-free (`propext` at most), every attack
  witness axiom-free. Honest limits kept in the file and in §3.9: address-trace
  granularity only; v1 alone (no v2, no v4); perfect rollback; nested speculation
  excluded **by the syntax** rather than dropped by the semantics; and the check is
  sufficient but not necessary — `benign_rejected` with `benign_transient_is_constant`
  exhibits a rejected body whose transient trace is provably constant, making the
  refinement a named follow-on rather than a soundness gap. **Brick 33 complete — the
  last OUT-OF-MODEL row enters the model, and the map now has no class whose channel
  is simply absent from every semantics in the repo.**

### Brick 34 ledger (resource exhaustion — the cost bound as a graded certificate)

- `CostBound.lean` — row 10's [classified] reduction, proved, and one clause of it
  corrected. `CostAtMost c k` quantifies over **all inputs and all fuel**, so DoS is the
  failure of uniformity rather than the absence of a bound. `costGA : GradedAction Nat
  Nat` (mul `+`, act `+`, le `≤`) is a checked instance of the interface's own
  accumulation algebra, and `cost_seq`/`cost_seq_is_mul` prove budgets add — the first
  time a *security* row lands directly in the transport calculus's algebra rather than
  beside it. `costCheck` + `costCheck_sound` generate budgets for the loop-free
  fragment. `noAssign_preserves`, `countdown_turn` and `countdown_cost` give the loop
  bound `1 + v·(kc+3)` in the counter's initial value `v` — a bound that exists per
  input and *grows with it*, which is precisely the DoS surface. `spinU_cost_lb` (an
  induction with fuel supplied by `wexec_mono_le`) turns that into `dos_unbounded`:
  **no** uniform budget exists for a loop counting down untrusted input — and the
  victim is memory-safe, injection-free and noninterferent, so every earlier brick
  certifies it. `budget_cost` restores uniformity when the counter is initialised from a
  constant, `fixed_bounded` instantiates it at 402, and
  `dos_unbounded_budget_bounded` is the attack/fix pair. Numbers checked against the
  model: cost 16 at counter 5 and 31 at counter 10, matching `1 + 3v`; `costCheck`
  returns `none` on the victim and `some 2` on a loop-free program. No `sorry`,
  choice-free. **Correction of record:** brick 1's "`Bridge.ofModulus` territory" is
  wrong — a `Bridge` certifies a binary quantity and a cost budget is unary; the
  `GradedAction` transfers, the contraction does not. Honest limits: halting runs only
  (availability is liveness-shaped and still not claimed), the canonical countdown only
  (general ranking analysis stays external, so the verdict keeps "REDUCIBLE in
  general"), and instrumented steps rather than wall clock. **Brick 34 complete — the
  last [classified]-only reducible row is proved, and the security program's
  quantitative side now composes by the same law as the contraction estimates.**

### Brick 35 ledger (complete mediation — the split row 7 was hiding)

- `Mediation.lean` — row 7 carried the map's **last [classified] grade**, on the
  reasoning that π's correctness "is not a theorem anywhere". True of policy
  correctness; false of the thing CWE-285 and CWE-306 actually name. **Missing
  mediation** — a path reaching the protected operation without the check — is a
  program property, all-paths, decidable. `Mediated p` quantifies over every policy and
  every path. `med_victim_bypasses` (axiom-free): the unguarded branch reads a resource
  the policy denies, while `victim_guarded_path_is_fine` shows the other branch aborts
  cleanly — the defect is the *route*, not the check. `medCheck` (flow-sensitive,
  intersecting at joins) plus `medCheck_sound` generate the guarantee, on a three-part
  invariant: everything authorized is permitted, everything read is permitted, and the
  static set under-approximates the dynamic one. `policy_correctness_not_witnessed`
  proves the other half is *not* program-decidable — two policies, same checked program,
  both mediated, different reads — so `mediation_generated_policy_carried` states the
  split as one theorem. No `sorry`, choice-free; witnesses checked against the model
  (deny+unguarded reads `["db"]`, deny+guarded reads `[]`, the fix reads nothing under
  deny on either path). Honest limits: nesting excluded by the syntax; the join is an
  intersection so the check is sufficient not necessary; and there is no *subject* in the
  model, so IDOR (CWE-639) is a named follow-on. `memStr`/`interStr` are defined and
  proved locally — the package is mathlib-free and guessing at core lemma names had
  already cost two build rounds. **Brick 35 complete — the map's last [classified] grade
  is gone; every row is now [proved], [argued] or an explicitly named deferral.**

### The composable core (structural work, not a brick)

A measured weakness of the brick method, recorded here because it bears on what the map's
verdicts *jointly* mean. The bricks define **sixteen** distinct instruction types across
thirty modules, and there is **zero** cross-brick composition: no module mentions two brick
languages, and the only bridge is brick 7's `embed : Cmd → WCmd`. So each row's verdict
holds of *its own* toy language, and no single program carries two of them at once — which
is precisely where "composition accumulates certificates" most needs to hold.

Two stages have landed. `GradedAction.prod` / `Bridge.pair_comp_cert` (transport-calculus)
give the algebra: bundles accumulate componentwise, no interaction term, so carrying `n`
guarantees costs `n` independent accumulations. `Unified.lean` gives the object: `UCmd` is
`WCmd` plus `check`/`access`, with **`uexec_embed_eq`** proving the While development is a
*fragment* of it — store, cost and branch trace exactly `wexec`'s, the new dimensions
untouched — so brick results transfer (`ucost_of_cost`) rather than fork, and old programs
satisfy the new dimensions vacuously (`uembed_mediated`).

Stage 1c has landed (`Bundle.lean`): **`ucheck`** is one decidable analysis emitting a
bundle, **`ucheck_sound`** one soundness theorem, and **`handler_bundle_end_to_end`** a
worked request handler carrying a cost budget *and* complete mediation at once — with the
two halves composing by different laws (budgets add via `costGA.mul`, authorization sets
thread as a Hoare triple, no interaction term). The budget is tight on the permitting run,
and under a policy permitting the database but refusing the log the handler reads only the
database, so mediation is per-resource rather than all-or-nothing.

Stage 1d adds the third certificate (`UnifiedNI.lean`). The design decision it turned on
is recorded there: `reads` and `dead` are Low-observable, `auth` is not. With that,
`check`/`access` add **no flow channel** — their resource names are syntactic constants —
so `WSecTy`'s discipline lifts unchanged (`usecTy_sound`), and
**`handler_three_certificates`** carries a budget, mediation and noninterference on one
program, composing by three different laws.

**Correction, upward (stage 1g, `BundleCoverage.lean`).** This note previously said the
bundle carries "three of the map's properties". It carries **six**. The observation in
`uOptLowEq` includes the cost and the halting bit, so one application of `usecTy_sound`
discharges rows **1, 2 and 13** together — the same economy bricks 3, 5 and 7 had on the
While language. With row 7 (mediation), row 10 (budget) and row 12 (composition seams,
which is what `UCert.seq` *is*), that is six, each now projected out as a theorem
(`bundle_covers_store`, `bundle_covers_timing`, `bundle_covers_termination`,
`bundle_covers_seam`, `handler_covers_six_rows`). Stage 1e's ledger additionally supplies
row 11's *mechanism*, though not its class.

**What is still not true.** Six of the map's properties, not sixteen. The bundle now admits **bounded loops** (stage 1f,
`BundleLoop.lean`): `UCert.ofEmbedded` takes any separately-certified While program,
loops included, once three lemmas pin down an aborted run — the abort is *total*
(`uexec_dead_unchanged`), a dead run inside a live loop never returns
(`uexec_dead_loop_diverges`), so its cost is statically bounded (`uexec_dead_cost`).
General loops are still out: the counter must be constant-initialised and the body
check-free, and ranking-function analysis remains external. The NI result is *bought* by having no
store-dependent resource selection: with `access (e)`, `reads` would be a genuine flow
channel and the rules would need side conditions — `access_is_static_by_design` records
this as a price, and it is the IDOR follow-on named in brick 35. Stage 1h grew the language with a **heap**, so row 6 is now partly in: `umcheck_no_fault`
gives memory safety as a *separate* certificate — added without touching any existing
checker, which is the extensibility claim tested rather than asserted — closing the
wild-access half (CWE-119). Stage 1i closed the other half: `SepInv` strengthens the
invariant with separation (distinct tracked variables hold distinct addresses) and
freshness, `free` gets a rule, and `slcheck_no_fault` rules out use-after-free (CWE-416)
— with `use_after_free_faults` confirming the rejected program really does fault, and
`slcheck_extends_umcheck` confirming nothing stage 1h accepted was lost. Stage 1i also
*explains* stage 1h's gap rather than merely filling it: `memInv_not_preserved_by_free`
exhibits a state satisfying the weaker `MemInv` that one `free` step invalidates, so the
missing rule was an obstruction, not an unfinished proof. Stage 1j then narrowed the standing limit and replaced its reason. `alloc` into a
**High** variable is noninterferent with no change to the observation (`USecTy.allocH`,
`high_alloc_is_NI_typed`), so `memops_not_yet_NI_typed` now covers only `deref` and
`free` — and their obstacle is not the one stage 1h named: they can *fault*, a fault
sets `dead`, and `dead` is observable (`deref_leaks_through_dead`). They are
noninterferent precisely on memory-safe states (`deref_NI_given_safety`). Row 6 and
row 1 therefore **interact**: `ni_and_memory_do_not_factor` is the first pair of
certificates in this repo that cannot be established independently and conjoined, which
is a structural finding about the bundle rather than about either row.
`allocL_would_be_unsound` records the one genuinely open design question — whether
allocation addresses are visible to a Low adversary.

Stage 1k resolved the interaction rather than only naming it. `JSecTy P V c V'` carries
the partition and the tracked set in one judgment, `jsecTy_sound` proves both
properties in a single induction (the memory invariant being a *hypothesis* of the
noninterference proof), and `jcheck_gives_both` extracts them from one run of one
checker. `indexed_beats_the_conjunction` shows this is not a repackaging: on
`safeHeapProg` — allocate into a secret, dereference, mediate an access, free —
`ucheckNI` rejects outright and `slcheck` is silent about leaks, while `jcheck`
certifies both. So on this machine rows 1, 2, 13 and 6 can now be carried by a single
program that uses the heap. Stage 1l then removed the loop conservatism with exactly that widening step:
`narrowFix` computes the tracked-set loop invariant by descending iteration,
`narrowFix_spec` discharges `JSecTy.whileW`'s side-conditions, and
`widening_beats_the_exact_rule` accepts a loop that allocates while still tracking the
pointer that must survive it. Stage 1m then closed the last item, and by dissolving it rather than deciding it.
`allocL` looked like it required a ruling on whether addresses are visible to a Low
adversary; in fact this type system has no High-guarded control flow, so two Low-equal
runs allocate in lockstep. Carrying `s.fresh = s'.fresh` as a *relational invariant*
(not as an observation) makes allocation noninterferent with **no side condition** —
stage 1m removes a hypothesis rather than adding a rule, and the public statements are
unchanged. `allocation_sync_is_load_bearing` records that stage 1j's counterexample is
still true and now serves as the reason the invariant cannot be dropped;
`high_branch_desynchronises_the_allocator` plus `highBranch_is_untypable` record what
the argument rests on, so adding High-guarded control flow would break the build.
The composable core's conservatism list is empty; what remains is scope.

Stage 1n merged the bundle and the joint judgment: `allcheck` yields a budget, an
authorization set, noninterference and memory safety from one pass, and `fullProg`
carries all four (rows 1, 2, 7, 10, 13 and 6) with a budget that is tight — certified
six, spends six. Merging them turned a hidden asymmetry into a theorem:
`only_the_budget_lacks_a_loop_rule`. Noninterference, memory safety and mediation all
compose over loops; the cost bound cannot, because it needs an *iteration* bound, which
is a termination argument rather than a typing side-condition. That is a boundary
rather than a to-do — brick 30's `loopFix` and stage 1f's `countdown` are the two ways
to supply it, and both are analyses of a different kind.
Stage 1o gave `UCmd` **strings**, so row 3 is now expressible and partly carried here
too: `tcheck_no_injection` guarantees that every emitted string carries exactly the
delimiter count the analysis predicted, with `injection_is_real` executing the attack
(three delimiters where two were written), `injection_rejected` refusing it, and
`sanitised_query_holds_under_every_input` covering all inputs rather than one payload.
This is *narrower* than bricks 11–20's treatment, deliberately: a two-symbol alphabet
and a count, not a tokenizer and a parse tree — it captures the structural break that
defines an injection, and nothing else. Row 14 (path traversal) is done as of stage 1q, and not as a copy of row 3: traversal
is a **prefix** condition rather than a count (`counting_cannot_decide_traversal` —
`a/..` and `../a` carry the same symbols and only one escapes), so it has its own
property (`safePath`, a depth walk), its own rule, and a per-sink discipline.
`path_escape_is_real` runs the `../..` payload and shows the vulnerable program emitting
a path that pops above its root; `path_escape_rejected` refuses it;
`safe_path_holds_under_every_input` covers all inputs. `path_needs_the_taint_environment`
records that this certificate *layers on* stage 1o's count environment rather than
sitting beside it — the second dependency in the bundle after
`ni_and_memory_do_not_factor`, and the first that a parameter rather than a new indexed
judgment could resolve. Stage 1p removed two of stage 1o's three limits. The sink is now **in** the
noninterference observation — it is an output channel, and leaving it out had made every
string operation trivially noninterferent (`emit_of_secret_rejected` is the leak now
caught) — and every checker accepts string operations, so `fiveProg` carries all five
certificates at once. `sanitising_does_not_declassify` records that `san` removes
delimiters, not secrets: the structural checker accepts `emit (san secret)` and the
noninterference checker refuses it, which is why both are carried.
`factoring_holds_here` records that this fifth certificate *does* factor, unlike the
third (`ni_and_memory_do_not_factor`). Standing limit: loops have no `tcheck` rule.
Before stage 1o both rows were not even *expressible* on `UCmd` —
and rows 8, 9 and 11 are proved on their own machines in bricks 32, 33 and 4. So the
remaining ten rows' verdicts are still statements about their own languages, and the
conjunction of all sixteen classes on one program is not a theorem.

### The security program, standing state (thirty-five bricks, sixteen classes)

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
decimal identifiers (a verified codec), path traversal,
OS command injection, and log injection are closed by the same
data-not-structure discipline, composition is certificate accumulation by the same
law that composes contraction estimates, and every guarantee carries its trusted
base as an automatic bill of materials. The honest edges are all named as theorems
or deferrals: `(ε,δ)`-DP stays
OUT-NONCOMPOSABLE, authz stays CARRIED, the speculative channel is modelled only at
address-trace granularity and only for v1 (brick 33), the may-alias loop rule now iterates to a
fixed point (a coarsening invariant is inferred, validated, the iteration provably
terminates within `|P|+1` steps, the search is complete for the top of the
lattice — every alias-maintaining loop — and the rule composes into whole programs
through a full recursive checker mutually recursive with the fixpoint iterator, so
loops nest to any depth, and merges the classes the loop body actually aliased so
strict-intermediate fixed points are reached) with only loops that have no
body-guided-reachable fixed point as the residual, **escaping is now REDUCIBLE
with its assumption in the ledger** rather than an unmodelled gap — string
literals with escapes are in the tokenizer, complete escaping is proved sound and
faithful, the unescaped-escape-character bug and the escaper/tokenizer convention
mismatch are proved injectable, and the distance from escaping to parameterization
is exactly one load-bearing ledger entry (brick 31) — further grammar richness and
the remaining dialect quirks stay depth follow-ons, **races and TOCTOU are no
longer OUT-OF-MODEL** — a demonic-scheduling small-step semantics carries the
check-then-act attack (`toctou_interleaving_unsafe`, a negative balance), the
atomic fix proved safe under every interleaving, and a decidable race-freedom
check whose soundness *reduces* the concurrent obligation to a sequential one per
critical section (brick 32), with fairness, liveness, deadlock, weak memory and
information-flow-under-scheduling named as what is still outside,
and the spec/model/TCB gaps of §0 are unmovable by construction.
