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
| `ConfTyping/CountedLoop.lean` | stage 2j | **the counted loop, natively**: a uniform budget for a loop whose body is an arbitrary `UCmd` — heap, mediation and emission included — so `loopHandler` carries all five certificates *while iterating*. A dying loop diverges rather than overspending, which is what makes the bound provable |
| `ConfTyping/SpecFused.lean` | stage 2i | **the fused induction, and the trace theorem**: `PtrLow` is inductive over whole certified programs when — and only when — it travels with `SepInv`, `LabInv` and `uLowEqA`, and the speculative trace of a certified program is a function of the Low part of its input at every window. Stage 2d's conjecture, proved, and applied to `bigHandler` |
| `ConfTyping/BigHandler.lean` | stage 2h | **a program worth the name**: twenty-one operations, all five certificates from one checker, budget 24 and tight. The trusted base is still two entries, the secret address is retired, and 2e's speculation bound does real work (26 real against 24 certified) |
| `ConfTyping/SpecFactor.lean` | stage 2g | **the trace does not factor either**: the natural relation for stating trace agreement is not inductive, and `LabInv` is the missing hypothesis — so the trace proof must be *fused into* `jsecTy_sound`, not layered on it. Stage 1j's wall from a third direction |
| `ConfTyping/SpecTrace.lean` | stage 2f | the trace conjecture **was false**, and not because of speculation: a halted machine kept issuing memory operations. `touched` corrected, the defect kept on record, and `PtrLow` — the invariant the repaired conjecture needs — proved inductive |
| `ConfTyping/SpecBudget.lean` | stage 2e | **rollback is complete** for every program and every window, so four of the five certificates are immune to speculation outright; the fifth — the budget — is bounded at `k * (1 + w)`. Only the trace is left open |
| `ConfTyping/SpecUnified.lean` | stage 2d | speculation on the unified machine: the plan was a certified program that leaks, and **no such program exists** — `slcheck`'s load rule and the low-guard requirement already exclude both routes. What *is* broken is the budget |
| `ConfTyping/Assumptions.lean` | stage 2c | the trusted base **computed from the program**: `needs` collects the entries a program can incur, two vacuity lemmas prove the omitted ones are omitted for cause, and `pureProg` gets all three deployment guarantees on an *empty* ledger |
| `ConfTyping/Ownership.lean` | stage 2b | the failure pinned at the *invariant*: `SepInv` is **not conjunctive**, so two thread-local certificates say nothing about the pair — plus the frame rule's decomposition |
| `ConfTyping/Interleave.lean` | stage 2a | two threads on the unified machine: **memory safety does not compose** (two certified threads, one faulting interleaving) while the budget does |
| `ConfTyping/HeapRetire.lean` | stage 1z | 1y's gap closed by **retiring** secret addresses instead of recycling them — one branch in the evaluator, one dropped hypothesis, no new invariant |
| `ConfTyping/HeapAttack.lean` | stage 1y | attacking the labelled heap: the new guarantee is **not** vacuous, and two correct rules compose into one that is too strong — **a secret cell can never be freed** |
| `ConfTyping/HeapSecret.lean` | stage 1x | the invariant spent: the observation becomes **per address** and `storeH` lets a secret live in the heap — the heap is now two-level rather than public |
| `ConfTyping/HeapLabel.lean` | stage 1w | **per-address heap labels, the invariant half**: cells labelled at allocation, allocation zeroes, and `LabInv` — every tracked pointer points at a cell of its own level — proved inductive |
| `ConfTyping/HeapValue.lean` | stage 1v | the heap gets real `load`/`store`: memory safety extended for free, noninterference did not — the heap enters the observation and becomes a **public resource** |
| `ConfTyping/Reuse.lean` | stage 1u | the allocator now **reuses** freed addresses: the separation argument survived with two new invariant conjuncts, but reuse turned the free list into a **channel**, so `free` needs a Low pointer |
| `ConfTyping/Attack.lean` | **attacking the core**, stage 1t | twelve adversarial programs, all refused — and three defects found by looking on purpose, all of them a guarantee narrower than its name |
| `ConfTyping/Deploy.lean` | composable core, stage 1s | the ledger, threaded: what must be true of the **world** — and the answer is a trusted base **three lines long**, with two of the six certificates needing nothing at all |
| `ConfTyping/StringLoop.lean` | composable core, stage 1r | loop rules for both string certificates by narrowing; the loop count is corrected to **five of six**, the budget still the exception |
| `ConfTyping/PathCert.lean` | composable core, stage 1q | **path traversal** (CWE-22), the last coverage row: a prefix condition rather than a count, per-sink, and layered on the taint environment |
| `ConfTyping/AllFive.lean` | composable core, stage 1p | the sink enters the noninterference observation (closing a real weakness in 1o), and `fiveProg` carries **five** certificates |
| `ConfTyping/TaintCert.lean` | composable core, stage 1o | **strings**, and injection on the unified machine: exact delimiter counts, a real attack (`injection_is_real`), a refusal, and a fix that survives the same payload |
| `ConfTyping/FullCert.lean` | composable core, stage 1n | one checker, four certificates: `allcheck` produces budget, authorization, noninterference and memory safety in one pass — and `only_the_budget_lacks_a_loop_rule` names the one law that will not compose over loops |
| `ConfTyping/HeapAlloc.lean` | composable core, stage 1m | the last open question dissolved: because no guard may depend on a secret, the allocator stays synchronised, so **allocation loses its side condition** entirely |
| `ConfTyping/HeapWiden.lean` | composable core, stage 1l | widening for the tracked set: `narrowFix` computes a loop invariant by descending iteration, and `widening_beats_the_exact_rule` accepts a loop stage 1k had to refuse |
| `ConfTyping/HeapJoint.lean` | composable core, stage 1k | the judgment stage 1j forced: `JSecTy P V c V'` proves noninterference **and** memory safety in one induction, and `indexed_beats_the_conjunction` shows it certifies a program neither old checker could |
| `ConfTyping/HeapNI.lean` | composable core, stage 1j | noninterference meets the heap: High allocation is free, and `ni_and_memory_do_not_factor` finds the first pair of certificates that **cannot** be derived independently |
| `ConfTyping/MemLinear.lean` | composable core, stage 1i | `free` gets a rule under a **separating** invariant (`slcheck_no_fault`), and `memInv_not_preserved_by_free` proves stage 1h's missing rule was a genuine obstruction |
| `ConfTyping/MemCert.lean` | composable core, stage 1h | the language grows a **heap**, and memory safety arrives as a *separate* certificate (`umcheck_sound`, `umcheck_no_fault`) — added without touching any existing checker |
| `ConfTyping/BundleCoverage.lean` | composable core, stage 1g | what the bundle actually covers, projected out as theorems: **six** map rows, not three (`handler_covers_six_rows`) — a correction upward |
| `ConfTyping/BundleLoop.lean` | composable core, stage 1f | bounded loops enter the bundle: three lemmas pin down what an aborted run does (`uexec_dead_unchanged`, `uexec_dead_loop_diverges`, `uexec_dead_cost`), so `UCert.ofEmbedded` admits any certified While program — loops included |
| `ConfTyping/BundleLedger.lean` | composable core, stage 1e | the trusted base as a fourth bundle component, accumulating by `++` (`UCertL.seq`) — and row 7's CARRIED half turned from prose into a load-bearing ledger entry (`row7_carried_is_a_ledger_entry`) |
| `ConfTyping/UnifiedNI.lean` | composable core, stage 1d | noninterference on `UCmd` (`usecTy_sound`) — the third certificate, so `handler_three_certificates` carries a budget, mediation and NI at once |
| `ConfTyping/Bundle.lean` | composable core, stage 1c | one checker emitting a *bundle* (`ucheck`), one soundness theorem (`ucheck_sound`), and a worked handler carrying a cost budget **and** complete mediation at once (`handler_bundle_end_to_end`) |
| `ConfTyping/Unified.lean` | composable core, stage 1b | one language (`UCmd` = `WCmd` + `check`/`access`) carrying store, cost and authorization, with `uexec_embed_eq` proving the While development is a *fragment* of it, so brick results transfer (`ucost_of_cost`) instead of forking |
| `ConfTyping/Mediation.lean` | brick 35 / `VULN-COVERAGE.md` row 7 | complete mediation: missing authorization proved bypassable on an unguarded path (`victim_not_mediated`), a flow-sensitive check proved sound on every path and policy (`medCheck_sound`), and policy correctness proved *not* program-decidable (`policy_correctness_not_witnessed`) |
| `ConfTyping/CostBound.lean` | brick 34 / `VULN-COVERAGE.md` row 10 | resource exhaustion: a uniform cost budget, accumulation as a `GradedAction` (`cost_seq_is_mul`), algorithmic-complexity DoS proved (`dos_unbounded`), and uniformity restored by a constant-initialised budget (`budget_cost`) |
| `ConfTyping/Speculate.lean` | brick 33 / `VULN-COVERAGE.md` row 9 | speculative execution: a transient-execution machine with demonic misprediction — Spectre-v1 as a theorem (`spectre_leaks`), architecturally invisible (`arch_indistinguishable`), and a fence check whose soundness makes speculation observationally inert (`spec_inert`) |
| `ConfTyping/Race.lean` | brick 32 / `VULN-COVERAGE.md` row 8 | races and TOCTOU: a demonic-scheduling small-step machine — the attack (`toctou_interleaving_unsafe`), the atomic fix safe under every interleaving, and a decidable check that reduces the concurrent obligation to a sequential one |
| `ConfTyping/QueryEscape.lean` | brick 31 / `VULN-COVERAGE.md` row 3 | string literals with escapes: complete escaping proved sound and faithful, the unescaped-escape bug and the escaper/tokenizer convention mismatch proved injectable — escaping is a ledger entry (`escaping_no_silent_discharge`), parameterization is not |

## House rules learned the hard way

Three, each of which cost real time before being written down.

1. **This package is mathlib-free — define list/finite helpers locally.** Guessing which
   core lemma exists under which name (`List.mem_of_mem_filter`, `List.of_mem_filter`,
   `List.mem_of_elem_eq_true`) failed repeatedly. Brick 35 defines `memStr`/`interStr`
   and proves their two properties in nine lines; that is cheaper than one wrong guess.
2. **Per-module builds do not catch namespace collisions.** All ~1050 top-level
   declarations live in one flat `ConfTyping` namespace. `lake build ConfTyping.Foo`
   succeeds and `lake build` then fails at root import with "environment already
   contains …". `tools/check-claims.sh` guard 1aa now names both sites instead.
3. **A guard is not live until it has failed on purpose.** `tools/guard-selftest.sh`
   breaks the repo one way per guard family and asserts each fires. It exists because a
   guard was once spliced by an edit that silently did nothing, and its negative tests
   passed vacuously. Run it after touching `check-claims.sh`.

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
the command. The merge is **body-guided** (`findMerge2`): it merges the two classes
the body's transfer unified — the genuine join — landing on strict-intermediate fixed
points the blind first-two heuristic missed (`weak_accepted`/`weak_prog_safe`: the
loop that pinned the residual, now accepted and proved safe end to end). Residual:
loops with no coarsening fixed point reachable by iterated body-guided merging.

## String literals with escapes (`QueryEscape.lean`) — escaping is a ledger entry

Brick 31 takes the last named depth follow-on on the injection axis. Bricks 14 and
26 tokenized without an escape mechanism, so the only safe value was a quote-free
one — and every real database disagrees. Escapes enter the model as a three-state
scanner over brick 14's own alphabet (the backslash is the character at code 92),
and `segsT_noBS`/`skeletonE_eq_skeleton` prove it a **conservative extension**:
identical to brick 14's tokenizer on backslash-free strings, so bricks 14 and 26
re-derive inside it (`param_correct_esc`, `concat_injectable_esc`).

`segsT_esc` is the heart — scanning a completely-escaped value inside a literal
consumes exactly that value and stays inside, with *no hypothesis on the value* —
so `segsE_buildEsc` gives `[pre, v, suf]` for every `v`, lifting brick 14's
quote-freeness restriction. Hence `esc_immune` (integrity NI: the executed skeleton
is constant) and `esc_faithful` (the value delivered is `v` unchanged — safety is
not bought by corrupting data). The classic bug is bracketed on both sides:
`escBad_injectable` (axiom-free) is the `\'` attack on an escaper that misses the
escape character, and `escBad_noBS_ok` proves that same escaper sound on
backslash-free values.

The point of the brick is the pair of mismatches. Against the SQL-standard
doubled-quote tokenizer the backslash escaper is injectable
(`esc_mismatch_injectable`); against the backslash tokenizer the doubling escaper is
injectable (`escDouble_mismatch_injectable`) — while each is sound for its own
convention (`esc_skeleton`, `escDouble_skeleton`), all four bundled as
`escaping_is_convention_relative`. So "the value is escaped" is not a security
property of the value or of the escaper; it is a property of the pair, i.e. an
**assumption** — and brick 4's ledger already handles those. `esc_cond_immune` gives
the conditional certificate for every sink tokenizer relative to the one-entry
ledger `Sat [T = segsE]`; `esc_not_unconditional` shows the unconditional one is
false at a mismatched sink; `escaping_no_silent_discharge` is
`ledger_no_silent_discharge` on the injection channel. Parameterization needs the
**empty** ledger (`param_immune_no_ledger`) because no value ever reaches the
tokenizer, and `escaping_reducible_parameterization_in` states the verdict as one
theorem: the distance between "escape your inputs" and "use prepared statements" is
exactly one load-bearing ledger entry. Honest limit: two conventions modeled, and
the no-go is exhibited on that pair rather than proved for all escapers.

## Races and TOCTOU (`Race.lean`) — the class the map called OUT-OF-MODEL

Brick 32 builds row 8's named extension: a nondeterministic small-step semantics
with demonic scheduling. Threads are lists of indivisible instructions over a
shared store with private registers, and a **schedule is a list of thread
indices** — so nondeterminism is data. "Under some interleaving" is an existential
a witness discharges by `decide`; "under every interleaving" ranges over all index
lists, unfair and repetitive ones included.

The fine grain is the phenomenon. Two threads run the textbook check-then-act
withdrawal — `load` the balance, `guard` that it covers 60, `decsh` debit 60 —
against a balance of 100. `toctou_interleaving_unsafe` (axiom-free): under
`[0,0,1,1,0,1]` the balance ends at **−20**, because both threads read 100 and
both pass the guard before either debits. `sequential_model_misses_races`
(axiom-free) is the other half, and the more interesting one: *both* sequential
schedules of the same program are safe, so a proof in the sequential semantics is
true of a machine the program does not run on. That is §0's model gap as a
theorem rather than a caveat.

The fix is an `atom` — the critical section as one scheduling step — and
`atomic_all_schedules_safe` proves the invariant under **every** schedule, by
induction over the interleaving rather than by sampling. It is generated:
`racefree` is a decidable rule (no bare shared write outside a critical section),
`racy_rejected`/`atomic_accepted` decide it, and `racefree_all_schedules` is the
soundness theorem — a **reduction**, and the point of the brick. For a checked
pool, "the invariant survives every interleaving" follows from "each critical
section preserves the invariant", an ordinary sequential obligation in which no
schedule appears; `racefree_poolPreserves` supplies the syntactic half (a step
that does not write shared state cannot break a shared-state invariant) and
`poolPreserves_step`/`rrun_preserves` carry it across the schedule.

Honest limits, all real: safety only — no fairness, liveness or deadlock; `atom`
is an idealized critical section, not a lock protocol; the memory model is
sequentially consistent; the per-section obligation is a genuine residual
(`bad_atom_not_preserving` and `bad_atom_accepted` witness an atomic-but-wrong
section that the checker accepts and that breaks the invariant); and
2-safety *over* interleavings — information flow under scheduling — stays open,
since determinism is still load-bearing for the confidentiality gate.

## Speculative execution (`Speculate.lean`) — the last OUT-OF-MODEL row

Brick 33 runs §0's recipe a third time, after timing (brick 2) and scheduling (brick 32).
The machine splits state: an **architectural** part that rolls back, and a
**microarchitectural** address trace that does not. A `brLt` branch may be mispredicted,
running its body transiently for a window taken from a **misprediction schedule** — a data
parameter, so `∃ misprediction` is decidable on a witness and `∀ misprediction` ranges over
unbounded windows.

The victim is the textbook gadget: `if i < 4 then (x := mem[i]; y := mem[x])`, where the
second load's *address* is the first load's *value*. With `i` out of bounds the guard is
false. `spectre_trace_is_the_secret` pins the traces at `[8,42]` and `[8,99]` for two
memories differing only at the secret, so `spectre_leaks`; `leak_needs_window_two` shows
the channel has depth — a one-instruction window leaks only the public index.

`arch_indistinguishable` is the other half, and the point: architecturally nothing runs, so
those two memories are *identical*. `speculative_model_misses_it` pairs them — the program
is secure on the machine the earlier bricks describe and insecure on the machine it runs
on. This is §0's model gap in its sharpest form, the architectural semantics not merely
coarse but silent.

The fix is a `fence`, and the soundness is strong: `specCheck_sound` proves the speculative
registers *and* trace **equal** the architectural ones under every schedule
(`spec_inert`), so speculation is observationally inert and `arch_ni_transfers` carries any
architectural noninterference over verbatim. That is what makes the row compose with the
rest of the map. `victim_rejected`/`fixed_accepted` decide the check;
`fixed_secret_independent` closes it end to end.

Honest limits: the microarchitectural state is an address trace — no cache-line
granularity, eviction, timing or contention — so what is excluded is the address-visible
channel, not every physical side channel. Only v1 (no indirect branches, no store-to-load
forwarding), rollback is perfect, and nested speculation is excluded **by the syntax**
(branch bodies are a separate instruction type) rather than dropped by the semantics. The
check is sufficient but not necessary: `benign_rejected` with
`benign_transient_is_constant` exhibits a rejected body whose transient trace is provably
constant, so the refinement is a follow-on, not a soundness gap.

## Resource exhaustion (`CostBound.lean`) — the cost bound as a graded certificate

Brick 34 proves row 10's [classified] reduction and corrects one clause of it. The
property is **uniformity**: `CostAtMost c k` quantifies over *all* inputs and *all* fuel,
so algorithmic-complexity DoS is the failure of uniformity, not the absence of a bound.

`costGA : GradedAction Nat Nat` — grade composition `+`, action `+`, order `≤` — is a
checked instance of the interface's own accumulation algebra, and `cost_seq` /
`cost_seq_is_mul` prove budgets add as `costGA.mul`. This is the first time a *security*
row lands directly in the transport calculus's algebra rather than beside it.
`costCheck` + `costCheck_sound` generate budgets for the loop-free fragment.

`countdown_cost` bounds the canonical countdown by `1 + v·(kc+3)` in the counter's
initial value — a bound that exists per input and grows with it, which is the DoS
surface. `spinU_cost_lb` turns that into `dos_unbounded`: **no** uniform budget exists
for a loop counting down untrusted input. Worth noting what this catches that nothing
else does — the victim is memory-safe, injection-free and noninterferent, so every
earlier brick certifies it. `budget_cost` restores uniformity when the counter is
initialised from a constant, and `dos_unbounded_budget_bounded` is the pair.

**Correction of record.** Brick 1 called this "`Bridge.ofModulus` territory". The
`GradedAction` half is right and now proved; the `Bridge` half is wrong — a `Bridge`
certifies a *binary* quantity (`dist (map x) (map y) ≤ act cert (dist x y)`) and a cost
budget is *unary*. The accumulation transfers; the contraction does not.

Honest limits: halting runs only (availability is liveness-shaped and still not
claimed), the canonical countdown only (general ranking analysis stays external, so the
verdict keeps "REDUCIBLE in general"), and instrumented steps rather than wall clock.

## Complete mediation (`Mediation.lean`) — the split row 7 was hiding

Row 7 carried the map's last `[classified]` grade, on the reasoning that π's correctness
"is not a theorem anywhere". That is true of *policy correctness* — and it was swallowing a
second, different property. CWE-285's actual defect, and CWE-306's, is almost never "the
policy was wrong"; it is **missing mediation**: some path reaches the protected operation
without passing the check. That is a program property, on every path, and decidable.

`check r` consults the policy and aborts if refused; `access r` is the protected read;
`branch` offers two routes with the path as a data parameter — the demonic device of bricks
32 and 33. `med_victim_bypasses`: on the unguarded branch, under a policy that *denies* the
resource, the read happens anyway. `victim_guarded_path_is_fine` shows the other branch
aborts cleanly, which is the point — the program *contains* a correct check, just not on
every route, so mediation is a whole-program all-paths property.

`medCheck` is a flow-sensitive analysis carrying the authorized set and intersecting at
joins; `medCheck_sound` proves a checked program reads only what the policy permits, on
every path and under every policy, via a three-part invariant (everything authorized is
permitted, everything read is permitted, the static set under-approximates the dynamic one).

`policy_correctness_not_witnessed` proves the *other* half is not program-decidable: two
policies, the same checked program, both mediated, different reads. So
`mediation_generated_policy_carried` states the split as one theorem — mediation generated,
policy carried, and now the carrying is demonstrated rather than asserted.

Honest limits: nesting is excluded by the syntax; the join intersects, so the check is
sufficient not necessary; and the model has no *subject*, so "authorized for this
principal" — IDOR, CWE-639 — is a named follow-on. `memStr` and `interStr` are defined and
proved locally, the package being mathlib-free.

## The composable core (`Unified.lean`) — stage 1b

Measured weakness: the security program defines **sixteen** instruction types across thirty
modules with **zero** cross-brick composition — no module mentions two brick languages, and
the only bridge is brick 7's `embed : Cmd → WCmd`. Thirty-five bricks each prove "for *my*
toy language this class is excluded", so no program carries two guarantees at once. That
undercuts the repo's headline exactly where the goal needs it.

Stage 1a (in `transport-calculus`) added the algebra: `GradedAction.prod` and
`Bridge.pair_comp_cert` — bundles accumulate componentwise, no interaction term. This stage
adds the object. `UCmd` is `WCmd` plus `check` and `access`; the state gains `auth`, `reads`
and `dead`. A refused check aborts and every later step becomes a no-op, so "nothing is read
after a refusal" holds *definitionally* — checked in the model: after a refusal the later
`access` reads nothing **and** the later assignment does not fire.

The load-bearing theorem is `uexec_embed_eq`: on the image of `uembed`, started live, the
unified machine's store, cost and branch trace are **exactly** `wexec`'s, and `auth`,
`reads`, `dead` are untouched — one equation. So the While development is a fragment of this
one rather than a parallel copy, the standard brick 7 set with `wexec_embed_eq`, applied a
level up. Two transfers follow at once: `ucost_of_cost` (a brick-34 budget is a budget here,
no reproof) and `uembed_mediated` (a program with no `access` reads nothing, so the new
dimension cannot be violated by code that predates it).

The new dimensions are live rather than decorative: `uVictim_not_mediated` shows an
unchecked read is expressible and fails mediation, while `uFixed_refused_reads_nothing` and
`uFixed_permitted_reads` show the policy actually decides.

Honest scope: this builds the object and the transfers. It does **not** yet re-derive the
checkers on it — stage 1c retargets noninterference, cost and mediation onto `UCmd` and
proves one program carrying all three composed certificates. The existing bricks are not
superseded; they remain the record of what was proved, and the transfers make them reusable.

## The composable core (`Bundle.lean`) — stage 1c, the artifact

Stage 1a gave the algebra, 1b the object. This closes the loop: **one checker** over
`UCmd` emitting a bundle, **one** soundness theorem, and a program that carries it.

The two certificates were chosen because they compose by genuinely different laws — which
is the point of bundling. A **cost budget** is graded, accumulating by `costGA.mul` (`+`).
An **authorization transformation** is a Hoare triple `{A} c {A'}`, accumulating by
*threading*. `UCert A c A' k` carries both, and `UCert.seq` shows the halves advancing
independently: budgets add, authorization sets thread, neither mentions the other. That is
`Bridge.pair_comp_cert`'s "no interaction term", concretely. `UCert.ite` joins by
intersecting the authorization sets and taking the worse budget.

`ucheck` is the single decidable analysis emitting both; `ucheck_sound` is the single
soundness theorem. `handler` — authorize, read, compute, conditionally log — passes with
`ucheck [] handler = some (["db"], 6)` by `decide`, and `handler_bundle_end_to_end` reports
the budget **and** complete mediation. **The first program in this repo holding two
guarantees at once.**

Three witnesses make it concrete rather than nominal. `handler_budget_tight`: the certified
budget is 6 and the permitting run spends 6, so the bound is not slack padding.
`handler_partial_policy`: under a policy permitting the database but refusing the log, the
handler reads `["db"]` and goes `dead` before the log — mediation tracks resources
individually, it is not an all-or-nothing gate. `handler_without_check_rejected`: drop the
`check` and the analysis says `none`.

Honest scope. **Two certificates, not three** — noninterference is not retargeted. Lifting
it needs a low-equivalence on `UState` and a decision about whether `reads` and `auth` are
observable: a design question, not a transcription, and naming it beats rushing it. For
embedded While programs NI still transfers via stage 1b. **Loop-free only** — `ucheck`
returns `none` at a `loop`, exactly as brick 34's `costCheck` does; lifting brick 34's
constant-initialised `budget` construct is the follow-on.

## The composable core (`UnifiedNI.lean`) — stage 1d, the third certificate

Stage 1c stopped at two because lifting noninterference needed a **design decision**, not a
transcription: which parts of a `UState` can a Low adversary see? The answer taken, and it
is load-bearing: the Low `store` (as always); `reads` **observable** — which resources a
request touches is visible, the same premise brick 33 used for cache lines and brick 29 for
log records, so denying it here would contradict the rest of the map; `dead` **observable**
— a refused request is visible to whoever made it; `auth` **not** observable, being internal
bookkeeping whose outward effect is already carried by `reads`.

With that fixed the result is slightly surprising: **`check` and `access` add no flow
channel**. Their resource names are syntactic constants, so the reads a run performs and
whether it dies are determined by control flow and policy — both already Low-determined for
a well-typed program. The two constructors are unconditionally well-typed and `WSecTy`'s
whole discipline carries over (`usecTy_sound`, a fuel-and-two-run induction mirroring
`wsecTy_sound`).

The claim has a sharp edge, and `access_is_static_by_design` records it rather than hiding
it: this holds *because* there is no `access (e)`. Store-dependent resource selection would
make `reads` a genuine flow channel and both rules would need side conditions — that is
IDOR-shaped, and it was already the named follow-on from brick 35.

**`handler_three_certificates`** is P1's deliverable: one program carrying a cost budget,
complete mediation, and termination-sensitive noninterference, composing by three different
laws — budgets add (`costGA.mul`), authorization sets thread (Hoare), NI is conjunctive.
`Psec_rejects_leaks` keeps it honest: `secret` really is High, the handler's own variable is
Low, and both branching on the secret and laundering it through a Low variable are rejected
— so this is a claim about a program that *could* have leaked and does not.
`secret_loop_still_rejected` confirms brick 7's termination channel is still closed.

## The composable core (`BundleLedger.lean`) — stage 1e, does it scale?

Three certificates is suggestive; the design claim — no interaction term, so `n`
guarantees cost `n` independent accumulations — is only tested by adding a fourth. It
slots in, and `UCertL.seq` is four lines. That is the evidence.

The fourth is not decoration: it is **the trusted base**, brick 4's ledger lifted to the
bundle, accumulating by list append — a fourth genuinely different monoid after `+`, Hoare
threading and conjunction. `four_laws_one_composition` states all four advancing through
one `seq`.

The payload is a debt the map was carrying in prose. Brick 35 split row 7 into *mediation*
(generated) and *policy correctness* (CARRIED, since `policy_correctness_not_witnessed`
shows no program can decide it). The bundle's mediation certificate says "every read is
π-permitted" — a **security** statement only if π is the policy the specification intended.
That gap was a paragraph. Now:

- `handler_intended_reads` — given the ledger entry, the handler reads only what the
  specification *intends*, not merely what the deployed policy permits;
- `handler_needs_the_policy_assumption` — and the entry is load-bearing: with a permissive
  deployed policy and a restrictive specification, the same program, unchanged and still
  carrying all three certificates, reads something unintended;
- `row7_carried_is_a_ledger_entry` — both halves as one theorem.

So CARRIED is no longer a caveat in prose. It is an entry in a ledger that appends under
composition and cannot be silently discharged — the discipline the repo is named for,
applied to its own bundle.

## The composable core (`BundleLoop.lean`) — stage 1f, loops

Every stage so far carried the same limit: `ucheck` returns `none` at a `loop`. That is
brick 34's limit inherited, and brick 34 also showed the way out — a countdown whose
counter is initialised from a constant has an input-independent budget.

One obstacle had to be cleared first, and it is the interesting part. A bundle's budget
must hold from **any** starting state, including an aborted one, or `UCert.seq` cannot
compose: the first component may abort and hand a dead state to the second. So what does
an aborted run do? Three lemmas settle it, and they are worth having anyway.
`uexec_dead_unchanged`: from a dead state **no command changes the state at all** — the
abort is total, not merely read-suppressing. `uexec_dead_loop_diverges`: a dead run inside
a loop whose guard holds never returns, because the store is frozen so the guard can never
become false. `uexec_dead_cost`: hence an aborted run's cost is bounded by a static
`deadCost`, loops contributing 1 since the only terminating case is a guard already false.

With those, `UCert.ofEmbedded` admits any separately-certified While program by splitting
on live (where `uexec_embed_eq` hands the While development over wholesale) versus dead
(where the three lemmas apply). `handlerBounded` is the payoff — authorize, read, then do
at most five units of constant-budgeted work — still carrying its certificates, and
`handlerBounded_contains_a_loop` confirms a `loop` really is in there.

`handlerBounded_numbers` records an honest difference from stage 1c: the certified budget
is 22 and the permitting run spends 19, so unlike the straight-line handler's *tight*
bound this one over-approximates by 3 — the price of an analytic bound across a loop. The
refused run costs 4 and shows the lemmas at work: the abort suppresses the counter's
initialisation, so the guard is already false and the loop exits at once rather than
spinning.

Still outstanding: this admits loops *already certified as While programs*, so the counter
must be constant-initialised and the body check-free. A loop containing a `check` can go
dead mid-iteration, which the analysis covers only by divergence, not by a bound. General
ranking-function analysis remains external, exactly as brick 34 said.

## The composable core (`BundleCoverage.lean`) — stage 1g, a correction upward

Stages 1c–1f were described as carrying "three certificates", and the map was updated to
say so. That under-counted, and not as a matter of interpretation: the observation in
`uOptLowEq` includes the **cost** and the **halting bit**, so one application of
`usecTy_sound` discharges three separate map rows at once — exactly as bricks 3, 5 and 7
did for the While language, which is where the observation came from.

The coverage is now checkable rather than asserted, each row projected out of a certificate
the bundle already had: `bundle_covers_store` (row 1), `bundle_covers_timing` (row 2 —
Low-equal runs cost *exactly the same*), `bundle_covers_termination` (row 13 — they halt
together), `handler_mediated` (row 7), the budget (row 10), and `bundle_covers_seam`
(row 12 — this is what `UCert.seq` *is*, so the row is carried by construction).
`handler_covers_six_rows` states it for the worked handler. Stage 1e's ledger also supplies
row 11's *mechanism*, though not its class.

Six of sixteen — and the other half is kept in the same file so the two cannot drift apart.
`UCmd` has no strings and no heap, so rows 3, 6 and 14 are not *expressible* here at all,
and rows 8, 9 and 11 are proved on their own machines in bricks 32, 33 and 4. That is left
in prose deliberately: "the language has no strings" is a syntactic fact about an inductive
type, and dressing it up as a theorem would produce something vacuous that looks like
evidence.

## The composable core (`MemCert.lean`) — stage 1h, the language grows

Stage 1g named the obstacle: the remaining rows need a bigger language. `UCmd` gains one
constructor — `memop : MemOp → String → UCmd`, bundling `alloc`/`deref`/`free` so every
downstream match takes **one** new case rather than three — and `UState` gains a heap, a
live-address list, a fresh counter and an `err` flag. Pointers are ordinary `Int` values in
the existing store, so the value domain did not change; that is why memory safety was
reachable and injection was not.

**The design decision worth naming**: memory safety is *not* folded into `ucheck`. It gets
its own analysis and its own certificate. That is the honest test of stage 1a's claim — a
new property, added later, should not require touching the original checker. It did not:
`ucheck` gained a single conservative line (`none` at a `memop`), `USecTy` gained none, and
nothing else in stages 1c–1g was modified. The certificate is again a Hoare triple
`{V} c {V'}`, this time on the variables known to hold a live pointer, so it threads under
`seq` and intersects at a branch — the same shape a third time.

`umcheck_no_fault` is the guarantee: a checked program never faults. Four witnesses keep it
concrete — `wild_deref_rejected` and `wild_deref_faults` (the rejected program really does
fault, so the check is not refusing something harmless), `alloc_then_deref_ok`, and
`clobbered_pointer_rejected` (overwriting a pointer drops it from the tracked set, so the
analysis is not fooled by an intervening assignment).

Two limits, both recorded as theorems rather than footnotes. `free_has_no_rule`: `free` is
in the syntax and the semantics, so use-after-free is *expressible*, but dropping an address
from `live` invalidates every alias, and soundness needs brick 12's linearity or brick 19's
must-alias tracking in the invariant — so this closes the wild-access half of row 6
(CWE-119) and not the use-after-free half (CWE-416). `memops_not_yet_NI_typed`: `alloc`
writes the fresh counter into the observable store, so heap ops are not NI-typed; whether
allocation addresses are Low-visible is the same question stage 1d settled for `reads` and
deserves the same care rather than a guess.

## The composable core (`MemLinear.lean`) — stage 1i, `free`, and why 1h could not have it

Stage 1h left a hole on purpose and named it: `free` in the syntax and the semantics,
no typing rule, `free_has_no_rule`. Stage 1i does two things, and the second is the
one worth the module.

**It closes the hole.** `SepInv` adds two conjuncts to `MemInv` — tracked variables
hold *pairwise distinct* addresses, and every live address is below the allocation
counter. With those, `free` has a rule: freeing `x` removes one address from `live`,
and every other tracked variable survives precisely because separation says its
address is a different one. `slcheck_no_fault` then extends memory safety to programs
that deallocate, which is row 6's use-after-free half (CWE-416). The freshness
conjunct is what makes `alloc` re-establish separation: the new address is
`s.fresh`, everything live is strictly below it, so the new pointer is provably new.

**It proves the hole was real.** `memInv_not_preserved_by_free` exhibits a concrete
state satisfying stage 1h's `MemInv` in which one `free` step lands in a state
violating it — `q`'s address deallocated underneath it. So the missing rule was not an
unfinished proof; the weaker invariant is not inductive for `free`, and no work on
`MemCert` could have added it. A limit recorded as a theorem is now *explained* by one.

One honest note, kept in the module. The separation conjunct is load-bearing in the
proof and unreachable in the language: `assign` always drops its target, so this
`UCmd` cannot construct two tracked aliases. But soundness quantifies over every state
satisfying the invariant, not only reachable ones, and the witness above is exactly
such an unreachable-but-admissible state. Restricting to reachable states would trade
a two-line conjunct for a global reachability argument and would break the moment the
language gained a pointer-copying assignment.

`slcheck_extends_umcheck` records that this is a conservative extension — everything
stage 1h accepted, stage 1i accepts, with the same tracked set — and
`SepInv.toMemInv` lets a stage-1h consumer keep the weaker invariant. Witnesses:
`use_after_free_rejected` with `use_after_free_faults` (the rejected program really
does fault), `double_free_rejected_by_slcheck`, `alloc_free_ok`, and
`free_one_keep_other` (freeing one of two pointers leaves the other usable, so the
rule is not conservative to the point of uselessness).

## The composable core (`HeapNI.lean`) — stage 1j, where the certificates stop factoring

Stage 1h carried `memops_not_yet_NI_typed` with a reason: `alloc` writes the fresh
counter into the observable store. That reason was right only for a *Low* target, and
stage 1j corrects it. Three findings, in increasing order of interest.

**High allocation is free.** `fresh` and `live` are not in the observation, so
allocating into a High variable is invisible — `USecTy.allocH` is sound with no change
to `uLowEq` whatsoever. `heapProg_two_certificates` is the first heap program carrying
noninterference *and* memory safety at once.

**Low allocation is the open question.** `allocL_would_be_unsound` exhibits two
Low-equal states at different points of the allocation sequence: allocate into a Low
variable and the difference is published. Typing it needs `fresh` in the observation,
which is a decision about what the adversary can see — left open deliberately, not
left undone.

**`deref` and `free` can never have an unconditional rule.** Not for stage 1h's
reason: they can *fault*, the fault sets `dead`, and `dead` is observable.
`deref_leaks_through_dead` separates a Low-equal pair with a single `deref` on a High
variable. No refinement of a syntactic judgment fixes this, because whether the step
faults is a property of the state. What they do have is `deref_NI_given_safety` — they
are noninterferent on states satisfying the memory invariant, and the hypothesis is
literally the other certificate.

That last pair is the finding. Stages 1c–1e established four accumulation laws with no
interaction term, and `Bridge.pair_comp_cert` was read as "carrying n properties costs
n independent accumulations". `ni_and_memory_do_not_factor` shows that reading does not
extend to the heap: NI for `deref` is *conditional* on memory safety, so the two cannot
be certified side by side and conjoined at the end. The consequence is concrete — a
combined checker cannot be `ucheckNI P c && slcheck V c`; the judgment must be indexed
by the tracked set so the NI rule for `deref x` can demand `x ∈ V`. That is a new
inductive, not a conjunction, and it is a design conclusion reached by counterexample
rather than by preference. Both places that made the independence claim
(`Bridge.pair_comp_cert`, `four_laws_one_composition`) now carry the qualification next
to the claim.

## The composable core (`HeapJoint.lean`) — stage 1k, the joint judgment

Stage 1j proved the two properties do not factor and said exactly what to build
instead. `JSecTy P V c V'` is that: a four-place relation carrying the partition *and*
the tracked set, so the noninterference rule for `deref x` can demand `x ∈ V` — the
side-condition neither system could state alone, since `USecTy` has no `V` and
`SepCert` has no `P`. One induction (`jsecTy_sound`) proves both guarantees, with the
memory invariant appearing as a **hypothesis of the noninterference proof**. That is
the formal content of "these do not factor".

`indexed_beats_the_conjunction` is the payoff, on `safeHeapProg` — allocate into a
secret, dereference it, mediate an access, free it. `ucheckNI` rejects the program
outright, so no NI certificate is available from it at any partition; `slcheck` accepts
it but says nothing about leaks; `jcheck` certifies both. The indexed judgment is not a
repackaging of its parts — it proves what their conjunction cannot, which is what
stage 1j predicted from a single counterexample.

Getting here needed `SepCert.loop`, a loop rule for the memory certificate that stages
1h and 1i both ducked (`umcheck` and `slcheck` return `none` at a loop). It is a fuel
induction with the tracked set as the loop invariant. It went in this module rather
than as a back-patch to `MemLinear`, so stage 1i's claims stay exactly as audited.

Two rules stay conservative, both argued for before being implemented. `allocL` is
still absent — it needs `fresh` in the observation, stage 1j's open question, with
`allocL_would_be_unsound` as the witness that it cannot just be added. And a loop must
preserve the tracked set *exactly*, so `allocating_loop_rejected`: a loop that
allocates is refused although nothing about it is unsafe. The fix is a widening step —
iterate the body's effect to a fixed point, as brick 30's `loopFix` does for intervals
— which is real work rather than a missing line, so it is named rather than hidden.

## The composable core (`HeapWiden.lean`) — stage 1l, widening

Stage 1k refused a loop whose body changed the tracked set, and named the fix rather
than hiding it: iterate the body's effect to a fixed point, as brick 30's `loopFix`
does for intervals. This is that step on a different lattice — the first time that
fixpoint idea serves a second client.

The tracked set is a **must** set, so weakening means *shrinking* and the fixed point
is reached by descending iteration: start at the entry set, intersect with the body's
effect, repeat. `narrowFix_spec` extracts exactly the two side-conditions
`JSecTy.whileW` needs — the result is inside the entry set, and the body maps it into a
superset of itself. Because the sets shrink and are finite, `V.length + 1` steps always
suffice, so the budget is computed rather than guessed
(`narrowing_budget_is_computed`).

`widenProg` is the payoff and deliberately not a toy: allocate `p`; loop, allocating
`q` and dereferencing `p` each time round; dereference `p` again afterwards. The body's
tracked set grows, so stage 1k's checker refuses it — and `p` has to survive the loop
for the final dereference to be typable at all. `widening_beats_the_exact_rule` shows
both halves: `jcheck` returns `none`, `jcheckW` returns `["p"]`.

**Why a fuel index and not well-founded recursion.** The narrowing call sits under a
closure, which structural recursion on the command cannot see through. Recursing on
fuel keeps the definition structural, and structural definitions kernel-reduce — so
every witness here is still a `decide`. The well-founded version was written first, and
it type-checked, but it broke `decide` on all of stage 1k's witnesses: the same trap
nested inductives set in bricks 32, 33 and 35. `jcheckW_out_of_fuel` records that
exhausting the fuel is a refusal, never an acceptance, so the index can only make the
analysis more conservative.

Stage 1k's `jcheck` is left exactly as audited — its theorems and `decide`-checked
witnesses stand unchanged, including `allocating_loop_rejected`, which
`allocating_loop_now_accepted` pairs with rather than replaces.

One item survives from the conservatism list, and it is the design question rather
than an engineering gap: `allocL` is still absent, because it needs `fresh` in the
observation. `HeapNI.allocL_would_be_unsound` is the standing witness.

## The composable core (`HeapAlloc.lean`) — stage 1m, the last question dissolved

Stage 1j left one item and framed it as a design fork: allocation into a *Low*
variable publishes the counter, so `allocL` looked like it needed `fresh` in the
observation — a decision about the adversary, with a public allocator and an
address-renaming bisimulation as the honest options.

Neither was needed. This type system has **no High-guarded control flow**: every `ite`
and `loop` guard must be `exprLow`. So two Low-equal runs perform the same allocations
in the same order, and their counters never drift. `jsecTy_sound` now carries
`s.fresh = s'.fresh` as a **relational invariant** rather than as an observation, and
allocation becomes noninterferent with *no side condition at all*. Stage 1m therefore
removes a hypothesis instead of adding a rule: `JSecTy.allocH` becomes `JSecTy.alloc`,
and `jcheck`'s allocation case loses its test.

The public statements are unchanged. `uOptLowEqA.toLowEq` projects the strengthened
relation back down, and two runs starting from `initU` agree on the counter for free —
so `jcheck_gives_both` and `jcheckW_gives_both` read exactly as they did.

Two theorems keep the argument honest, because "the invariant holds" is easy to assert
and easy to get wrong. `allocation_sync_is_load_bearing`: stage 1j's
`allocL_would_be_unsound` is *still true* — nothing was refuted, and it is now precisely
the statement that the invariant cannot be dropped. And
`high_branch_desynchronises_the_allocator` with `highBranch_is_untypable`: one
secret-guarded branch makes the counters differ, and that branch is untypable here,
which is *why* the rule is sound. If `UCmd` ever gains High-guarded control flow, that
pair breaks the build rather than silently invalidating `JSecTy.alloc`.

**The conservatism list is now empty.** Stage 1j opened three items — High allocation
(closed there), `deref`/`free` (closed in 1k by indexing the judgment), `allocL`
(closed here) — and stage 1k opened one more, the exact loop rule, closed in 1l by
widening. What remains is *scope*, not conservatism: `UCmd` has no strings, and the
budget/mediation/ledger certificates are carried by `UCert` rather than `JSecTy`.

## The composable core (`FullCert.lean`) — stage 1n, one checker, four certificates

Stages 1c–1e built a bundle carrying a budget, an authorization set and a ledger;
stages 1h–1m built a joint judgment carrying noninterference and memory safety. They
were separate artifacts — `ucheck` refused every heap operation and `jcheck` said
nothing about cost — so no single program had ever carried all of them.

`allcheck` does. One pass yields the authorization set, the tracked pointer set and the
cost bound; `allcheck_sound` turns that into a `FullCert`. `fullProg` is the artifact
the 1a–1n arc was for: check a permission, allocate, read the mediated resource,
dereference, assign, free — **four certificates from one run of one checker**, with a
budget that is *tight* (`fullProg_runs`: certified 6, spends 6). `fullProg_needs_its_check`
confirms the mediation half is load-bearing rather than decorative.

Most of this is integration: stages 1c–1e had already established that these laws do
not interact, so merging them was expected to work, and it did.

**The part that was not integration.** Extending the budget to heap operations needed a
new rule, `UCert.memop` — stage 1h's `none` was a placeholder, not a limit — and
writing it exposed an asymmetry that two separate `none`s had been hiding. Three of the
four certificates have loop rules: `JSecTy.whileW` (1l), `SepCert.loop` (1k), and
mediation threads through unchanged. **The budget does not, and cannot**: a cost bound
over a loop requires an *iteration* bound, which is a termination argument rather than
a typing side-condition. `only_the_budget_lacks_a_loop_rule` states it, and
`loops_carry_three_of_four` shows the split is about which certificates a loop can
carry, not about which programs are safe. Brick 30's `loopFix` and stage 1f's
`countdown` are the two ways to supply the missing ingredient, and both are analyses of
a different kind — so this is a boundary, not a to-do.

The honest summary of the composable core: four certificates, one checker, on the
loop-free fragment; three of the four on loops.

## The composable core (`TaintCert.lean`) — stage 1o, strings and injection

Every stage since 1h repeated the same limit: `UCmd` has no strings, so injection and
path traversal are not *expressible* on the unified machine. Stage 1o adds the missing
value domain — `UCh`, `UStr`, `SExpr`, and one new command constructor `sop` (set a
string variable, or emit to a sink), which rippled a single new case into fourteen
existing matches.

**The alphabet is two symbols, and that is the problem rather than a simplification of
it.** An injection succeeds by contributing a *delimiter* the query's author did not
intend, so `UCh` is exactly "delimiter or not". Everything else about a character is
irrelevant to the attack, and two symbols keeps every witness a `decide`.

**The certificate tracks exact counts, not a taint bit.** A taint bit is too coarse to
be usable: a query variable legitimately contains delimiters — `name='` has one — so
"clean vs tainted" would reject every real query. `TaintEnv` maps a string variable to
the exact number of delimiters it holds, `scount` computes an expression's count
symbolically, and `sanStr` is the single discharge that turns an unknown count into
zero. The guarantee is structural: every emitted string carries exactly the number of
delimiters the analysis predicted, so untrusted input cannot change the query's shape.

The row is four theorems. `injection_is_real` — run the vulnerable program on a
malicious input and it emits a string with **three** delimiters where two were written;
the shape changed, which is the injection itself and not a proxy for it.
`injection_rejected` — the checker refuses it, and refuses at the `emit`, which is where
the injection happens. `sanitised_query_checks` — the fix is accepted with the count
pinned at two. `sanitised_query_holds_under_every_input` — and that holds for *every*
attacker input, not the one payload.

Three scope limits, all deliberate. The sink is **not** in the noninterference
observation, so `JSecTy` still has no rule for `sop`: a checked program's *structure* is
guaranteed, its confidentiality is not. Loops have no rule — the count environment needs
the narrowing stage 1l gave the tracked set, which is mechanical but a stage of its own.
And every other checker (`ucheck`, `jcheck`, `allcheck`) returns `none` at a `sop`, so a
string program cannot yet carry the other four certificates; merging `tcheck` into
`allcheck` is the obvious next step and is packaging, not discovery.

Path traversal is now *expressible* but not done. It is the same shape with `/` and `..`
in place of the delimiter, and claiming it without writing it is exactly the drift the
guards exist to catch.

## The composable core (`AllFive.lean`) — stage 1p, the sink becomes observable

Stage 1o left the sink **outside** the noninterference observation. That was a real
weakness rather than a scoping choice: a sink is an *output channel*, so leaving it
unobserved made every string operation trivially noninterferent, and a program could
emit a secret and still be "noninterferent". Stage 1p puts it in. `uLowEqA` gains the
Low part of the string store and the sink, `JSecTy` gains `setH`/`setL`/`emit`, and
`jsecTy_sound` threads two more conjuncts through every case.
`emit_of_secret_rejected` is the leak that is now caught.

**`san` is not declassification**, and that is this stage's security decision.
Sanitising removes *delimiters*, not *secrets*. `sanitising_does_not_declassify` makes
the point sharp: `emit (san secret)` is structurally perfect — count zero, it cannot
break a query — and still leaks. The taint checker accepts it; the noninterference
checker refuses it. Neither is wrong; they answer different questions, which is the
argument for carrying both.

**The fifth certificate factors, unlike the third.** Stage 1j found noninterference and
memory safety could not be established separately and conjoined, forcing the indexed
judgment of 1k. Structural integrity is not like that: the two conditions an `emit`
must meet — a known delimiter count, and a Low value — constrain different parts of the
state. So `xcheck` is a *pairing* (`factoring_holds_here`) rather than a sixth judgment.
Worth recording both: "these compose" is not a default one may assume — it held four
times, failed once, and holds again here, each time for a reason.

`fiveProg` is the artifact: check a permission, allocate, read the mediated resource,
build a sanitised query, emit it, free the buffer. **Five certificates** — budget
(tight: certified 6, spends 6), mediation, noninterference, memory safety, structural
integrity — from one program.

Three things remain, all named in the module. Loops carry three of the five (the budget
cannot, per stage 1n; structural integrity has no loop rule yet). Path traversal is
expressible and not written. And stage 1e's ledger is not threaded through `xcheck`, so
a program's assumptions are still tracked by hand.

## The composable core (`PathCert.lean`) — stage 1q, path traversal

Stage 1o said this row was "the same shape with `/` and `..` in place of the
delimiter". That was half right, and the wrong half is what makes the stage worth
writing. Injection is about a **count**: how many delimiters reach the sink. Traversal
is about a **prefix condition**: a path escapes when some *prefix* pops above the root,
and no count can see that — `counting_cannot_decide_traversal` proves it, since `a/..`
and `../a` carry the same symbols and only one escapes.

So the two-symbol alphabet gets a second reading (`ord` = ordinary segment, `quote` =
the parent segment `..`) and a new property: `walk` runs the depth and fails on
underflow; `safePath` is "the walk survives". `spath` computes a *lower bound* on the
final depth, which is what makes variables usable at all.

**Path safety does not factor from taint.** To know a variable can only increase depth,
the analysis must know it contains no parent segments — exactly the count-zero fact
stage 1o's `TaintEnv` records. `path_needs_the_taint_environment` shows the dependency:
the same program is refused with an empty environment and accepted once the variable is
recorded as count-zero. That is the *second* dependency in the bundle, after stage 1j's
noninterference-needs-memory-safety — and unlike that one it is a clean layering rather
than an entanglement, so `PathCert` takes the environment as a parameter and no new
indexed judgment was needed. Two dependencies, two different remedies.

**The discipline is per-sink**, which is what stage 1p's destination-recording sink was
for. A query is not a path: `pcheck fs` constrains only the emits that go to `fs`, and
`query_sink_untouched_by_path_checker` records that it says nothing about the others.

The row is the same four theorems as injection: `path_escape_is_real` (the vulnerable
program emits a path that pops above its root, on a `../..` payload),
`path_escape_rejected`, `safe_path_checks`, and `safe_path_holds_under_every_input`.

## The composable core (`StringLoop.lean`) — stage 1r, loops for the string certificates

Stage 1n measured "three of four certificates compose over loops" *before* there were
string certificates. Stages 1o and 1q then added two more, both with
`| .loop _ _ => none`, which quietly made the honest figure three of six. This stage
closes that with exactly stage 1l's narrowing, and the figure becomes **five of six** —
`five_of_six_compose_over_loops` states it, with the budget still the only law that
cannot, for the reason stage 1n gave: a cost bound over a loop needs an *iteration*
bound, which no amount of narrowing supplies.

Two things made it cheaper than stage 1l. **The emission list needs no widening**: `Ks`
records *which* delimiter counts a program may emit — a set of possibilities, not a
running total — so a loop emitting the same query a thousand times draws from the same
`Ks`, and only the environment needs a fixed point. And **the two certificates share
the shape**: `TaintCert.loop` and `PathCert.loop` are the same fuel induction over the
same weakening lemmas, the fourth and fifth appearance of the
Hoare-triple-with-a-tracked-set pattern. That repetition is the evidence the shape was
right.

`loopQuery` and `loopServe` are the witnesses — a query server and a file server, each
emitting inside a loop. `loopQuery_needed_the_widening` shows stage 1o's checker could
not handle them, and `loopQuery_safe` / `loopServe_safe` give the guarantees over an
unbounded number of emissions.

The fuel index is stage 1l's answer to the same problem for the same reason: the
narrowing call sits under a closure, so structural recursion on the command cannot see
through it, and a well-founded definition would stop kernel-reducing and break every
`decide`.

## The composable core (`Deploy.lean`) — stage 1s, what must be true of the world

Five certificates say things about the *machine*. A deployment cares about something
else: that the database accepts the query, that the filesystem serves a file inside the
root, that the policy the program consulted is the policy the specification meant.
Stage 1e built the mechanism for exactly this — a ledger that appends under composition
and cannot be silently discharged — and it was never threaded through the rest of the
core. This threads it.

**The useful part is the sorting**, which the exercise forces and which was not obvious
in advance:

* **Noninterference** and **memory safety** need *nothing*. They are statements about
  the machine's own state, and the machine is the artifact.
* The **budget** needs nothing either, because it is denominated in the model's own
  steps. Converting it to seconds would need an assumption; "at most six steps" does
  not.
* **Mediation**, **structural integrity** and **path safety** each need exactly one
  entry — and the three entries belong to three *different* external components: the
  policy author, the query parser, the filesystem.

So the trusted base of a fully-certified program is **three lines long**, and
`Discharged` names them. `deployment_reading` is the transformation from machine
guarantees to deployment guarantees, and it needs no axioms at all. `toLedger` and
`sat_toLedger` connect the entries to stage 1e, so they append under composition like
any others.

Two theorems keep it from being a formality. `sink_assumption_is_load_bearing` exhibits
a deployment whose parser accepts nothing: `fiveProg` really does emit, so the
conclusion fails with the assumption, however well the program is certified. And
`machine_guarantees_need_no_deployment` records the other half — noninterference,
memory safety and the budget hold with the ledger *empty* — so the sorting above is a
fact rather than a presentation choice.

That last number is the point. A program can be certified to the hilt and still be
wrong about the world; what the ledger buys is that the ways it can be wrong are
listed, appendable, and impossible to discharge by accident.

## Attacking the core (`Attack.lean`) — stage 1t

Every finding from stage 1h onwards came from a counterexample that turned up while
building something else. That only finds defects which happen to block the next step, so
this stage looks on purpose.

**Twelve attacks, all refused**, each recorded as a theorem rather than asserted:
laundering a secret through concatenation and through sanitisation, branching and
looping on a secret, use-after-free through an alias, freeing through a second name, a
path built from a variable with an unknown parent-segment count, an escaping literal, an
access without its check, and a check of the wrong resource. `twelve_attacks_refused`
collects them so the list cannot quietly shrink. **No unsoundness was found in any
checker.**

**Three defects, all of the same kind** — a guarantee narrower than its name, which is
the failure mode this repo treats as most serious:

1. **The exported noninterference statement was vacuous for strings.**
   `xcheck_gives_five` states noninterference from `initU σ`, and `initU` gives every
   string variable the empty value — so two runs from it *cannot differ in a secret
   string*, and everything the statement said about the sink was true and empty. The
   underlying `jsecTy_sound` was general all along; only the wrapper was weak.
   `allcheck_NI_general` exports the general form and `secretTouching_NI_is_real` is a
   witness where the two runs genuinely differ in a secret string. This is stage 1o's
   unobserved-sink mistake made one level up.
2. **The heap is a fiction.** `heap_is_never_touched` proves `uexec` never reads or
   writes the `heap` field, so memory safety here means *liveness of addresses* and
   nothing about stored values. That is exactly what the no-fault theorems claim, but a
   `heap : Int → Int` field in `UState` implies more.
3. **The allocator never reuses an address** (`allocator_never_reuses`), and `SepInv`'s
   freshness conjunct is where the proof *uses* that. Real allocators reuse, which is how
   use-after-free becomes exploitable rather than merely wrong — so stage 1i's CWE-416
   result carries a hypothesis that had never been written down.

All three were in the **statements**, not the proofs. That is where to look next time.

## The allocator reuses (`Reuse.lean`) — stage 1u

Stage 1t found that `uexec`'s allocator only advanced a counter, so a freed address was
never handed out again — and that stage 1i's use-after-free result silently depended on
it. Real allocators reuse. This one now does: `free` returns the address to a free list,
`alloc` takes from the free list before touching the counter.

**The separation argument survived**, which I had predicted it would not. It needed two
more conjuncts in `SepInv`: every freed address is *not live*, and every freed address
is below the counter. With those, `alloc` still hands out an address distinct from every
tracked one — from the free list by disjointness, from the counter by freshness. The old
proof used only the second route, so this is a genuine case split rather than a
re-derivation. `stale_pointer_refused_after_reuse` shows the ABA hazard is handled:
after `alloc p; free p; alloc q` both variables hold **the same address**, `q` is usable
and `p` is refused — the stale pointer is rejected even though its address is live
again, which is precisely what makes reuse dangerous in practice.

**Reuse opened a channel.** The free list decides the next address, so freeing a *High*
pointer makes the two runs' allocators diverge and the next allocation into a Low
variable publishes the difference. `freeing_a_secret_pointer_leaks` is the witness: two
Low-equal, memory-safe states whose secret pointers hold 5 and 7; after one `free` and
one `alloc`, a public variable holds 5 in one run and 7 in the other. Nothing faults —
it is a well-behaved program leaking through the allocator.

So `JSecTy.free` gained a hypothesis it never needed before, `P x = false`, and all
three checkers gained the test. Under the non-reusing allocator that rule was
unnecessary, which is why it was absent: **the model had been too kind to require it.**
One worked program had to change — `safeHeapProg` now allocates through a public
variable rather than a secret one, because freeing a secret pointer is now genuinely
unsafe rather than merely unmodelled.

The exchange rate is worth stating: removing a *limitation* cost one new typing
restriction and two invariant conjuncts. Nothing that had been proved became false.

## The heap holds values (`HeapValue.lean`) — stage 1v

Stage 1t found the `heap` field was never read or written, so memory safety meant the
liveness of addresses and nothing about stored values. This gives the heap real
operations: `load d p` is `d := *p`, `store p v` is `*p := v`, both faulting if the
pointer is not live. `the_heap_is_live` closes the finding — allocate, write 42, read it
back, and 42 comes back.

**The two properties reacted very differently to the same change**, which is the point
of the stage. Memory safety extended *for free*: the separation invariant never
mentioned heap contents, so `SepCert.load` and `SepCert.store` need the pointer tracked
and nothing else (`memory_safety_extended_for_free`). Noninterference did not: once a
value can travel from the heap into the store, the heap is part of what an adversary
sees. `uLowEqA` gained `s.heap = s'.heap`, and three rules appeared where there had been
none — `loadL` (through a Low pointer the value is Low), `loadH` (through a High pointer
the address is unpredictable, so the destination must be High), and `storeL` (both
operands Low).

**The absence of a `storeH` rule is the finding.** Making the whole heap Low-observable
is the simplest sound choice, and its consequence is that the heap is a **public
resource**: `storing_a_secret_is_refused` shows a secret value cannot be written to it
at any address. That is more restrictive than a real system needs. Lifting it requires
a *label per address* — a heap of labelled cells, with the label read at the `load` and
checked at the `store` — which changes the state and the observation rather than adding
a rule, so it is named here rather than attempted.

`wild_store_faults` and `wild_store_rejected` confirm the new operations really can go
wrong and that the analysis stops them, the same pairing stages 1h and 1i used.

## Per-address heap labels (`HeapLabel.lean`) — stage 1w, the invariant

Stage 1v made the heap real and, to stay sound, made it entirely **public**. Lifting
that needs a label per address — and the payoff rules can only be *syntactic* if the
analysis can read a cell's level off the program text. This stage establishes exactly
that, and nothing more: it is the invariant half of a two-stage change.

* `UState` gains `hlab : Int → Bool`, fixed at allocation; `MemOp` gains `allocS`, so
  the allocation **site** declares the cell's level.
* **Allocation zeroes its cell**, and this is not tidiness. With reuse (stage 1u) a
  freed *secret* cell handed back out as a *public* one would expose its old contents —
  a public address whose value differs between runs. `allocation_zeroes` is the witness:
  write 7, free, reallocate, read 0. It is an interaction between two stages that
  neither produced alone.
* `LabInv P V s` — every tracked pointer points at a cell of its own level — with
  `JSecTy.toLabInv` proving it inductive across all nineteen rules. **Separation (stage
  1i) is what makes it work**: no two tracked pointers can share a cell, so no cell has
  two levels. The allocation case is the only one that needs `SepInv`, which is 1i
  paying for 1w.
* `JSecTy.alloc` gains `P x = false` and `allocS` requires `P x = true`
  (`allocation_site_must_match_the_level`). That is a *consistency* condition, not a
  secrecy one — stage 1m removed a secrecy condition and nothing it proved became false;
  the rule was split, not restricted. The note on `alloc_rule_rests_on_low_guards` says
  so where the old claim lives.

**What this stage does not do**, stated because the field would otherwise look like it
earns more than it does: the observation still contains `s.heap = s'.heap`, so the heap
is still public and `storing_a_secret_is_refused` still holds —
`heap_still_public_at_this_stage` records it as a theorem. `LabInv` is proved and *not
yet used* by noninterference.

Stage 1x is the other half: replace the heap conjunct with "labels agree, and public
cells agree", and add the rules that spend the invariant — `storeH` (a secret through a
secret pointer is invisible) and a label-aware `loadL`. Splitting it this way means the
invariant is audited before anything depends on it, the order stages 1j and 1k used for
the analogous problem.

## Spending the invariant (`HeapSecret.lean`) — stage 1x

Stage 1v made the heap public; stage 1w built `LabInv` and deliberately did not use it.
This uses it, and it is short — which is the argument for having split them.

Two changes. **The observation is per address**: `uLowEqA`'s `s.heap = s'.heap` becomes
`s.hlab = s'.hlab ∧ (∀ a, s.hlab a = false → s.heap a = s'.heap a)`, so labels are
public, public cells are public, and secret cells are not observed. And **`storeH`**: a
secret may be stored through a secret pointer, because `LabInv` lets the analysis read
the cell's level off the pointer's — that is exactly what makes the rule syntactic.

`jsecTy_sound` gained the two `LabInv` hypotheses, with `JSecTy.toLabInv` supplying them
at every intermediate state; nothing else about the proof changed shape.

**What is new and what is not.** `secret_through_a_secret_pointer` and
`secret_round_trip_checks` are the new ground — a secret can now live in the heap.
`public_pointer_still_cannot_carry_a_secret` is the boundary that remains, and it is the
right one: a public pointer points at a public cell, so writing a secret there really
would leak. `secret_cell_cannot_be_read_into_a_public_variable` closes the other
direction. `the_heap_is_two_level` puts all four in one statement. Stage 1v's
`storing_a_secret_is_refused` survived *unchanged* — its pointer is public — but it is
now a boundary rather than a blanket ban, and its docstring says so.

The remaining restriction is a design point, not a gap: labels are fixed at allocation
and there is no relabelling operation (`no_relabelling_operation_exists`), so a cell
cannot change level and a secret cannot be released. Declassification is a policy
decision of the kind stage 1e's ledger exists to record, not another typing rule.

## Attacking the labelled heap (`HeapAttack.lean`) — stage 1y

Stage 1t's discipline applied to 1v–1x. Two questions: is the new guarantee vacuous the
way the string one was, and does anything reasonable get refused for a bad reason?

**Not vacuous.** Stage 1t found noninterference exported from `initU` said nothing about
strings, because `initU` makes both runs identical in that dimension. The heap could
have gone the same way. It does not: `secret_write_is_not_vacuous` runs a certified
program from two `initU` states differing only in a High variable and lands with
**different values in the secret cell** — 3 against 0 — while the runs stay Low-equal.

**But a real gap: a secret cell can never be freed.** Neither rule is wrong; two correct
rules compose into something too strong. Stage 1u: `free` needs a **Low** pointer,
because the free list decides the next address and is observed. Stage 1w: a secret cell
is reached through a **High** pointer, because the label must match the pointer's level.
The two are each right and jointly unsatisfiable, so secret memory leaks by
construction. `memory_safety_would_allow_it` locates the gap precisely — `slcheck` frees
the secret pointer happily, and the refusal is entirely from the information-flow side —
and `public_cells_can_be_freed` shows the restriction is specific.
`both_rules_are_load_bearing` keeps the witnesses that neither rule can just be dropped.

The fix is identifiable and named rather than attempted: give secret allocation its own
counter and free list, neither observed, over a disjoint address range. Freeing a secret
pointer then perturbs only unobserved state, which is what stage 1u's argument needs.
It is not a patch — `SepInv`'s freshness conjunct becomes two conjuncts over two ranges,
and range disjointness joins the separation argument — so on the evidence of 1w and 1x
it is an invariant stage followed by a short rule stage.

## Retiring secret addresses (`HeapRetire.lean`) — stage 1z

Stage 1y found the gap: `free` needed a Low pointer (1u) and a secret cell is reached
through a High pointer (1w), so a secret cell could never be freed. It named a fix — a
separate unobserved counter and free list over a disjoint address range — and predicted
an invariant stage plus a rule stage. **That prediction was wrong, and following it
would have been expensive.**

A much smaller change does the whole job: when a *secret* cell is freed, put its address
nowhere. Retire it. Freeing through a secret pointer then perturbs only `live`, which is
not observed, so `free` needs no level condition at all. `SepInv` did not change —
pushing fewer addresses onto the free list only makes its conjuncts easier — and no new
invariant appeared. One branch in `uexec`, one dropped hypothesis.

`secretLifecycle` is the result: allocate a secret cell, write the secret in, read it
back, release it. The last step was untypable before this stage.

**The price**, stated plainly: secret addresses are never reused.
`public_is_recycled_secret_is_retired` shows the difference — a public
allocate-free-allocate returns the same address, a secret lifecycle does not. That is
address-space consumption, not a safety property, and this model claims nothing about
exhaustion.

**What became of stage 1u's rule.** Its leak witness is still true — it is a statement
about two concrete states — but those states are now provably unreachable:
`ptrFive` aims a secret pointer at a cell labelled public, which is exactly what
`LabInv` forbids (`the_leaking_state_violates_the_label_invariant`). So three stages
were involved and **the middle one carried the load**, which was invisible when it was
written because 1w had no payoff of its own.

The estimate is worth recording: three memory-model predictions in a row have been
wrong — 1u cheaper, 1w dearer, 1z much cheaper. The pattern in the misses is usable
though: the expensive changes touched the **observation** or an **invariant**; the cheap
ones touched only the semantics.

## Two threads (`Interleave.lean`) — stage 2a

Brick 32 proved race freedom on its own small language and has never been brought onto
`UCmd`; that is the largest remaining distance between sixteen bricks and one core.
Following stage 1z's rule of thumb — changes touching the observation or an invariant
are the expensive ones — the first step here is to find the obstruction, not to build
the proof.

`uexecPar` interleaves two threads at **command** granularity: a schedule picks a
thread, and that thread's next command runs atomically. That is the granularity at
which a check and its use can be torn apart, which is what makes it worth modelling.

**Memory safety does not compose.** `interleaving_breaks_memory_safety` gives two
threads *each individually certified* — one allocates and dereferences, certified from
the empty tracked set; the other frees, certified given the pointer tracked — whose
sequential run is clean and whose interleaving faults. Neither certificate is wrong: the
tracked set is thread-local, and nothing makes one thread's set an obligation on the
other. And by stage 1j's dependency the failure propagates — noninterference for `deref`
*needs* the memory invariant, so the two properties cannot be rescued separately here.
That is 1j doing work at a distance.

**The budget composes.** `budget_composes_across_threads`: the interleaved and
sequential runs cost the same. The one law that refused to compose over *loops*
(stage 1n) composes over *threads* without a murmur, because cost is a property of the
trace and cares about neither state nor order.

**And the fix has a shape.** `disjoint_threads_are_safe` — two threads sharing no
variable are fine at either schedule. That is ownership in the separation-logic sense:
disjoint tracked sets, with freeing the owner's prerogative. On the evidence of 1j → 1k
that means a new indexed judgment rather than a side condition, and on the evidence of
1w → 1x an invariant stage before a rule stage.

One scoping note kept as a theorem: `addresses_depend_on_the_schedule`. The allocator
hands out different addresses under different schedules. The schedule is a *public*
input here, demonic as in brick 32, so this is not a leak — but it would become one the
moment a schedule could depend on a secret, which is an assumption a scheduler model
would have to state.

This stage claims a machine, one obstruction and one positive. It does **not** claim a
race-freedom certificate on `UCmd`; brick 32's results stay where they are.

## The counted loop, natively (`CountedLoop.lean`) — stage 2j

Every fully-certified program in this repo is straight-line, and the record says why:
`only_the_budget_lacks_a_loop_rule`. Five of six laws compose over loops; a cost bound
needs an *iteration* bound; brick 34's `dos_unbounded` proves no uniform one exists in
general. So `allcheck` returns `none` at every `.loop`.

Stage 1f found one way past it. `UCert.ofEmbedded` budgets a loop whose body is a **pure
store program embedded wholesale** from the `While` development — which is why
`handlerBounded`'s loop body is `.skip`. An embedded `WCmd` has no heap, no strings, no
`check` and no `access`, so the certified loop cannot touch memory, cannot be mediated,
and cannot emit. The budget was available; the loop was not worth writing.

**The native rule.** `forU i k body` initialises a counter from a constant and counts
down, with `body` an arbitrary `UCmd`. `countU_cost` bounds the loop by `1 + v·(b+2)` in
the counter's *value*; `UCert.forU` reads `v = k` off the initialiser and turns it into
the uniform budget `2 + k·(b+2)`; `JSecTy.forU` supplies the flow and memory halves. The
counter must be Low, so a loop whose *length* is secret is refused — stage 1b's timing
channel, at the iteration level.

**The case stage 1f's proof does not have.** A `WCmd` body cannot die; a `UCmd` body can.
If the machine dies inside the loop, the decrement is a no-op, the guard never falls, and
the loop runs forever (`a_dead_counted_loop_does_not_halt`, which is stage 1f's own
`uexec_dead_loop_diverges` applied where it bites). The budget is therefore never
violated — there is no halting run to violate it — and that is precisely what makes
`countU_cost` provable. It is recorded as a defect of the *language*: a failed
authorization check inside a loop should abort, not hang. The fix is a `dead`
short-circuit in `uexec`'s loop rule, a semantics change every module below depends on,
and it is named here rather than guessed at.

**One checker.** `bcheck` is `allcheck` plus one clause; everything that is not a `seq` or
an `ite` goes straight to `allcheck`, so every earlier result applies verbatim, and
`asFor` reads the counted-loop idiom off raw syntax. The loop body is checked by
`allcheck`, so it may not itself contain a loop — nesting is a follow-on, not a claim.

**The artifact.** `loopHandler` carries **all five certificates while iterating**: budget
40 over every input and every fuel, a mediated read *inside* the loop, noninterference,
memory safety with a scratch cell allocated and freed on every turn, and a sanitized query
emitted per turn with its delimiter count fixed. `allcheck_refuses_loopHandler` is the
contrast — the previous checker returns `none` on it. Stage 2i's trace theorem covers it
as well (`loopHandler_trace_is_low`), retiring 2i's note that its loop-free restriction
was "the budget's, not the trace's".

The boundary is unmoved. `unbounded_countdown_still_refused` keeps the DoS loop out, and
`only_the_budget_lacks_a_loop_rule` stays true as written: there is still no rule for a
general `.loop`, and brick 34 proves there cannot be. Standard three axioms, no `sorry`.

## The fused induction, and the trace theorem (`SpecFused.lean`) — stage 2i

Stage 2d ended with a conjecture: *for every program `xcheck` accepts, the speculative
address trace is a function of the Low part of the initial state, under every window.*
Stage 2f attacked it, found it **false** in the model as it then stood, and repaired the
model. Stage 2g showed the obvious way to prove the repaired version cannot work. This
stage proves it.

**The fused induction.** `jcheck_ptrLow` lifts stage 2f's `PtrLow` from one atomic command
to whole certified programs — `seq`, `ite` and `loop` — carrying `SepInv`, `LabInv` and
`uLowEqA` through every case. The hypothesis list *is* the result: stage 2g's
`traceEq_is_not_inductive` proved a relation omitting the two memory-safety invariants
breaks at its first step, so nothing lighter than this would do. `FusedInv` bundles the
six, `FusedInv.step` moves them as one, and the four preservation theorems it composes
come from four different stages (1i's `toSepCert`, 1w's `toLabInv`, 1x's `jsecTy_sound`,
and `jcheck_ptrLow` itself).

Worth saying precisely, because stage 2g named a *place*: the fusion is at the level of
the invariant, not of the proof text. `jcheck_ptrLow` is a second induction over the same
rules that *calls* `jsecTy_sound` at each step rather than an edit to it — `PtrLow` and
`touched` are defined six modules downstream of `HeapJoint.lean`, and moving them up the
import graph to fuse literally would buy nothing. What stage 2g's obstruction forbids is
proving the conclusion from a *weaker frame*, and this frame is the full one. That
layering over the invariant bundle works while layering over `TraceEq` does not is itself
the sharpest statement of where the boundary lies.

**The transient window is where it is earned.** `transRun_agrees` is the case the
architectural argument does not cover and the one the whole stage is about: a mispredicted
window is a certified run whose *state* is thrown away and whose trace is not, so
`touched_agrees` fixes what each command contributes and `FusedInv.step` carries the
invariant to the next. `jcheckList`/`jcheck_flatten` supply the small missing fact that a
certified command flattens to a certified list.

**The theorem.** `jcheck_strace`: two runs of a certified program from states satisfying
the fused invariant produce the same speculative trace, at **every window and every fuel**.
`allcheck_jcheck` — `allcheck` is `jcheck` rule for rule on the pointer component — turns
that into `certified_trace_is_low`, stage 2d's conjecture in its own words.

**No new rule was needed.** Brick 33 closed this on its own language with a `fence`. On
`UCmd` the rules that exclude the gadget are stage 1i's linearity discipline (a loaded
value leaves the tracked set, so it can never become an address) and the flow certificate
(no branch on a secret) — both written long before speculation was in view. Stage 2d
recorded that as "two exclusions and a failure to find, which is not a theorem"; this is
the theorem. `the_hypothesis_is_load_bearing` keeps the converse on record: `victimU`
leaks its secret through the trace, and `xcheck` refuses it.

**Applied, not just stated.** `bigHandler_trace_is_low` puts stage 2h's twenty-one
operation handler under the theorem, and `bigHandler_trace_is_not_empty` shows the trace it
equates has six addresses in it. Stage 2h could not exhibit a program whose *transient*
window lengthens the trace — `bigHandler`'s untaken branch happens to touch no memory — so
`brWitness` supplies one: a certified program tracing `[1]` at window 0 and `[0, 1]` at
window 1, whose trace agrees between two stores differing in a secret anyway.

Limits, unchanged from stage 2d and restated in the module: addresses only, so no cache
lines, eviction, timing or contention; one global window; loop guards always predicted
correctly; nested speculation excluded by `flatten`. `allcheck` has no loop rule, so
"every program `xcheck` accepts" means every loop-free one — but `jcheck_strace` and
`jcheck_ptrLow` both handle `loop`, so that restriction belongs to the budget, not to the
trace. And **the cost stays broken**: `transient_work_is_off_the_budget` is untouched by
any of this. The trace is now proved secret-independent; the *number* of transient
commands is still off the certificate.

Standard three axioms, no `sorry`; `allcheck_jcheck`, the two checker runs and the two
trace measurements use only `propext`.

## A program worth the name (`BigHandler.lean`) — stage 2h

Every worked example here has been small enough to read in one line. `fiveProg` is six
operations, built to exercise one rule per certificate. Six is enough to show the
certificates *compose*; it is not enough to show they compose at a size anyone would call
a program — and four of the last five stages have been obstructions rather than artifacts.

`bigHandler` is twenty-one operations: two authorization checks, two mediated reads, three
allocations (one secret), pointer stores and loads, arithmetic, a sanitized query built
and emitted, a branch, two dereferences, three frees. It carries **all five certificates
from one run of one checker** at budget 24, and everything below is measured rather than
asserted.

- **The trusted base is still two entries.** Twenty-one operations, and stage 2c's `needs`
  charges the policy author and the `db` parser and nothing else — no filesystem, because
  the program never emits there. The base grew with what the program *does*, not with how
  long it is, which is the point of computing it rather than fixing it.
- **The secret address is retired, not recycled.** Three allocations, three frees, and
  `freed` comes back `[0, 1]` — address 2, the `allocS` cell, has left circulation. Stage
  1z's rule, introduced to close a two-line leak, as a fact about a real run.
- **The budget is tight.** 24 certified, 24 spent.
- **Stage 2e's speculation bound does real work, and is loose by a factor of three.**
  `bigHandler` branches, so unlike `fiveProg` it is not inert: at window 2 it really runs
  26 commands against a certified 24, and the bound allows 72. That gap is what "charges
  a full window to every command rather than to every branch" costs on something concrete.
- **Its trace does not grow under misprediction** — but only because the untaken branch
  happens to touch no memory. Recorded as a measurement, explicitly *not* a theorem;
  stage 2g is the reason no theorem is available.

No new rule, no new obstruction, no new defect: everything held at three and a half times
the previous example's size. After four consecutive obstruction stages that is worth
writing down.

Two limits. The program is loop-free, because `allcheck` has no loop rule — twenty-one
operations means twenty-one operations, not a bounded iteration over them. And `decide`
does the work throughout, so every measurement is a kernel computation on a closed term:
the strongest evidence available, and also why this stage says nothing about programs it
did not run.

## The trace does not factor either (`SpecFactor.lean`) — stage 2g

Stage 2f produced the two halves of a step case. The obvious next move is to lift them
to whole programs by induction, layered on top of the noninterference proof the repo
already has. **That does not work**, and this stage says why as a theorem rather than as
a difficulty.

Write down the relation a trace argument visibly needs: low-equal stores (branch guards),
equal `dead`, equal `fresh` and `freed` (the allocator), agreeing public cells, and
`PtrLow` (the addresses). Call it `TraceEq`. It omits `SepInv` and `LabInv`, because
nothing in the *statement* of trace agreement mentions separation or heap labels.

`traceEq_is_not_inductive` shows one certified command breaks it. The witness is a `load`
through a **Low** pointer: `jcheck` accepts `load d p` when `p` is tracked and
`!P p || P d`, so a Low pointer may load into a Low variable — and if the *cell* it
points at is secret, the two runs disagree afterwards in a Low variable.
`labInv_is_the_missing_hypothesis` names the exclusion: `LabInv P V s` says
`s.hlab (s.store x) = P x`, so a Low tracked pointer never points at a secret cell, and
the witness violates exactly that. `publicCell_labInv` confirms the invariant is not
vacuous.

So the trace conclusion has to be **fused into** `jsecTy_sound` — which already threads
`SepInv`, `LabInv` and `uLowEqA` through every rule — with `PtrLow` added as a fifth
hypothesis and `touched` agreement as a second conclusion. That is a statement about
*where* the next proof goes, worth having before writing four hundred lines in the wrong
place. `traced_step_agrees` assembles 2f's halves into precisely that step case, already
proved; it is the frame around it that has to change.

**This is stage 1j one level up.** 1j showed noninterference and memory safety do not
factor, because the `deref` rule needs the memory invariant. The entanglement now reaches
the trace: the addresses a program touches cannot be shown Low without the heap-label
invariant, which is a memory-safety artefact. Three properties, one induction — and the
core has now hit that wall from three directions, which makes it a design fact rather
than an observation about three proofs.

Two honest notes kept in the module. `TraceEq` failing does not mean *no* lighter
relation works, only that the obvious one does not and for a structural reason. And the
transient window is untouched by any of this — `transRun` will inherit whatever the fused
induction proves, but that inheritance is a lemma nobody has written.

## Attacking the trace conjecture (`SpecTrace.lean`) — stage 2f

Stage 2e left one question: is a certified program's speculative trace a function of the
Low part of its input? Attacking it did two things, and the first is a correction.

**The conjecture was false, and speculation had nothing to do with it.** `deadS` — fail a
mediation `check`, then allocate a secret pointer and dereference it — **passes
`xcheck`**, all five certificates, and its trace at window **zero** was `[11]` against
`[77]` for two low-equivalent stores.

The defect was in stage 2d's trace, not in the certificates. A failed `check` sets
`dead`; `uexec` then makes every command a no-op, so `allocS` never runs and `secret`
keeps its *initial* value; and `touched` recorded an address anyway. A command that does
not execute does not issue a memory operation. `touched` is now conditioned on `dead` —
the same shape stage 1q needed for `TaintInv`, for the same reason — and `touchedRaw` is
kept so the retracted definition can still be pointed at rather than quietly
disappearing. `halted_machine_leaks_in_the_raw_model` and `the_fix_closes_it` are the two
halves on record. Everything 2d and 2e proved survives unchanged, because none of their
witness states is ever halted; that is luck, which is why the witness is worth keeping.

**The invariant the repaired conjecture needs.** Every traced address is `s.store x` for
a tracked pointer `x`, so what is needed is `PtrLow V s s'`: every tracked pointer holds
the same address in both runs.

It is **not** implied by `uLowEqA`, and `ptrLow_is_not_implied_by_uLowEqA` proves it.
`allcheck`'s `allocS` rule *requires* `P x = true` — a secret-*named* variable is a
legitimate tracked pointer (`allocS_wants_a_secret_name`) — and low-equivalence says
nothing about its contents. The invariant holds anyway, for a different reason: the
allocator is driven by `fresh` and `freed`, which `uLowEqA` does synchronise. That is
exactly the kind of fact that has to be carried rather than derived.

`ptrLow_step` proves it inductive over every atomic command, including both allocators
and both faulting paths, and `touched_agrees` cashes it: two runs satisfying the
invariant touch the same addresses. Those are the two halves of stage 2g's step case;
what remains is the whole-program induction and the transient window.

## What speculation costs (`SpecBudget.lean`) — stage 2e

Stage 2d left one genuine unsoundness — the certified budget ignores transient work —
and one positive so narrow it barely counted. Both are closed here, and the second turns
out to have been the wrong statement of a much stronger one.

**Rollback is complete.** `rollback_is_complete`: for **every** program and **every**
window, the architectural state after speculation is the state `uexec` reaches. Stage 2d
proved this only for branch-free programs, as a by-product of proving something stronger
about them. Generalising 2d's faithfulness lemma from `w = 0` to every `w` costs nothing
— the transient parts live in the two components that lemma projects away — and makes it
a corollary, and universal.

**So four of the five certificates are immune.** `four_of_five_are_immune` and
`ni_transfers_to_speculation`: mediation, memory safety, structural integrity and
noninterference are all predicates on the final `UState`, and a machine reaching the same
final state satisfies them identically. No rule changes, no side condition, no fence.
They were never at risk, and the one-line reason is that transient state is discarded by
construction.

That leaves the surface exactly two things wide: the cost and the trace.

**The cost, bounded.** `spec_cost_bound`: in any run, `realCost ≤ archCost * (1 + w)`.
The budget is not lost to speculation, it is *scaled*, and the multiplier is the
misprediction window. Stated within a single run, so it needs no two-run comparison.
Composed with a certificate, `certified_cost_under_speculation` says a program checked at
bound `k` really runs at most `k * (1 + w)` commands, transient work included —
`fiveProg_costs_six_even_speculating` for the worked program, which being branch-free
pays nothing. `the_bound_is_not_vacuous` exhibits a certified program whose real cost
genuinely exceeds its certified one, so the scaling is doing work rather than restating
the budget.

Two looseness notes, stated rather than implied. The bound charges a full window to every
*command* rather than to every *branch*, so `k * (1 + w)` sits far above the true
`k + w * (branches taken)`; tightening it needs a branch count in the judgment. And the
**trace** question is untouched — it is stage 2d's conjecture, and separating the stages
is what makes clear which one moved.

## Speculation on the unified machine (`SpecUnified.lean`) — stage 2d

Brick 33 put Spectre in the semantics and closed row 9, but on its own small language.
The five-certificate core lives on `UCmd`. This stage brings the machine across and asks
what the certificates survive. **The answer was not the one the stage set out to write
down.**

`uexecS` is `uexec` with an **address trace** and **misprediction**: at an `ite` the
untaken branch also runs, for a window of `w` commands, with its state discarded and its
trace kept. `spec_is_uexec_extended` proves the extension faithful: the state and the
*architectural* cost are `uexec`'s at **every** window, so nothing here is an artifact of
a substituted machine. (It began as the `w = 0` statement; generalising it cost nothing,
since the transient parts live in the two components the projection drops, and stage 2e
runs on the general form.)
And the model is not vacuous: `victimU_leaks` gives the textbook gadget with two heaps
differing in one cell producing two different traces.

**But the core already rejects it.** `slcheck`'s load rule is `load d p => if memStr p V
then some (dropStr d V) else none`: the source must be tracked and the destination is
*dropped*, so a loaded value can never afterwards be dereferenced and the gadget has no
derivation (`gadget_rejected_by_memory_safety`). And a branch on a secret is refused by
the joint checker, so which branch mispredicts cannot depend on a secret either
(`secret_guard_rejected`) — memory safety alone would have allowed that one; the flow
certificate is what refuses. Both rules were written for other reasons, stages earlier.
There is also no pointer arithmetic, so the bounds-check-bypass half of Spectre-v1 has
no analogue at all (`no_pointer_arithmetic_here`) — an absence in the model, recorded so
it does not read as a result.

**What is not closed.** Two exclusions and an absence are not a theorem. The five
certificates are statements about `UState`; the trace is not in `UState`; so nothing
proves a certified program's trace is secret-independent. A search for a third route did
not find one, and that is a failure to find, recorded as such. The conjecture is written
into the module so it can be attacked: *for every program `xcheck` accepts, the
speculative trace is a function of the Low part of the initial state, under every
window.*

**What is genuinely broken: the budget.** `transient_work_is_off_the_budget`, on a
program the core does certify. The bound is 2, the machine reports 2 at every window,
and at window 1 a third command really ran. Stage 1n found the budget was the law that
would not compose over *loops*; stage 2a found it was the one law that *did* compose
over *threads*. It fails here in a third and different way — not wrong about what it
counts, but counting the wrong thing.

**The positive.** `branch_free_is_inert`: with no `ite`, the machine is independent of
`w` — trace and real cost included — so speculation changes nothing at all. That covers
the worked program (`fiveProg_is_speculatively_inert`). Stage 2e supersedes the
*architectural* half of this for every program; what stays special about branch-free ones
is that their trace and real cost agree too.

Scoping, stated rather than implied: one global window at every branch instead of brick
33's per-branch schedule (a *stronger* attacker, so nothing here is weakened, and brick
33 keeps the finer model); loop guards always predicted correctly; the
microarchitectural state is an address trace, so no cache lines, eviction, timing or
contention; conditional-branch misprediction only. No fence rule is proved on `UCmd` —
that is the named follow-on, not a claim.

## The trusted base, computed (`Assumptions.lean`) — stage 2c

Stage 1s said the trusted base of a fully-certified program is three lines: the policy
author, the query parser, the filesystem. That was a statement about the *language*, and
it was stated as a fixed `Discharged` record demanding all three of every program. Three
stages flagged the missing connection to stage 1e's ledger without making it.

The gap was not plumbing. A fixed three-entry record **overcharges**: a program that
never calls `access` reads nothing, so "the deployed policy is the intended one" is not
an assumption it needs, it is a statement about nothing.

So the ledger is computed. `needs c` collects, from the syntax, exactly the obligations
the program can incur, and `needsLedger` turns them into a stage-1e `Ledger` that
composes like any other. Two lemmas prove the omitted entries are omitted for cause:

- **`no_access_no_reads`** — a program without `access` leaves `reads` untouched, so the
  mediation guarantee holds with the policy entry absent;
- **`unwritten_sink_untouched`** — a program that never emits to `q` adds nothing tagged
  `q`, so that sink's entry is unnecessary too.

Both are proved by fuel induction over every command, `free` and `deref` included, not
by inspection.

**What it buys.** `pureProg_deployed_with_nothing` gives all three deployment-level
guarantees for a pure computation with the ledger **empty** — no policy author, no
parser, no filesystem trusted. Stage 1s could not state that: `deployment_reading`
demanded a `Discharged` record, and a `Discharged` record is three assumptions whether
the program uses them or not. And `fiveProg_deployed_with_two` proves the identical
three conclusions stage 1s's `fiveProg_deployed` proves, from **two** entries instead of
three — the filesystem conclusion holding vacuously, because `fiveProg` never emits to
`fs`. `discharged_covers_needs` confirms the old hypothesis always implies the new one,
so nothing that held before stops holding.

**The limit, as a theorem.** `needs` is syntactic and therefore conservative:
`needs_is_syntactic` shows an `access` in dead code is still charged. Nothing here
attempts reachability — over-charging the trusted base is the safe direction, and a
reachability analysis is a different and worse trade. The negative tests
`an_fs_writer_is_charged` and `access_really_reads` confirm the exemptions are earned by
the syntax rather than built into `needs`.

## Ownership (`Ownership.lean`) — stage 2b

Stage 2a's counterexample was about *runs*, which leaves open where the reasoning
actually fails. This pins it at the invariant, which is where a fix has to act.

**`SepInv` is not conjunctive.** `separation_is_not_conjunctive` gives one state
satisfying `SepInv ["p"]` and `SepInv ["q"]` and *not* `SepInv ["p","q"]` — the two
pointers alias. Two thread-local certificates therefore say nothing about the pair, and
that is exactly where 2a's faulting interleaving comes from. It is the same shape as
stage 1i's `memInv_not_preserved_by_free`: a counterexample at the level of the
invariant, showing the missing rule was an obstruction rather than an omission.

So the object a concurrent judgment must maintain is `SepInv (V₁ ++ V₂)`, over the
**union**. `union_gives_both` shows the union delivers both thread-local invariants, and
`ownership_is_the_missing_hypothesis` shows what it adds: cross-thread address
disjointness.

**The frame rule decomposes into three kinds of case**, which is worth knowing before
writing it: most commands frame for a dull reason (they change neither `live` nor the
store outside their own targets); `alloc` frames for an *interesting* reason — the new
address must differ from the other thread's pointers, which is the freshness conjunct
working across a thread boundary, already proved as
`alloc_frames_over_a_disjoint_set`; and `free` **cannot** frame, because it removes an
address another thread may hold. `free_frames_when_owned` states the rule an ownership
discipline would license, and its hypothesis is exactly what the discipline must
enforce.

The next stage is a judgment indexed by an ownership split with the frame rule as its
central lemma. Both precedents for that shape — 1j → 1k and 1w → 1x — were about a
dependency between two *properties*; this one is between two *threads*, and the
recurrence of the shape is itself worth noting.

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
