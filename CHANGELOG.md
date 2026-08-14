# Changelog — certified composition

Top-level arc across the three sub-projects. Each subdir keeps its own detailed
`CHANGELOG.md`; this traces the line of work as a whole. Dates are when the work
landed.

## Repository verification

- **CI, and a single entry point** (`tools/ci.sh`, `.github/workflows/ci.yml`). Until now
  every check — 78 Lean modules across three packages, `check-claims`, `guard-selftest`,
  `walk-check` — was run by hand at the end of a working session. A repo whose identity is
  "machine-checked and guarded against drift" had nothing enforcing that on push.

  The workflow calls `tools/ci.sh` and **nothing else**, so what gates a push is exactly
  what a session runs; `check-claims` now enforces both halves of that — the workflow must
  invoke the script, and the script must gate on every package, on `sorry`, and on all
  three tools. `guard-selftest` gains two cases covering that guard and is now 14/14.

- **Measurements assert their own preconditions** (`tools/walk-check.py`). Four
  corrections in six notes sections (§60, §62, §65, §66) were failures in measurements or
  their reading; none was in a proof. They were recorded as prose advice, which did not
  prevent the next one.

  `require()` and `PreconditionError` make the §66 failure structurally impossible:
  `defect_census` refuses to run at a non-limit level, where `C_x = {x-1}` makes the
  defect vacuously empty and silently biases the census toward the empty class. The census
  is now a permanent measurement, so §66's corrected table regenerates rather than sitting
  frozen in prose (`14:1 28:1 42:2 56:2 70:2 84:1`). A **canary** calls it at a successor
  and fails the run if no error is raised — the guard-selftest discipline applied to the
  measurement tool, and negative-tested: disabling the precondition makes `walk-check`
  report the canary failure.

## conf-typing — the confidentiality-typing framework (mathlib-free)

- **0.1 – 0.3** — mechanized the IMP timing instance: instrumented semantics +
  determinism; parametric `J` with admissibility (A1–A3) and separability;
  the `P_leak` worked example; strata, the no-coercion discharge judgment, the
  J-invariant rejection; the conformance gate; Boolean soundness. Bounded the
  policy stratum (delimited release with a real proof obligation — closing the
  unbounded-permit hole) and made the gate transport *both* strata.
- **0.4 – 0.5** — joint generation and completeness (Thm. 2) via the factoring
  bridge (Prop. 1); separability-equivalence.
- **0.6 – 0.8** — the corrected §10: "separable ⟺ 2-safety" is **false**
  (`Rbad`); among admissible properties the only nondegenerate 2-safety one is
  noninterference; the k-safety hierarchy above 2-safety is kernel-determined
  (no genuinely k-ary admissible atoms).
- **0.9** — the Πₖ up-set characterization (`simA3_iff_respectsCoarsening`):
  admissible ⟺ closed upward under kernel coarsening, with the realizability /
  observation-cardinality condition pinned explicit.

- **Brick 33 — speculative execution, the last OUT-OF-MODEL row
  (`Speculate.lean`).** §0's recipe run a third time, after timing (brick 2) and
  scheduling (brick 32). A transient-execution machine: architectural state that
  rolls back, a microarchitectural **address trace** that does not, and a `brLt`
  branch that may be mispredicted, running its body transiently for a window from
  a **misprediction schedule** — a data parameter, so `∀ misprediction` ranges over
  unbounded windows. `spectre_trace_is_the_secret` (axiom-free) pins the gadget's
  traces at `[8,42]`/`[8,99]` for two memories differing only at the secret, so
  `spectre_leaks`; `leak_needs_window_two` shows the channel has real depth.
  `arch_indistinguishable` is the other half — architecturally the guard is false,
  nothing runs, the two memories are *identical* — and
  `speculative_model_misses_it` pairs them: §0's model gap in its sharpest form,
  the architectural semantics not merely coarse but **silent**. The fix is a
  `fence`, with the strong soundness `specCheck_sound`/`spec_inert`: on a checked
  program the speculative registers *and* trace equal the architectural ones under
  every schedule, so speculation is observationally inert and `arch_ni_transfers`
  carries any architectural noninterference over verbatim — which is what makes
  the row compose. Limits kept explicit: address-trace granularity only; v1 alone;
  perfect rollback; nested speculation excluded **by the syntax** (branch bodies
  are a separate instruction type) rather than dropped by the semantics; and the
  check sufficient-not-necessary, witnessed by `benign_rejected` +
  `benign_transient_is_constant`. Note the class count stays **sixteen**: by the
  §2½ convention a verdict change is not a new class, which is the convention
  doing its job on its first use.

- **Brick 34 — resource exhaustion, the cost bound as a graded certificate
  (`CostBound.lean`).** Row 10's [classified] reduction, proved — and one clause
  of it corrected. `CostAtMost c k` quantifies over **all inputs and all fuel**,
  so algorithmic-complexity DoS is the failure of *uniformity*, not the absence
  of a bound. `costGA : GradedAction Nat Nat` (mul `+`, act `+`, le `≤`) is a
  checked instance of the interface's own accumulation algebra, and `cost_seq` /
  `cost_seq_is_mul` prove budgets add as `costGA.mul` — **the first time a
  security row lands directly in the transport calculus's algebra rather than
  beside it**. `costCheck`/`costCheck_sound` generate budgets for the loop-free
  fragment; `countdown_cost` bounds the canonical countdown by `1 + v·(kc+3)` in
  its counter's initial value, a bound that exists per input and grows with it —
  the DoS surface — and `spinU_cost_lb` turns that into **`dos_unbounded`**: no
  uniform budget exists for a loop counting down untrusted input. What it catches
  that nothing else does: the victim is memory-safe, injection-free and
  noninterferent, so every earlier brick certifies it. `budget_cost` restores
  uniformity from a constant-initialised counter. **Correction of record:** brick
  1's "`Bridge.ofModulus` territory" is wrong — a `Bridge` certifies a *binary*
  quantity and a cost budget is *unary*; the `GradedAction` transfers, the
  contraction does not. Limits kept: halting runs only (availability is
  liveness-shaped, still not claimed), the canonical countdown only (so the
  verdict keeps "REDUCIBLE in general"), instrumented steps not wall clock. Class
  count stays sixteen by the §2½ convention.

- **Brick 35 — complete mediation, and the split row 7 was hiding
  (`Mediation.lean`).** Row 7 carried the map's **last `[classified]` grade**, on
  the reasoning that π's correctness "is not a theorem anywhere". True of policy
  correctness — and it was swallowing a second, different property. CWE-285's
  actual defect, and CWE-306's, is almost never "the policy was wrong"; it is
  **missing mediation**: some path reaches the protected operation without the
  check. That is a program property, all-paths, decidable. `med_victim_bypasses`
  (axiom-free): the unguarded branch reads a resource the policy denies, while
  `victim_guarded_path_is_fine` shows the other branch aborts cleanly — the
  defect is the *route*, not the check. `medCheck` (flow-sensitive, intersecting
  at joins) with `medCheck_sound` generates the guarantee on every path and under
  every policy, via a three-part invariant.
  `policy_correctness_not_witnessed` proves the other half is **not**
  program-decidable — two policies, same checked program, both mediated,
  different reads — so `mediation_generated_policy_carried` states the split as
  one theorem and the CARRIED half is finally demonstrated rather than asserted.
  Limits: nesting excluded by the syntax; the join intersects, so the check is
  sufficient not necessary; no *subject* in the model, so IDOR (CWE-639) is a
  named follow-on. `memStr`/`interStr` defined and proved locally — the package
  is mathlib-free and guessing core lemma names had already cost two build
  rounds. **With this the map has no `[classified]`-only grade left**: every row
  is `[proved]`, `[argued]`, or an explicitly named deferral. Class count stays
  sixteen — a sub-formulation within a row is a verdict, not a class (§2½).

- **Composable core, stage 1b — one language, and the embedding
  (`Unified.lean`).** `UCmd` is `WCmd` plus `check`/`access`; the state gains
  `auth`, `reads` and `dead`. A refused check aborts and every later step becomes
  a no-op, so "nothing is read after a refusal" holds **definitionally** — checked
  in the model: after a refusal the later `access` reads nothing *and* the later
  assignment does not fire. The load-bearing theorem is **`uexec_embed_eq`**: on
  the image of `uembed`, started live, the unified machine's store, cost and
  branch trace are *exactly* `wexec`'s and the three new fields are untouched —
  one equation, so the While development is a **fragment** of this one rather
  than a parallel copy (brick 7's `wexec_embed_eq` standard, a level up). Two
  transfers follow: `ucost_of_cost` — a brick-34 budget is a budget here, no
  reproof — and `uembed_mediated` — a program with no `access` reads nothing, so
  the new dimension cannot be violated by code that predates it. The dimensions
  are live rather than decorative (`uVictim_not_mediated`, and the policy
  genuinely decides). **Not** done: the checkers are not retargeted, so no single
  program yet carries three certificates; that is stage 1c, and `VULN-COVERAGE`
  now says so explicitly so the map is not read as if the rows' conjunction were
  a theorem.

- **Composable core, stage 1c — one program, one check, two certificates
  (`Bundle.lean`).** The loop closes. `UCert A c A' k` bundles a **cost budget**
  (graded, accumulating by `costGA.mul`) with an **authorization triple**
  `{A} c {A'}` (Hoare-shaped, accumulating by threading) — two genuinely
  different composition laws, which is the point of bundling. `UCert.seq` shows
  the halves advancing independently, neither mentioning the other: that is
  `Bridge.pair_comp_cert`'s "no interaction term", concretely. `UCert.ite` joins
  by intersecting authorization sets and taking the worse budget. **`ucheck`** is
  one decidable analysis emitting both and **`ucheck_sound`** one soundness
  theorem. The artifact is `handler` — authorize, read, compute, conditionally log
  — passing by `decide` at `(["db"], 6)`, with `handler_bundle_end_to_end`
  reporting budget **and** complete mediation: **the first program in this repo
  holding two guarantees at once**. Three witnesses keep it concrete:
  `handler_budget_tight` (certified 6, spent 6 — not slack padding),
  `handler_partial_policy` (permit the database, refuse the log ⟹ reads `["db"]`
  then aborts, so mediation is per-resource not all-or-nothing), and
  `handler_without_check_rejected`. **Scope, stated in the module, both READMEs
  and `VULN-COVERAGE`:** two certificates, not three — noninterference is not
  retargeted, because lifting it needs a low-equivalence on `UState` and a
  decision about whether `reads`/`auth` are observable, a design question rather
  than a transcription — and the bundle is loop-free, as brick 34's `costCheck`
  already was. So the conjunction of all sixteen classes on one program is still
  not a theorem, and the map says so.

- **Composable core, stage 1d — the third certificate (`UnifiedNI.lean`).**
  Stage 1c stopped at two because noninterference needed a **design decision**:
  which parts of a `UState` can a Low adversary see? Recorded and load-bearing:
  the Low `store`; `reads` **observable** (which resources a request touches is
  visible — the same premise brick 33 used for cache lines and brick 29 for log
  records, so denying it would contradict the map); `dead` **observable** (a
  refused request is visible to whoever made it); `auth` **not** observable
  (internal bookkeeping, its outward effect already carried by `reads`). With
  that fixed, the result is slightly surprising: **`check` and `access` add no
  flow channel** — resource names are syntactic constants, so reads and death are
  determined by control flow and policy, both already Low-determined for a
  well-typed program. `WSecTy`'s whole discipline lifts unchanged
  (`usecTy_sound`, a fuel-and-two-run induction mirroring `wsecTy_sound`).
  **`handler_three_certificates`** is P1's deliverable: one program carrying a
  cost budget, complete mediation and termination-sensitive noninterference,
  composing by three different laws — budgets add, authorization sets thread, NI
  is conjunctive. `Psec_rejects_leaks` keeps it honest (the partition really has a
  secret; branching on it and laundering it through a Low variable are both
  rejected), and `secret_loop_still_rejected` confirms brick 7's termination
  channel stays closed. The price is recorded, not hidden:
  `access_is_static_by_design` — the NI result holds *because* there is no
  `access (e)`; store-dependent resource selection would make `reads` a genuine
  flow channel, and that is the IDOR follow-on named in brick 35. Still loop-free.

- **Composable core, stage 1e — a fourth component, and the scaling test
  (`BundleLedger.lean`).** Three certificates is suggestive; the design claim —
  `Bridge.pair_comp_cert`'s "no interaction term", so `n` guarantees cost `n`
  independent accumulations — is only tested by adding a fourth and seeing
  whether it slots in or forces rework. **It slots in: `UCertL.seq` is four
  lines.** The fourth is the **trusted base** — brick 4's ledger lifted to the
  bundle, accumulating by list append, a fourth genuinely different monoid after
  `+`, Hoare threading and conjunction (`four_laws_one_composition`). The payload
  is a debt the map carried in prose: brick 35 left *policy correctness* CARRIED
  because `policy_correctness_not_witnessed` shows no program can decide it, and
  the bundle's mediation certificate ("every read is π-permitted") is a
  **security** statement only if π is the intended policy. Now
  `handler_intended_reads` discharges the security reading *from* the ledger
  entry, and `handler_needs_the_policy_assumption` (axiom-free) shows the entry is
  load-bearing — with a permissive deployed policy and a restrictive
  specification, the same program, unchanged and still carrying all three
  certificates, reads something unintended. `row7_carried_is_a_ledger_entry`
  states both halves. **CARRIED is no longer a caveat in prose; it is an
  obligation with a type**, appending under composition and not silently
  dischargeable — the discipline the repo is named for, applied to its own bundle.

- **Composable core, stage 1f — bounded loops enter the bundle
  (`BundleLoop.lean`).** Every stage so far inherited brick 34's limit: `ucheck`
  returns `none` at a `loop`. Removing it needed one obstacle cleared first, and
  it is the interesting part — a bundle's budget must hold from **any** starting
  state, including an aborted one, or `UCert.seq` cannot compose, since the first
  component may abort and hand a dead state to the second. Three lemmas settle
  what an aborted run does, and are worth having anyway:
  **`uexec_dead_unchanged`** (from a dead state no command changes the state at
  all — the abort is *total*, not merely read-suppressing),
  **`uexec_dead_loop_diverges`** (a dead run inside a loop whose guard holds never
  returns: the store is frozen, so the guard cannot become false and the fuel runs
  out), and **`uexec_dead_cost`** (hence an aborted run's cost is statically
  bounded, loops contributing 1). With those, **`UCert.ofEmbedded`** admits any
  separately-certified While program — loops included — splitting on live (where
  `uexec_embed_eq` hands the While development over wholesale) versus dead.
  `handlerBounded` is the payoff, and `handlerBounded_numbers` is honest about the
  difference from stage 1c: certified 22, permitting run spends 19, so unlike the
  straight-line handler's *tight* bound this one over-approximates by 3 — the
  price of an analytic bound across a loop. The refused run costs 4 and shows the
  lemmas at work: the abort suppresses the counter's initialisation, so the guard
  is already false and the loop exits at once. Still outstanding: the counter must
  be constant-initialised and the body check-free, since a loop containing a
  `check` can go dead mid-iteration — covered only by divergence, not a bound.

- **Composable core, stage 1g — the coverage claim, corrected upward
  (`BundleCoverage.lean`).** Stages 1c–1f were described as carrying "three
  certificates", and `VULN-COVERAGE` was updated to match. That **under-counted**,
  and not as a matter of interpretation: the observation in `uOptLowEq` includes
  the cost and the halting bit, so one application of `usecTy_sound` discharges
  three map rows at once — the same economy bricks 3, 5 and 7 had on the While
  language, which is where the observation came from. The bundle covers **six**
  rows, each now projected out as a theorem rather than asserted:
  `bundle_covers_store` (row 1), `bundle_covers_timing` (row 2 — Low-equal runs
  cost *exactly the same*), `bundle_covers_termination` (row 13 — they halt
  together), `handler_mediated` (row 7), the budget (row 10), and
  `bundle_covers_seam` (row 12 — which is what `UCert.seq` *is*, so the row is
  carried by construction). `handler_covers_six_rows` states it for the worked
  handler; stage 1e's ledger additionally supplies row 11's *mechanism*. The other
  half is kept in the same file so the two cannot drift: `UCmd` has no strings and
  no heap, so rows 3, 6 and 14 are not expressible here, and rows 8, 9 and 11 are
  proved on their own machines. Left in prose deliberately — "the language has no
  strings" is a syntactic fact, and a first draft of it as a theorem came out
  vacuous (`Or.inr trivial`) and was deleted rather than kept as something that
  looks like evidence.

- **Composable core, stage 1h — the language grows a heap, and memory safety arrives
  as a separate certificate** (`ConfTyping/MemCert.lean`, plus a heap in
  `Unified.lean`). Stage 1g named the obstacle: the remaining rows need a bigger
  language. `UCmd` gains one constructor, `memop : MemOp → String → UCmd` (bundling
  `alloc`/`deref`/`free`, so each downstream match takes one new case rather than
  three), and `UState` gains `heap`, `live`, `fresh` and `err`. Pointers are ordinary
  `Int` values in the existing store, so the value domain did not change — which is
  why memory safety was reachable at this stage and injection was not.

  The point is *how* it was added: memory safety is **not** folded into `ucheck`. It
  gets its own analysis (`umcheck`) and its own certificate (`MemCert`, a Hoare triple
  on the variables known to hold a live pointer — threading under `seq`, intersecting
  at a branch, the same shape a third time). That is the honest test of stage 1a's
  extensibility claim, and it passed: `ucheck` gained one conservative line (`none` at
  a `memop`), `USecTy` gained none, and nothing in stages 1c–1g was reworked.
  `umcheck_no_fault` is the guarantee — a checked program never faults — with
  `wild_deref_rejected` **and** `wild_deref_faults` (the rejected program really does
  fault, so the check is not refusing something harmless), `alloc_then_deref_ok`, and
  `clobbered_pointer_rejected` (overwriting a pointer drops it from the tracked set).

  Both limits are theorems, not footnotes. `free_has_no_rule`: `free` is in the syntax
  and the semantics, so use-after-free is *expressible*, but dropping an address
  invalidates every alias and soundness needs brick 12's linearity or brick 19's
  must-alias tracking in the invariant — so this closes the wild-access half of row 6
  (CWE-119) and **not** the use-after-free half (CWE-416).
  `memops_not_yet_NI_typed`: `alloc` writes the fresh counter into the observable
  store, so heap ops are not noninterference-typed. Stage 1g's closing "what it does
  not cover" note said row 6 was inexpressible here; that sentence was updated rather
  than left to rot, which is the reason it lives next to the claim. The handler's
  count is unchanged at six — it contains no `memop`.

- **Composable core, stage 1i — `free`, and a proof that stage 1h could not have had
  it** (`ConfTyping/MemLinear.lean`). Two results, and the second is the one worth the
  module.

  *The rule.* `SepInv` adds two conjuncts to `MemInv`: tracked variables hold pairwise
  **distinct** addresses, and every live address is below the allocation counter. With
  those, `free` has a rule — freeing `x` drops one address from `live`, and every other
  tracked variable survives precisely because separation says its address is a
  different one — and `slcheck_no_fault` extends memory safety to programs that
  deallocate. That is row 6's use-after-free half, CWE-416. The freshness conjunct is
  what lets `alloc` re-establish separation: the new address is `s.fresh` and
  everything live is strictly below it, so the new pointer is provably new. Witnesses:
  `use_after_free_rejected` with `use_after_free_faults` (the rejected program really
  does fault), `double_free_rejected_by_slcheck`, `alloc_free_ok`, and
  `free_one_keep_other` — freeing one of two pointers leaves the other usable, so the
  rule is not conservative to the point of uselessness.

  *Why 1h could not.* `memInv_not_preserved_by_free` exhibits a concrete state
  satisfying stage 1h's `MemInv ["p","q"]` in which one `free "p"` step lands in a
  state violating `MemInv ["q"]` — `q`'s address deallocated underneath it. So the
  missing rule was not laziness or an unfinished proof: the weaker invariant is not
  inductive for `free`, and no work on `MemCert` could have added the rule.
  `aliasState_violates_SepInv` confirms the strengthening is aimed at that state and
  not at something incidental. A limit that stage 1h recorded as a theorem is now
  *explained* by a theorem.

  Nothing regressed: `slcheck_extends_umcheck` proves everything `umcheck` accepted,
  `slcheck` accepts with the same tracked set, and `SepInv.toMemInv` lets a stage-1h
  consumer keep the weaker invariant. `free_has_no_rule` stays true as written — it is
  a statement about `umcheck` — with a forward pointer added so it is not read as the
  repo's last word.

  One honest note, kept in the module rather than a README. The separation conjunct is
  load-bearing in the proof and *unreachable* in the language: `assign` always drops
  its target, so this `UCmd` cannot construct two tracked aliases. Soundness quantifies
  over every state satisfying the invariant, not only reachable ones, and the witness
  above is exactly such an unreachable-but-admissible state. Restricting to reachable
  states would trade a two-line conjunct for a global reachability argument, and would
  break the moment the language gained a pointer-copying assignment.

  Stage 1g's "what it does not cover" note has now been rewritten by two later stages,
  which is the argument for keeping it next to the claim. The handler's count is still
  six: what the *machine* can certify is not what the *worked program* does certify.

- **Composable core, stage 1j — noninterference meets the heap, and the first pair of
  certificates that does not factor** (`ConfTyping/HeapNI.lean`, plus `USecTy.allocH`
  in `UnifiedNI.lean`). Three findings.

  *High allocation is free, and stage 1h's reason was wrong.* Stage 1h said heap ops
  are not NI-typed because `alloc` writes the fresh counter into the observable store.
  That holds only for a *Low* target. `fresh` and `live` are not in the observation at
  all, so allocating into a **High** variable is invisible: `USecTy.allocH` is sound
  with no change to `uLowEq`. `memops_not_yet_NI_typed` accordingly narrows to `deref`
  and `free`, and `high_alloc_is_NI_typed` records the new positive.
  `heapProg_two_certificates` is the first heap program carrying noninterference and
  memory safety at once.

  *Low allocation is the open design question.* `allocL_would_be_unsound` exhibits two
  Low-equal states at different points of the allocation sequence; allocating into a
  Low variable publishes the difference. Typing it needs `fresh` in the observation —
  a decision about what the adversary can see, left open deliberately.

  *`deref` and `free` can never have an unconditional rule.* They can **fault**, a
  fault sets `dead`, and `dead` is observable: `deref_leaks_through_dead` separates a
  Low-equal pair with one `deref` on a High variable. No syntactic judgment fixes this,
  because faulting is a property of the state. What they do have is
  `deref_NI_given_safety` / `free_NI_given_safety` — noninterference on states
  satisfying the memory invariant, the hypothesis being literally the other
  certificate. `the_leaking_state_is_the_unsafe_one` confirms the leaking state is
  exactly the one failing `MemInv`.

  **The finding.** `ni_and_memory_do_not_factor` puts both halves in one statement.
  Stages 1c–1e built four accumulation laws with no interaction term, and
  `Bridge.pair_comp_cert` was read as "carrying n properties costs n independent
  accumulations". That reading does not extend to the heap: NI for `deref` is
  *conditional* on memory safety, so the two cannot be certified side by side and
  conjoined at the end. Concretely, a combined checker cannot be
  `ucheckNI P c && slcheck V c` — the judgment must be indexed by the tracked set so
  the NI rule for `deref x` can demand `x ∈ V`, which is a new inductive rather than a
  conjunction. Both sites that made the independence claim (`Bridge.pair_comp_cert`,
  `four_laws_one_composition`) now carry the qualification next to the claim, and
  `check-claims` enforces that they keep it.

- **Fixed: stage 1i deleted a README heading.** The stage-1i insert used
  `## §11 pre-mechanization checklist (framework doc)` as its anchor and did not
  re-emit it, orphaning that section's bullets under the stage-1i text. Restored, and
  `check-claims` gains a required-headings guard so an insert that eats its anchor is
  caught rather than committed — the failure mode the guard suite exists for, and one
  it did not previously cover.

- **Composable core, stage 1k — the joint judgment stage 1j's counterexample forced**
  (`ConfTyping/HeapJoint.lean`). `JSecTy P V c V'` is a four-place relation carrying
  the partition *and* the tracked set, so the noninterference rule for `deref x` can
  demand `x ∈ V` — the side-condition neither system could state alone (`USecTy` has no
  `V`, `SepCert` has no `P`). `jsecTy_sound` proves both guarantees in **one**
  induction, with the memory invariant appearing as a hypothesis of the noninterference
  proof: that is the formal content of "these do not factor". `jcheck` decides the
  judgment and `jcheck_gives_both` extracts both guarantees from one run.

  `indexed_beats_the_conjunction` is the payoff. On `safeHeapProg` — allocate into a
  secret, dereference it, mediate an access, free it — `ucheckNI` rejects the program
  outright so no NI certificate is available at any partition, and `slcheck` accepts it
  but says nothing about leaks; `jcheck` certifies both. The indexed judgment proves
  what the conjunction of its parts cannot, which is exactly what stage 1j predicted
  from a single counterexample. `safeHeapProg_runs` confirms the program does what the
  prose says: access mediated, nothing faulted, pointer released.

  Getting here needed `SepCert.loop`, the loop rule for the memory certificate that
  stages 1h and 1i both ducked (both checkers return `none` at a loop). It is a fuel
  induction with the tracked set as the loop invariant, and it went in this module
  rather than as a back-patch to `MemLinear`, so stage 1i's claims stay as audited.

  Two rules stay conservative and both are recorded as theorems rather than footnotes:
  `allocL` is still absent (stage 1j's open question — it needs `fresh` in the
  observation, with `allocL_would_be_unsound` showing it cannot simply be added), and a
  loop must preserve the tracked set exactly, so `allocating_loop_rejected` refuses a
  loop that allocates although nothing about it is unsafe. The fix there is a widening
  step of brick 30's kind, which is real work rather than a missing line.

- **Composable core, stage 1l — widening, and the last of 1k's conservatism**
  (`ConfTyping/HeapWiden.lean`, plus `JSecTy.whileW` replacing `whileL` in
  `HeapJoint.lean`). Stage 1k named the fix instead of hiding it: iterate the body's
  effect to a fixed point, as brick 30's `loopFix` does for intervals. This is that
  step on a different lattice — the first time that fixpoint idea serves a second
  client.

  The tracked set is a **must** set, so weakening is *shrinking* and the fixed point is
  a descending iteration: start at the entry set, intersect with the body's effect,
  repeat. `narrowFix_spec` extracts precisely the two side-conditions `whileW` needs —
  the result is inside the entry set, and the body maps it into a superset of itself.
  The sets shrink and are finite, so `V.length + 1` steps always suffice and the budget
  is computed rather than guessed (`narrowing_budget_is_computed`).

  `widenProg` is the payoff: allocate `p`; loop, allocating `q` and dereferencing `p`
  each time round; dereference `p` again afterwards. The body's tracked set grows, so
  stage 1k refuses it, and `p` must survive the loop for the final dereference to be
  typable at all. `widening_beats_the_exact_rule` shows both halves — `jcheck` gives
  `none`, `jcheckW` gives `["p"]` — and `widenProg_both` extracts noninterference and
  memory safety for it.

  **Fuel index, not well-founded recursion.** The narrowing call sits under a closure,
  which structural recursion on the command cannot see through. Recursing on fuel keeps
  the definition structural, and structural definitions kernel-reduce, so every witness
  here is still a `decide`. The well-founded version was written first and type-checked
  — but it broke `decide` on all of stage 1k's witnesses, the same trap nested
  inductives set in bricks 32, 33 and 35. `jcheckW_out_of_fuel` records that exhausting
  the fuel is a refusal, never an acceptance, so the index can only add conservatism.

  Stage 1k's `jcheck` is left exactly as audited: its theorems and `decide`-checked
  witnesses stand unchanged, including `allocating_loop_rejected`, which
  `allocating_loop_now_accepted` pairs with rather than replaces. One item survives the
  conservatism list and it is a design question, not an engineering gap: `allocL` needs
  `fresh` in the observation, with `allocL_would_be_unsound` as the standing witness.

- **Composable core, stage 1m — the last open question, dissolved rather than decided**
  (`ConfTyping/HeapAlloc.lean`, plus `JSecTy.alloc` replacing `allocH` and the
  strengthened `jsecTy_sound` in `HeapJoint.lean`). Stage 1j framed `allocL` as a fork:
  allocation into a Low variable publishes the counter, so it looked to need `fresh` in
  the observation — a ruling on whether addresses are visible to a Low adversary, with
  a public allocator and an address-renaming bisimulation as the honest options.

  Neither was necessary. This type system has **no High-guarded control flow** — every
  `ite` and `loop` guard must be `exprLow` — so two Low-equal runs allocate in lockstep.
  `jsecTy_sound` now carries `s.fresh = s'.fresh` as a **relational invariant** rather
  than as an observation, and allocation becomes noninterferent with *no side condition
  at all*. The stage therefore **removes a hypothesis** instead of adding a rule:
  `JSecTy.allocH` becomes `JSecTy.alloc`, and `jcheck`/`jcheckW` lose their allocation
  test. Public statements are unchanged: `uOptLowEqA.toLowEq` projects the strengthened
  relation down, and two runs from `initU` agree on the counter for free.

  Two theorems keep it honest. `allocation_sync_is_load_bearing`: stage 1j's
  `allocL_would_be_unsound` is **still true** — nothing was refuted, and the same fact
  now states that the invariant cannot be dropped. `high_branch_desynchronises_the_allocator`
  with `highBranch_is_untypable`: one secret-guarded branch makes the counters differ,
  and that branch is untypable here, which is *why* the rule is sound. If `UCmd` ever
  gains High-guarded control flow, that pair breaks the build rather than silently
  invalidating `JSecTy.alloc`. `low_alloc_now_typable` is the new ground — a Low
  allocation the stage-1d checker still rejects outright.

  **The composable core's conservatism list is now empty.** Stage 1j opened three items
  (High allocation, `deref`/`free`, `allocL`) and 1k opened a fourth (the exact loop
  rule); 1k, 1l and 1m closed all four. What remains is *scope* rather than
  conservatism: `UCmd` has no strings, and the budget/mediation/ledger certificates are
  carried by `UCert` rather than by `JSecTy`.

- **Composable core, stage 1n — one checker, four certificates, and the law that does
  not compose over loops** (`ConfTyping/FullCert.lean`). Stages 1c–1e built a bundle
  (budget, authorization, ledger); stages 1h–1m built a joint judgment (noninterference,
  memory safety). They were separate artifacts — `ucheck` refused every heap operation,
  `jcheck` said nothing about cost — so no single program had carried all of them.

  `allcheck` does: one pass yields the authorization set, the tracked pointer set and
  the cost bound, and `allcheck_sound` turns that into a `FullCert`. `fullProg` — check
  a permission, allocate, read the mediated resource, dereference, assign, free — is the
  artifact the whole 1a–1n arc was for: **four certificates from one run of one
  checker**, with a *tight* budget (`fullProg_runs`: certified 6, spends 6).
  `fullProg_needs_its_check` confirms the mediation half is load-bearing.

  Most of this is integration, and it was expected to work: stages 1c–1e had already
  established that these laws do not interact.

  **What was not integration.** Extending the budget to heap operations needed a real
  rule, `UCert.memop` — stage 1h's `none` there was a placeholder, not a limit — and
  writing it exposed an asymmetry that two separate `none`s had been hiding. Three of
  the four certificates have loop rules: `JSecTy.whileW` (1l), `SepCert.loop` (1k), and
  mediation threads through unchanged. **The budget does not, and cannot**: a cost bound
  over a loop needs an *iteration* bound, which is a termination argument rather than a
  typing side-condition. `only_the_budget_lacks_a_loop_rule` states it;
  `loops_carry_three_of_four` shows the split is about which certificates a loop can
  carry, not about which programs are safe. Brick 30's `loopFix` and stage 1f's
  `countdown` are the two ways to supply the missing ingredient, and both are analyses
  of a different kind — a boundary rather than a to-do.

  Honest summary of the composable core: four certificates, one checker, on the
  loop-free fragment; three of the four on loops.

- **Composable core, stage 1o — strings, and injection on the unified machine**
  (`ConfTyping/TaintCert.lean`, plus `UCh`/`UStr`/`SExpr`/`sop` in `Unified.lean`).
  Every stage since 1h recorded the same limit: `UCmd` has no strings, so injection and
  path traversal are not *expressible* here. This adds the value domain — one new
  command constructor, which rippled a single new case into fourteen existing matches.

  **Two symbols, and that is the problem rather than an abstraction of it.** An
  injection succeeds by contributing a *delimiter* the author did not intend, so `UCh`
  is exactly "delimiter or not"; everything else about a character is irrelevant to the
  attack, and two symbols keeps every witness a `decide`.

  **Exact counts, not a taint bit.** A taint bit rejects every real query, because a
  query variable legitimately contains delimiters (`name='` has one). `TaintEnv` maps a
  string variable to the exact number it holds, `scount` computes an expression's count
  symbolically, and `sanStr` is the single discharge turning an unknown count into zero.
  The guarantee is structural: every emitted string carries exactly the predicted number
  of delimiters, so untrusted input cannot change the query's shape. `Ks` accumulating
  by `++` is a fifth monoid after `+`, threading, conjunction and the ledger's append.

  The row is four theorems: `injection_is_real` (the vulnerable program, run on a
  malicious input, emits **three** delimiters where two were written — the shape changed,
  which is the injection itself); `injection_rejected` (the checker refuses it, at the
  `emit`, which is where injection happens); `sanitised_query_checks`; and
  `sanitised_query_holds_under_every_input` (all attacker inputs, not one payload).

  A first draft of the `set` rule was **unsound**: a refused run stops updating the
  string store, so a recorded count need not survive an abort. `TaintInv` is therefore
  conditioned on `dead = false`, the same shape `MemInv` needed for the heap and for the
  same reason. Recorded here because the bug was mine and the fix is structural.

  Three deliberate limits. The sink is not in the noninterference observation, so
  `JSecTy` has no rule for `sop` — a checked program's *structure* is guaranteed, its
  confidentiality is not. Loops have no `tcheck` rule (the count environment needs
  stage 1l's narrowing — mechanical, but its own stage). And `ucheck`/`jcheck`/`allcheck`
  return `none` at a `sop`, so a string program cannot yet carry the other four
  certificates; merging `tcheck` into `allcheck` is packaging, not discovery. Path
  traversal is now *expressible* and **not done** — same shape with `/` and `..` — and
  is not claimed.

- **Composable core, stage 1p — the sink becomes observable, and one program carries
  five certificates** (`ConfTyping/AllFive.lean`, plus `sexprLow`/`evalS_lowEq` in
  `Unified.lean`, three `JSecTy` rules and a widened `uLowEqA` in `HeapJoint.lean`).
  Stage 1o left the sink **outside** the noninterference observation. That was a real
  weakness rather than a scoping choice: a sink is an *output channel*, so leaving it
  unobserved made every string operation trivially noninterferent — a program could emit
  a secret and still be "noninterferent". `uLowEqA` now includes the Low part of the
  string store and the sink; `JSecTy` gains `setH` (writing a High string variable is
  invisible), `setL` and `emit` (both need a Low value); `jsecTy_sound` threads the two
  new conjuncts through every case. `emit_of_secret_rejected` is the leak now caught.

  **`san` is not declassification.** Sanitising removes *delimiters*, not *secrets*, and
  `sexprLow` treats it that way — getting it backwards would be a vulnerability dressed
  as a discharge. `sanitising_does_not_declassify` makes it sharp: `emit (san secret)` is
  structurally perfect (count zero, cannot break a query) and still leaks. The taint
  checker accepts it, the noninterference checker refuses it, and neither is wrong —
  they answer different questions, which is the argument for carrying both.

  **The fifth certificate factors, unlike the third.** Stage 1j found NI and memory
  safety could not be established separately and conjoined, forcing 1k's indexed
  judgment. Structural integrity is not like that: the conditions an `emit` must meet —
  a known delimiter count, and a Low value — constrain different parts of the state. So
  `xcheck` is a *pairing* (`factoring_holds_here`) rather than a sixth judgment. Both
  facts are recorded because "these compose" is not a default: it held four times,
  failed once, and holds again here, each time for a reason.

  `fiveProg` carries **five certificates** — budget (tight: certified 6, spends 6),
  mediation, noninterference, memory safety, structural integrity — from one program.
  Remaining: loops carry three of the five (the budget cannot, per 1n; structural
  integrity has no loop rule yet), path traversal is expressible and not written, and
  stage 1e's ledger is not threaded through `xcheck`.

- **Composable core, stage 1q — path traversal, the last coverage row**
  (`ConfTyping/PathCert.lean`). Stage 1o guessed this was "the same shape with `/` and
  `..` in place of the delimiter". Half right, and the wrong half is the content:
  injection is about a **count**, traversal about a **prefix condition**. A path escapes
  when some *prefix* pops above the root, and no count can see that —
  `counting_cannot_decide_traversal` proves it, since `a/..` and `../a` carry the same
  symbols and only one escapes. So the two-symbol alphabet gets a second reading
  (`ord` = ordinary segment, `quote` = the parent segment) and a new property: `walk`
  runs the depth and fails on underflow, `safePath` is "the walk survives", and `spath`
  computes a *lower bound* on the final depth, which is what makes variables usable.

  **Path safety does not factor from taint.** To know a variable can only increase
  depth, the analysis must know it holds no parent segments — exactly the count-zero
  fact stage 1o's `TaintEnv` records. `path_needs_the_taint_environment` shows the same
  program refused with an empty environment and accepted once the variable is recorded
  as count-zero. That is the *second* dependency in the bundle after stage 1j's
  noninterference-needs-memory-safety, and unlike that one it is a clean layering:
  `PathCert` takes the environment as a parameter, so no new indexed judgment was
  needed. Two dependencies, two different remedies — worth recording, since 1j's
  remedy was the expensive one.

  **The discipline is per-sink**, which is what stage 1p's destination-recording sink
  was for: `pcheck fs` constrains only emits to `fs`, and
  `query_sink_untouched_by_path_checker` records that it says nothing about the others.

  The row is the same four theorems as injection: `path_escape_is_real` (the `../..`
  payload makes the vulnerable program emit a path that pops above its root),
  `path_escape_rejected`, `safe_path_checks`, and `safe_path_holds_under_every_input`.
  `StringInert` was extracted from stage 1o's five inert-command proofs so both string
  certificates share them rather than duplicating.

- **Composable core, stage 1r — loops for the two string certificates, and a corrected
  count** (`ConfTyping/StringLoop.lean`). Stage 1n measured "three of four certificates
  compose over loops" *before* there were string certificates; 1o and 1q then added two
  more, both with `| .loop _ _ => none`, quietly making the honest figure three of six.
  This closes it with exactly stage 1l's narrowing:
  `five_of_six_compose_over_loops` is now the statement, with the budget still the only
  law that cannot — a cost bound over a loop needs an *iteration* bound, and no amount
  of narrowing supplies one.

  Two things made it cheaper than 1l. **The emission list needs no widening**: `Ks`
  records *which* delimiter counts a program may emit — a set of possibilities, not a
  running total — so a loop emitting the same query a thousand times draws from the same
  `Ks`, and only the environment needs a fixed point (`interNat` iterated downwards,
  `narrowFix` with a different meet). And **the two certificates share the shape**:
  `TaintCert.loop` and `PathCert.loop` are the same fuel induction over the same
  weakening lemmas — the fourth and fifth appearance of the
  Hoare-triple-with-a-tracked-set pattern, which is the evidence the shape was right.

  `loopQuery` and `loopServe` are the witnesses (a query server and a file server, each
  emitting inside a loop); `loopQuery_needed_the_widening` shows stage 1o's checker
  could not handle them; `loopQuery_safe` and `loopServe_safe` give the guarantees over
  an unbounded number of emissions. Fuel-indexed for stage 1l's reason: the narrowing
  call sits under a closure, and a well-founded definition would break every `decide`.
  Stage 1n's docstring now carries a forward pointer so its figure is not read as
  current.

- **Composable core, stage 1s — the ledger, threaded: what must be true of the world**
  (`ConfTyping/Deploy.lean`). Five certificates say things about the *machine*. A
  deployment cares that the database accepts the query, that the filesystem serves a
  file inside the root, that the policy consulted is the policy intended. Stage 1e built
  the mechanism — a ledger that appends under composition and cannot be silently
  discharged — and it was never threaded through the rest of the core.

  **The result is a sorting, and it was not obvious in advance.** Noninterference and
  memory safety need *nothing*: they are statements about the machine's own state, and
  the machine is the artifact. The budget needs nothing either, being denominated in the
  model's own steps — converting it to seconds would need an assumption, "at most six
  steps" does not. Mediation, structural integrity and path safety need exactly one
  entry each, and the three belong to three *different* external components: the policy
  author, the query parser, the filesystem. So the trusted base of a fully-certified
  program is **three lines long**, and `Discharged` enumerates it.

  `deployment_reading` is the transformation from machine guarantees to deployment
  guarantees, and it needs no axioms at all. `toLedger`/`sat_toLedger` connect the
  entries to stage 1e so they append like any others.

  Two theorems stop it being a formality. `sink_assumption_is_load_bearing` exhibits a
  deployment whose parser accepts nothing: `fiveProg` really does emit, so the
  conclusion fails with the assumption however well the program is certified.
  `machine_guarantees_need_no_deployment` records the other half — the other three hold
  with the ledger *empty* — so the sorting is a fact rather than a presentation choice.

  A program can be certified to the hilt and still be wrong about the world. What the
  ledger buys is that the ways it can be wrong are listed, appendable, and impossible to
  discharge by accident.

- **Stage 1t — attacking the core on purpose** (`ConfTyping/Attack.lean`). Every finding
  from 1h onwards came from a counterexample that turned up while building something
  else, which only finds defects that happen to block the next step. This looks
  deliberately.

  **Twelve attacks, all refused**, each a theorem rather than an assertion: laundering a
  secret through concatenation and through sanitisation, branching and looping on a
  secret, use-after-free through an alias, freeing through a second name, a path built
  from a variable with unknown parent-segment count, an escaping literal, an access
  without its check, a check of the wrong resource. `twelve_attacks_refused` collects
  them so the list cannot shrink unnoticed. **No unsoundness was found in any checker.**

  **Three defects, all the same kind** — a guarantee narrower than its name:

  1. *The exported noninterference statement was vacuous for strings.*
     `xcheck_gives_five` states NI from `initU σ`, and `initU` gives every string
     variable the empty value — so two runs from it cannot differ in a secret string,
     and everything it said about the sink was true and empty. `jsecTy_sound` was
     general all along; only the wrapper was weak. Fixed by `allcheck_NI_general`, with
     `secretTouching_NI_is_real` as a witness where the runs genuinely differ in a
     secret string. Stage 1o's unobserved-sink mistake, one level up. The correction
     sits in `AllFive.lean` beside the claim it corrects, and `check-claims` enforces
     that it stays there.
  2. *The heap is a fiction.* `heap_is_never_touched`: no command reads or writes the
     `heap` field, so memory safety here is the liveness of addresses and says nothing
     about stored values — which is what the no-fault theorems claim, but not what a
     `heap : Int → Int` field in `UState` implies.
  3. *The allocator never reuses an address* (`allocator_never_reuses`), and `SepInv`'s
     freshness conjunct is where the proof uses it. Real allocators reuse, which is how
     use-after-free becomes exploitable rather than merely wrong; stage 1i's CWE-416
     result therefore carries a hypothesis that had never been written down.

  Also fixed: `fiveProg_deployed` took a mediation hypothesis that was derivable from
  `fiveProg_five`, making the theorem weaker than it needed to be.

  All three defects were in the **statements**, not the proofs.

- **Stage 1u — the allocator reuses addresses, and that opens a channel**
  (`ConfTyping/Reuse.lean`, plus a free list in `Unified.lean`, two new `SepInv`
  conjuncts in `MemLinear.lean`, and a new hypothesis on `JSecTy.free`). Stage 1t
  recorded "the allocator never reuses" as a limitation that stage 1i's use-after-free
  result silently depended on. Real allocators reuse; this one now does — `free` returns
  the address to a free list, `alloc` takes from it before touching the counter.

  **The separation argument survived**, which I had predicted it would not. It needed
  two more conjuncts: every freed address is *not live*, and every freed address is
  below the counter. With those, `alloc` still hands out an address distinct from every
  tracked one — from the free list by disjointness, from the counter by freshness. The
  old proof used only the second route, so this is a genuine case split.
  `stale_pointer_refused_after_reuse` shows the ABA hazard handled: after
  `alloc p; free p; alloc q` both variables hold **the same address** (`the_allocator_reuses`),
  `q` is usable and `p` is refused — the stale pointer rejected even though its address
  is live again, which is exactly what makes reuse dangerous.

  **Reuse opened a channel.** The free list decides the next address, so freeing a
  **High** pointer makes two Low-equal runs' allocators diverge and the next allocation
  into a Low variable publishes the difference. `freeing_a_secret_pointer_leaks`: two
  Low-equal, memory-safe states whose secret pointers hold 5 and 7; one `free`, one
  `alloc`, and a public variable holds 5 in one run and 7 in the other. Nothing faults.

  So `JSecTy.free` gained `P x = false` and all three checkers gained the test. Under
  the non-reusing allocator that rule was unnecessary — **the model had been too kind to
  require it**. `safeHeapProg` now allocates through a public variable instead of a
  secret one, because freeing a secret pointer is now genuinely unsafe rather than
  merely unmodelled. `allocator_never_reuses` is renamed `fresh_counter_is_monotone`,
  which is what it always proved.

  The exchange rate, stated plainly: removing a *limitation* cost one new typing
  restriction and two invariant conjuncts, and nothing that had been proved became
  false.

- **Stage 1v — the heap gets real `load` and `store`, and becomes public**
  (`ConfTyping/HeapValue.lean`, plus `HOp`/`hop`/`updHU` in `Unified.lean`, two
  `SepCert` rules, three `JSecTy` rules and a heap conjunct in `uLowEqA`). Stage 1t
  found the `heap` field was never read or written, so memory safety meant the liveness
  of addresses and nothing about stored values. Now `load d p` is `d := *p` and
  `store p v` is `*p := v`, both faulting on a dead pointer. `the_heap_is_live` closes
  the finding: allocate, write 42, read it back, 42 comes back.

  **The two properties reacted very differently to the same change.** Memory safety
  extended *for free* — the separation invariant never mentioned heap contents, so
  `SepCert.load`/`SepCert.store` need the pointer tracked and nothing else
  (`memory_safety_extended_for_free`). Noninterference did not: once a value travels
  from the heap into the store, the heap is part of what an adversary sees. `uLowEqA`
  gained `s.heap = s'.heap` and three rules appeared — `loadL` (Low pointer ⇒ Low
  value), `loadH` (High pointer ⇒ the destination must be High, so secret pointers stay
  usable without leaking), `storeL` (both operands Low).

  **The absence of a `storeH` rule is the finding.** Making the whole heap
  Low-observable is the simplest sound choice, and it makes the heap a **public
  resource**: `storing_a_secret_is_refused` shows a secret value cannot be written at
  any address. Lifting that needs a *label per address* — a heap of labelled cells, the
  label read at the `load` and checked at the `store` — which changes the state and the
  observation rather than adding a rule, so it is named and not attempted.
  `wild_store_faults` with `wild_store_rejected` keeps the guarantee non-vacuous.

  `heap_is_never_touched` is gone, being false now; `uexec_heap_fresh` is split into
  `uexec_fresh_mono`, which is the half that survives.

- **Stage 1w — per-address heap labels: the invariant** (`ConfTyping/HeapLabel.lean`,
  plus `hlab`/`MemOp.allocS`/`updBU` in `Unified.lean` and a split allocation rule).
  Stage 1v made the heap real and, to stay sound, made it entirely public. Lifting that
  needs a label per address, and the payoff rules can only be *syntactic* if the
  analysis can read a cell's level off the program text. This is the invariant half of
  that change; the rules are the next stage, so the invariant is audited before anything
  depends on it — the order 1j and 1k used for the analogous problem.

  * Cells are labelled at allocation, and `MemOp.allocS` makes the **site** declare the
    level. `allocation_site_must_match_the_level` shows a mismatch is refused.
  * **Allocation zeroes its cell**, and that is not tidiness: with reuse (stage 1u) a
    freed *secret* cell handed back out as a *public* one would expose its old contents
    — a public address whose value differs between runs. `allocation_zeroes` writes 7,
    frees, reallocates and reads 0. An interaction between two stages that neither
    produced alone.
  * `LabInv P V s` — every tracked pointer points at a cell of its own level — with
    `JSecTy.toLabInv` proving it inductive across all nineteen rules. **Separation
    (stage 1i) is what makes it hold**: no two tracked pointers can share a cell, so no
    cell has two levels, and the allocation case is the only one needing `SepInv`.
  * `JSecTy.alloc` gains `P x = false`, `allocS` requires `P x = true`. That is a
    *consistency* condition, not a secrecy one: stage 1m removed a secrecy condition and
    nothing it proved became false — the rule was split, not restricted. The correction
    sits on `alloc_rule_rests_on_low_guards`, where the old claim lives.

  **Not claimed:** the observation still contains `s.heap = s'.heap`, so the heap is
  still public and `storing_a_secret_is_refused` still holds
  (`heap_still_public_at_this_stage` records it). `LabInv` is proved and not yet used by
  noninterference — the honest description of an invariant stage.

- **Stage 1x — spending the invariant: the heap stops being public**
  (`ConfTyping/HeapSecret.lean`, plus a per-address observation and `JSecTy.storeH` in
  `HeapJoint.lean`). Two changes, and the stage is short because 1w did the work.

  The **observation is now per address**: `uLowEqA`'s `s.heap = s'.heap` becomes
  `s.hlab = s'.hlab ∧ (∀ a, s.hlab a = false → s.heap a = s'.heap a)` — labels are
  public, public cells are public, secret cells are not observed. And **`storeH`**: a
  secret may be stored through a secret pointer, because `LabInv` lets the analysis read
  the cell's level off the pointer's, which is exactly what makes the rule syntactic.
  `jsecTy_sound` gained the two `LabInv` hypotheses, with `JSecTy.toLabInv` supplying
  them at every intermediate state; nothing else about the proof changed shape.

  New ground: `secret_through_a_secret_pointer` and `secret_round_trip_checks` — a
  secret can now live in the heap. Boundaries that remain, and they are the right ones:
  `public_pointer_still_cannot_carry_a_secret` (a public pointer points at a public
  cell, so that really would leak) and
  `secret_cell_cannot_be_read_into_a_public_variable`. `the_heap_is_two_level` states
  all four. Stage 1v's `storing_a_secret_is_refused` survived **unchanged** — its
  pointer is public — but it is now a boundary rather than a blanket ban and its
  docstring says so; 1w's scope theorem is renamed
  `public_pointer_cannot_carry_a_secret` for the same reason.

  The remaining restriction is a design point, not a gap:
  `no_relabelling_operation_exists` — labels are fixed at allocation, so a cell cannot
  change level and a secret cannot be released. Declassification is a policy decision of
  the kind stage 1e's ledger records, not another typing rule.

  The invariant `LabInv` and its preservation moved from `HeapLabel` into `HeapJoint`,
  since they now have to precede `jsecTy_sound`; the guard was repointed accordingly.

- **Stage 1y — attacking the labelled heap** (`ConfTyping/HeapAttack.lean`). Stage 1t's
  discipline applied to 1v–1x: is the new guarantee vacuous, and is anything reasonable
  refused for a bad reason?

  **Not vacuous.** Stage 1t found noninterference exported from `initU` said nothing
  about strings, because `initU` makes both runs identical in that dimension. The heap
  could have gone the same way and does not: `secret_write_is_not_vacuous` runs a
  certified program from two `initU` states differing only in a High variable and lands
  with **different values in the secret cell** — 3 against 0 — while the runs stay
  Low-equal. The per-address observation is doing work.

  **A real gap, made by two correct rules.** Stage 1u: `free` needs a **Low** pointer,
  because the free list decides the next address and is observed. Stage 1w: a secret
  cell is reached through a **High** pointer, because the label must match the pointer's
  level. Each is right; jointly they are unsatisfiable, so **a secret cell can never be
  freed** and secret memory leaks by construction
  (`secret_cells_can_never_be_freed`). `memory_safety_would_allow_it` places the gap
  precisely — `slcheck` frees the secret pointer happily, so the refusal is entirely on
  the information-flow side — and `public_cells_can_be_freed` shows the restriction is
  specific. `both_rules_are_load_bearing` keeps the witnesses that neither rule can just
  be dropped.

  The fix is named rather than attempted: a separate, **unobserved** counter and free
  list for secret allocation over a disjoint address range, so that freeing a secret
  pointer perturbs only unobserved state — which is exactly what stage 1u's argument
  needs. Not a patch: `SepInv`'s freshness conjunct becomes two conjuncts over two
  ranges and range disjointness joins the separation argument, so on the evidence of 1w
  and 1x it is an invariant stage followed by a short rule stage.

- **Stage 1z — closing the gap: secret addresses are retired, not recycled**
  (`ConfTyping/HeapRetire.lean`, plus one branch in `uexec` and a dropped hypothesis on
  `JSecTy.free`). Stage 1y named a fix — a separate unobserved counter and free list
  over a disjoint address range — and predicted an invariant stage plus a rule stage.
  **The prediction was wrong and following it would have been expensive.**

  A much smaller change does the whole job: when a *secret* cell is freed, put its
  address nowhere. Freeing through a secret pointer then perturbs only `live`, which is
  unobserved, so `free` needs no level condition at all. `SepInv` did not change —
  pushing fewer addresses onto the free list only makes its conjuncts easier — and no
  new invariant appeared. `secretLifecycle` (allocate a secret cell, write, read back,
  release) is now fully certified; the last step was untypable before.

  **The price**, plainly: secret addresses are never reused.
  `public_is_recycled_secret_is_retired` shows a public allocate-free-allocate returning
  the same address and a secret lifecycle not. Address-space consumption, not a safety
  property, and the model claims nothing about exhaustion.

  **What became of stage 1u's rule.** Its leak witness is still true — a statement about
  two concrete states — but those states are now provably unreachable by a checked
  program: `ptrFive` aims a secret pointer at a cell labelled public, exactly what
  `LabInv` forbids (`the_leaking_state_violates_the_label_invariant`). Three stages were
  involved and **the middle one carried the load**, which was invisible when 1w was
  written because it had no payoff of its own. `free_requires_a_low_pointer` is replaced
  by `free_needs_no_level_condition`; 1y's `secret_cells_can_never_be_freed` and
  `the_gap` are replaced by their closed forms.

  Three memory-model estimates in a row have now been wrong — 1u cheaper than predicted,
  1w dearer, 1z much cheaper. The pattern in the misses is usable: the expensive changes
  touched the **observation** or an **invariant**; the cheap ones touched only the
  semantics.

- **Stage 2a — two threads on the unified machine** (`ConfTyping/Interleave.lean`).
  Brick 32 proved race freedom on its own language and has never been brought onto
  `UCmd`; that is the largest remaining distance between sixteen bricks and one core.
  Following 1z's rule of thumb, the first step is to find the obstruction rather than
  build the proof.

  `uexecPar` interleaves two threads at **command** granularity — a schedule picks a
  thread and its next command runs atomically, which is the granularity at which a check
  and its use can be torn apart.

  **Memory safety does not compose.** `interleaving_breaks_memory_safety`: two threads
  *each individually certified* — one allocates and dereferences (certified from the
  empty tracked set), one frees (certified given the pointer tracked) — with a clean
  sequential run and a **faulting** interleaving. Neither certificate is wrong; the
  tracked set is thread-local and nothing makes one thread's set an obligation on the
  other. By stage 1j's dependency the failure propagates: noninterference for `deref`
  needs that invariant, so the two properties cannot be rescued separately. 1j doing
  work at a distance.

  **The budget composes.** `budget_composes_across_threads` — interleaved and sequential
  runs cost the same. The one law that refused to compose over *loops* (1n) composes
  over *threads* without a murmur, because cost is a property of the trace and cares
  about neither state nor order.

  **The fix has a shape**: `disjoint_threads_are_safe` shows two threads sharing no
  variable are fine at either schedule — ownership in the separation-logic sense, with
  freeing the owner's prerogative. On the evidence of 1j → 1k that is a new indexed
  judgment rather than a side condition; on the evidence of 1w → 1x, an invariant stage
  before a rule stage. Not attempted here.

  Scoping note kept as a theorem: `addresses_depend_on_the_schedule`. The allocator
  hands out different addresses under different schedules. The schedule is a *public*
  input, demonic as in brick 32, so this is not a leak — it becomes one the moment a
  schedule can depend on a secret, which any scheduler model must state.

  This stage claims a machine, one obstruction and one positive. It does **not** claim a
  race-freedom certificate on `UCmd`; brick 32's results stay on their own language.

- **Stages G and H — the other tools turned on this repo's own claims**
  (`cross-check/leak-kani/`, `cross-check/alloy/BoundedGrade.als`). `PLAN-MULTITOOL.md` was
  **retargeted** first: its previous version planned to integrate a different project's
  verification estate, which misread the request. The tools are for *this* project, as
  adversaries and implementations.

  **Stage G — Kani against `leakSafe_sound`, the newest theorem in the repo.** An
  independent Rust re-implementation of `uexec`'s memory fragment and `lcheck`, written from
  the Lean, searched exhaustively over symbolic 5-node programs: **no program that
  `leakSafe` accepts and that leaks** (447 checks, 0 failed, 877 s). This attacks the gap
  Lean cannot see — a modelling error — rather than re-proving the theorem.

  **The negative was checked for vacuity rather than assumed.** A second harness asserts
  that no accepted program allocates, and Kani **refutes** it with an accepted, completing,
  genuinely allocating program (1104 s). Two concrete witnesses run in CI: `alloc p ; free p`
  is accepted and allocates, and **`b06` is refused by the independent port and really does
  leak** on the `skip` arm — the Lean finding reproduced by code sharing nothing with it.
  Divergences are argued, not waved at: accepted programs never free through an alias, so
  modelling `assign` as writing a non-address cannot hide a leak. Loops are **not** modelled,
  and 5 nodes is a **bound**.

  **Stage H — Alloy against stage F's algebra, and Alloy was wrong first.** Four checks at
  `for 6 Int`, two expected to fail. S2 and S3 are refuted, independently confirming
  `min_unsound` and `bounded_grade_does_not_factor` from a different engine with different
  arithmetic. But the first run reported a counterexample to **associativity** — proved in
  Lean, brute-forced over 42 875 triples. It was an artifact of **Alloy's own wrapping
  integers**: `plus[g1,g2]` overflows bitwidth 6 and returns negative.

  **That is this session's theme biting the method instead of the object.** A bounded model
  finder used as an adversary manufactures a false refutation out of its own bounds, and the
  bound is not in the verdict — `SAT` said "counterexample", not "counterexample, modulo my
  integers wrapping". Both runs are kept in `captures/`, the artifact under its own name.
  Self-test 41/41 → **44/44**; `tools/ci.sh` gains a cross-check step, skipped when cargo is
  absent.

- **Stage E — the emission census, run rather than read**
  (`conf-typing/corpus/estate/EMISSION.md`, real bytes in `captures/`). Eight tools, and
  every row produced by **running the tool on the estate's own artifacts** on 2026-08-14.
  **Six of eight emit something consumable; the kill criterion (fewer than three) did not
  fire.**

  **Coq and Lean turned out to be the best reception targets**, which was not the
  expectation. `Print Assumptions` and `#print axioms` emit *exactly* the object
  `Ledger`/`needs` is about — per theorem, already computed — and "does not depend on any
  axioms" is `condBoundary_nil` printed by the tool itself. Closer to this repo's machinery
  than CN or Jasmin.

  **Kani: the `unwind(N)` annotation is not the bound.** It is a search parameter. The
  epistemic status is a separate check (`.unwind.N`), and with unwinding assertions on —
  the default — an insufficient bound makes verification **FAIL** rather than quietly
  return a bounded result. Both cases were run. **The estate disables unwinding checks
  nowhere, so all 124 of its harnesses carry unbounded guarantees**, and stage F's bound gap
  does not touch them. The naive reading — bounded model checker, therefore bounded results
  — is wrong here, and would have been believed if this census had been written from
  documentation.

  **Alloy is the only genuinely bounded producer in the estate, and its certificate is split
  across two files**: the verdict on stdout (`UNSAT`), the scope in a `receipt.json` written
  beside the model. Neither half is a certificate alone — `UNSAT` with the scope elided is
  exactly the reading `min_unsound` punishes — and **the estate's own wrapper discards
  both**, reducing the run to a boolean.

  **TLC emits a numeric soundness caveat**: the probability a reachable state was skipped
  through a fingerprint collision (6.9E-7 optimistic, 2.6E-9 actual on the spec run).
  **`Ledger = List Prop` has nowhere to put a probability** — a new gap in the *receiving*
  machinery, found by running rather than reasoning.

  Verus was not on `PATH` here and is recorded as **unassessed** rather than guessed. Two
  corrections of record: the census first reported that Alloy emits no scope (read off
  stdout before the receipt was found), and `PLAN-MULTITOOL.md`'s own table called Kani
  bounded and said the estate was "full of" bounded instances — both written before any tool
  was run, both now amended in place. Nothing in the sentinel estate was modified; the
  output directory Alloy creates was removed afterwards. Self-test 39/39 → **41/41**.

- **The leak gap, closed — the map's one admitted false accept**
  (`conf-typing/ConfTyping/LeakCert.lean`). Row 6 of `VULN-COVERAGE.md` had said since the
  external corpus landed that leaks (CWE-401) are **not** detected, with `corpus/ext/b06` —
  a CWE-401 demonstrative example — **accepted** by this framework. That was the one
  vulnerability class the map admitted it missed.

  Closed under a **scoped exception** now written into `PLAN-2026-08.md`: the freeze's
  rationale is that growing `UCmd` toward *writability* is the Jif path §2.4 shows lost,
  which is a different thing from closing a named vulnerability class. Property coverage is
  permitted; functions, arrays, records and early return remain forbidden, as does driving
  the author-written corpus's false-rejection rate to zero. The exception may only be
  invoked by citing the map row that admits the gap.

  No construct was added to the language. `live` was already in the state, so `LeakFree` —
  a completed run leaves nothing allocated that it did not start with — is statable as it
  stands. `lcheck` tracks variables holding an unfreed allocation, and its teeth are the
  rules that refuse to **lose a handle**: writing over a tracked variable, branches whose
  arms disagree, and loop bodies that are not a fixpoint. `leakSafe_sound` is the soundness
  theorem, through an ownership invariant that survives an abort.

  `b06_rejected` + `b06fixed_accepted`: the example is refused, the repair accepted.
  **In-model missed vulnerability classes: 1 → 0.**

  **The restriction is real, and witnessed rather than asserted.** `LeakFree` covers runs
  that *complete*; `allocThenCheck_accepted` shows `alloc p ; check r ; free p` is accepted
  and leaks when the policy refuses `r`. Rejecting every allocation before a `check` would
  refuse most real handlers to buy a guarantee about an already-aborted path. Row 6 states
  it, and a guard fires if either the certificate or the restriction leaves the map.
  `corpus/ext/RESULTS.md` records the change **without rewriting the original measurement** —
  a corpus result edited after the fact stops being one. Self-test 36/36 → **39/39**.

- **Stage F — bounded guarantees as grades, and the first grade that does not factor**
  (`conf-typing/ConfTyping/BoundedCert.lean`). Alloy's `check … for 4 AbacPolicy`, CBMC's
  unwinding depth, TLC's finite instance are one shape: a guarantee quantified by a budget.
  The assurance-case literature downgrades these to *confidence*; this asks the algebraic
  question.

  **`min` is unsound, and not marginally.** `f x = x + 20`, `g` well-behaved only below 10 —
  both correctly certified, the rule claims the composite safe below 11, and **the composite
  fails at every input including 0**. No bound exists for which it is safe. Neither
  certificate is wrong and neither tool erred: the rule that combined them threw away the
  growth.

  So the grade is the pair `(bound, growth)`, composing as
  `⟨min b₁ (b₂ - g₁), g₁ + g₂⟩` — sound **with no side condition**, because the bound is
  stored strictly, making `0` the vacuous certificate that truncated subtraction lands on
  when the growth overruns. An `Option Nat` formulation with a `g₁ ≤ b₂` guard proves the
  same theorem with a hypothesis and eight case splits; the shift removes both. Associative,
  and **tight** — safe below 8, broken at 8, so the law is not buying soundness with
  conservatism.

  **The finding is `bounded_grade_does_not_factor`.** The composite bound is provably not a
  function of the two bounds — it reads the inner certificate's growth (same bounds, growth
  0 vs 3, composite 5 vs 2). A bounded certificate therefore **cannot be carried as a
  product of an independent bound and an independent growth**, so `pair_comp_cert`'s
  free-lunch componentwise composition does not cover it. Stage 1j found two properties that
  cannot be independently *derived* while insisting bundling stayed free; **this is the
  other half, and the first coupled grade in the repo** — a real limit on the central claim,
  found by the first example that was not built to fit it. The component taxonomy gains a
  third kind: contracting, inert, and now **coupled** — ignored by `act`, yet reading
  another component in `mul` (`bounded_phantom_not_inert`).

  Every result was established by exhaustive search before being proved: `min`'s
  unsoundness, soundness over 1 803 random claims against brute-force semantics, and
  associativity over 42 875 triples. Self-test 32/32 → **35/35**, including a case that
  strips the growth subtraction from `bmul` — which silently restores the unsound rule.

- **Stage D — the kill criterion, checked rather than assumed** (`conf-typing/ConfTyping/JasminCert.lean`,
  `conf-typing/CertCompose.lean`, evidence in `conf-typing/corpus/jasmin/EMISSION.md`).
  Stages B and C received both tools by **hand encoding**, which is exactly what stage D's
  kill criterion is aimed at. So the first thing owed was an empirical answer about two real
  tools, not a design. **It half-fires.**

  **Jasmin emits a certificate.** Its SCT checker prints an inferred signature per function
  — MSF-clobber flag, input type, output level, output corruption, constraints — and the
  project checks that text into its own repo and diffs against it in CI. A tool that
  regression-tests its own output has output stable enough to parse. `accept.expected` is
  copied here verbatim, and `certcompose` reads it.

  **CN does not.** Its JSON is a **timing log** — the reader CN ships opens with "for
  reading the JSON (ish) timing output" and introduces its parser with "this next bit is a
  total hack". Its Coq export emits proof *obligations* plus a support library, the opposite
  direction from a guarantee to receive. Success is an exit code and console prose.

  **The scope is therefore corrected rather than smoothed over:** a pipeline for Jasmin, a
  hand encoding for CN, and **a composite of two *different* tools still cannot be built
  from consumed artifacts alone**. That is a fact about what the ecosystem emits, not about
  the algebra.

  `compose_lvl_is_sctLvlGA` proves the level the combinator computes on consumed bytes is
  exactly `sctLvlGA.mul`, so the parser feeds stage C's algebra rather than sitting beside
  it. `--assembly` adds the compiler-preservation entry to the printed trusted base, because
  a claim about the binary needs it and a claim about the source does not.

  **Measured coverage: 20 of 57 (35%).** The other 37 certificates are polymorphic or
  compound and have no image in `SLvl` — recorded as unreceived rather than flattened, for
  the reason the CWE corpus recorded inexpressible tasks instead of adapting them.

  **The parser runs on `List Char` because `String.startsWith`/`splitOn` do not reduce in
  the kernel.** Testing over them would have required `native_decide`, which adds
  `Lean.ofReduceBool` to the axiom set and appears nowhere in this repo. `String.toList`
  does reduce, so it is the boundary, and every parser test is kernel reduction on real
  emitted bytes. A guard fires if `native_decide` ever appears in tactic position — and it
  had to be taught to tell prose from use, having first fired on the doc comment explaining
  why it exists. Self-test 28/28 → **32/32**; `tools/ci.sh` gained a step that builds the
  executable and runs it on the corpus, since the Lean samples cannot catch a parser that
  stops parsing whole files.

- **Stage C, second pass — the other tool already had a name for it**
  (`conf-typing/ConfTyping/JasminSCT.lean`, sources in `conf-typing/corpus/jasmin/SOURCES.md`).
  The first pass's second certificate was invented. This one is read out of Jasmin's own
  SCT test corpus, and reading it changed the result.

  **A Jasmin SCT level is a pair** — one level for normal execution, one for misspeculating
  execution: `public` = ⟨L,L⟩, `transient` = ⟨L,H⟩, `secret` = ⟨H,H⟩. That was not what I
  had from memory, and it is the whole point.

  **`transient` is exactly what a CN certificate becomes when carried into a speculative
  world.** Public normally, unconstrained under misspeculation. The first pass discovered
  that gap and described it longhand, building a counterexample to show architectural
  agreement is not enough; Jasmin had already named it, and named it as something *distinct
  from* `public`. `bcb_footprint_is_transient` is that as a theorem, and
  `protected_footprint_is_public` is `#protect` performing the upgrade — the first pass's
  sufficient condition discharged by the mechanism Jasmin actually ships.

  The anchor is `fig3a` from the S&P 2023 paper's own test file: a guarded load whose
  *value* becomes the *address* of a second access, with `#protect` as the fix. **The first
  pass had built that gadget abstractly before any Jasmin was read** — which is the best
  evidence available that the seam was located rather than constructed.

  Heterogeneity is now a fact about two real tools instead of a property of a witness built
  to have it: **CN's footprints union, Jasmin's levels join**, one `Bridge.comp`.
  `touchesOnly_imp_arch` earns the lattice's well-formedness — nothing sits at ⟨H, L⟩. The
  invented `sctGA` is kept rather than retrofitted, so the record shows the structure was
  discovered. Self-test 24/24 → **28/28**, including a case that collapses the level pair,
  which leaves every theorem compiling and the finding silently gone.

- **Stage C — where the interaction term lives** (`conf-typing/ConfTyping/HeteroCompose.lean`).
  `pair_comp_cert` says bundled certificates accumulate componentwise, with no interaction
  term. The secure-compilation literature says composing distinct properties gives roughly
  the intersection. This stage existed because both cannot be the whole story.

  **Both are right, on opposite sides of one hypothesis.** `Bridge.pair` demands
  `hmap : b₂.map = b₁.map`. Within one tool over one semantics that is `rfl` and invisible.
  Across two tools over *different* semantics it is a **semantic reconciliation
  obligation** the composition law neither performs nor mentions. Accumulation is free —
  downstream of an admission ticket that is not. The intersections are the price of the
  ticket, not a defect in the algebra.

  **The counterexample rules out the obvious reconciliation.** CN certifies ownership
  architecturally and says nothing about speculation; that is its stated scope. The
  bounds-check-bypass gadget agrees with its architectural counterpart **on the store under
  every schedule** — rollback is perfect — and keeps its CN footprint architecturally, and
  **still touches memory outside that footprint transiently**. State-level agreement does
  not transfer an ownership certificate; the residue is in the trace.

  **The sufficient condition** (`cn_reception_transfers`) is store reconciliation *plus*
  trace inertness — brick 33's `spec_inert` at this altitude — which discharges `hmap` and
  carries the footprint to every schedule. `hetero_bundle_laws` then shows the free half is
  genuinely heterogeneous: a footprint accumulating by **union** beside an SCT-shaped
  public set accumulating by **intersection**, advanced by one `Bridge.comp`.

  **Modelled, not transcribed**, and guarded as such: no Jasmin output is consumed, and the
  bundle witness and the counterexample are separate results. A name clash with brick 33's
  own `gadget` was caught by the flat-namespace guard on the first run. Self-test 21/21 →
  **24/24**.

- **Stage B — receiving CN's certificate** (`conf-typing/ConfTyping/CNReceive.lean`,
  sources in `conf-typing/corpus/cn/SOURCES.md`). Every `Bridge` until now certified
  something this repo also proved. This one **receives** a guarantee from CN — a
  separation-logic refinement-type verifier for real C, built on the Cerberus C semantics
  (POPL 2023) — the way `Bridge.ofKernel` receives a Dobrushin coefficient. No C is
  verified here.

  **The ownership half of a CN spec is the half that composes.** `take pv = RW<unsigned
  int>(p)` names the memory a function may touch; its observable content is a modifies
  clause. Grade = footprint, `mul` = union, `act_mul` = associativity of `∨`. **The kill
  criterion was that CN's guarantee might need an interaction term to state — it did not
  need one, and none was invented.**

  The milestone sentence — *CN certifies f, CN certifies g, therefore the composite carries
  both with trusted base = ledger(f) ∪ ledger(g)* — is `cn_comp_footprint` and
  `cn_comp_ledger`, both `rfl`, with `modifiesOnly_comp` proving independently that the
  union really is a modifies clause for `g ∘ f`. The anchor is the CN tutorial's own frame
  rule exercise, where `incr_first` owns `p` and not `q` and the caller gets `qv_ == qv`
  *derived* rather than proved; `cn_untouched_outside` is that derivation, out of the
  composed certificate.

  **The trusted base is computed, and comes out strictly smaller.** CN rests on Cerberus,
  its own type system, and an SMT backend — but its obligations are engineered into a
  decidable fragment, and a purely structural ownership obligation never asks the solver
  anything. `cn_base_strictly_smaller` exhibits a world where **the solver is unsound and
  the frame certificate stands anyway**, and the saving survives composition.

  **What it is not, guarded so it stays said.** The encoding is by hand and **unchecked
  against CN's implementation**: nothing proves `take RW<T>(p)` implies `ModifiesOnly`,
  which is CN's soundness theorem over Cerberus's memory model. `CStore` is a total map, so
  provenance, lifetime and alignment are absent; the functional postcondition is not
  modelled. Four new guard cases fire if the caveat is deleted, if `Bridge.ofCN` stops
  demanding the modifies clause (which would make every downstream theorem vacuous while
  still compiling), or if the transcription drifts back to the older `Owned<T>` spelling.
  Guard self-test 17/17 → **21/21**.

- **The external corpus** (`conf-typing/corpus/ext/`). Twelve programs transcribed from
  CWE demonstrative examples — code neither written by this repo nor for it — with the
  cases the language cannot express recorded rather than adapted (CWE-862 ex.2 needs a
  *subject*, which this model has none of; CWE-401 ex.1 needs an early return).

  **Detection: 6 of 7 real vulnerabilities caught** — use-after-free through two
  intervening allocations, conditional free then use, unauthorized protected read, query
  built by concatenation, and both infinite loops. **One missed, and it is a scope hole
  worth stating: no certificate here detects a memory leak.** The map now says so instead
  of omitting it, and corpus A's program 21 has had its *reason* corrected — the refusal
  was right, "because it leaks" was not why.

  **Precision: 4 of 5 safe programs accepted. The one rejected is the fix CWE-835 tells
  developers to write** — validate the rate up front, then loop. The good version is still
  an unbounded `while`; what makes it terminate is the validation. Our counted-loop rule
  takes its bound from a *syntactic constant*, so it refuses the recommended fix.

  That defines the next rule by evidence rather than taste: the bound must be allowed to be
  a **variable validated by a guard**, with the budget read off the guard — the first
  value-dependent rule in this repo, and the shape Jasmin's type system already uses.

  **Recorded, then deliberately not scheduled.** Written the same day, and reversed on
  reading the plan back: a value-dependent rule on `UCmd`/`bcheck` is Option 1 work on a
  component §4 rejects and the plan marks frozen. Driving an author-written corpus to zero
  is re-rigging by a slower route. It stands as a known limitation, with leaks and nested
  counted loops.

- **Corpus, and stage 2k — the first measured rule** (`conf-typing/corpus/`,
  `ConfTyping/CountedLoop.lean`). The repo had no idea what its checkers reject. The corpus
  fixes the method: a task list written first from ordinary handler patterns and CWE
  categories, every program written before the checker was run once, and the tasks the
  language *cannot express* counted rather than quietly dropped.

  Baseline: 30 tasks, **5 inexpressible (17%)**; of the 25 expressible, 20 accepted, 3
  correctly refused (unsanitized emit; `free` of a conditionally-allocated pointer; five
  allocations and one `free`), **2 falsely refused (8%)**. Both false refusals were in one
  rule — stage 2j's counted loop.

  Stage 2k fixes one of them by *widening*, not weakening: `UCert.forU` now accepts a body
  that **grows** the authorization set (`A ⊆ A'`) and still concludes `A`, since at zero
  iterations the body never runs — `JSecTy.whileW`'s widening one component over, resting
  on `UMedInv.mono`. False rejections **8% → 4%**, with the three correct refusals still
  refused and `loopHandler_checks` unchanged at budget 40.

  The remaining false rejection (nested counted loops) is left deliberately: driving a
  25-program author-written corpus to zero would be re-rigging by a slower route. The
  binding limitation is now the corpus, not the rule.

- **Stage 3a — source text, and a tool** (`ConfTyping/Surface.lean`, `Main.lean`,
  `examples/`). Every certified program in this repo was a hand-built Lean AST, and
  nothing in the repo was runnable — no `lean_exe`, no `main`. So the guarantee attached
  to something nobody outside the repo could write, checked by a function nobody outside
  Lean could run. Brick 21 made this complaint about the *query* language and answered it;
  the language that carries the five certificates never got the same treatment.

  `Surface.lean` gives it a syntax, a lexer, and a recursive-descent parser; `certcheck
  FILE [--secret names]` parses a file, runs `bcheck` and `tcheckW`, prints the
  certificate, and exits 0 / 2 / 3 for accept / parse error / reject.
  **`source_certified`** is the contract as a theorem — file parses to `c`, checker accepts
  `c`, therefore `c` has a uniform cost budget, mediated reads, noninterference and memory
  safety. `examples/handler.uc` is `loopHandler` as text and checks at budget 40, the
  number pinned in Lean. `examples/rejected/` holds one file per class: unmediated access,
  use-after-free, unsanitized emit, secret leak, secret branch, unbounded loop.

  **The residue is the parser, stated rather than glossed.** `parseE_toksE` proves the
  round trip for the expression layer. The statement layer is not proved, so the
  `parseSource` hypothesis in `source_certified` carries no logical weight yet — a parser
  that mapped the text to a different well-typed program would satisfy every theorem here.
  What closes it is known and named: the statement-layer round trip under a right-nesting
  hypothesis, and the lexer round trip that brick 22 already did once. And `UCmd` is still
  `UCmd` — no functions, no records, no arrays — so this is a tool you can run on a file,
  not yet a tool you can run on *your* file.

- **Stage 2j — the counted loop, natively** (`ConfTyping/CountedLoop.lean`). Every
  fully-certified program in this repo has been straight-line, and the reason is on the
  record: `only_the_budget_lacks_a_loop_rule` — five of six laws compose over loops, a
  cost bound needs an *iteration* bound, and brick 34's `dos_unbounded` proves no uniform
  one exists in general. Stage 1f found one way past it, `UCert.ofEmbedded`, which budgets
  a loop whose body is a **pure store program embedded wholesale** from the `While`
  development — which is why `handlerBounded`'s loop body is `.skip`. An embedded `WCmd`
  has no heap, no strings, no `check` and no `access`, so no certified loop could touch
  memory, be mediated, or emit.

  `forU i k body` is the counted loop with a **native `UCmd` body**: `countU_cost` bounds
  it by `1 + v·(b+2)` in the counter's value, `UCert.forU` turns a constant initialiser
  into the uniform budget `2 + k·(b+2)`, and `JSecTy.forU` supplies the flow and memory
  halves (the counter must be Low, so a loop whose *length* is secret is refused).

  The proof has a case stage 1f's cannot: a `WCmd` body has no way to die, and a `UCmd`
  body does. If the machine dies inside the loop the decrement is a no-op, the guard never
  falls, and the loop runs forever — `a_dead_counted_loop_does_not_halt`. So the budget is
  never violated because there is no halting run to violate it, and that is exactly what
  makes `countU_cost` provable. Recorded as a defect of the *language*: the fix is a
  `dead` short-circuit in `uexec`'s loop rule, which is a semantics change every module
  below depends on, and is named rather than guessed at.

  `bcheck` is `allcheck` plus one clause — everything that is not a `seq` or an `ite` goes
  straight to `allcheck`, so every earlier result applies verbatim — and `asFor` reads the
  iteration bound off the syntax. **`loopHandler` carries all five certificates while
  iterating**: budget 40, mediated reads *inside* the loop, noninterference, memory safety
  with a scratch cell allocated and freed each turn, and a sanitized query emitted per
  turn. `allcheck_refuses_loopHandler` is the contrast — the old checker returns `none`.
  Stage 2i's trace theorem covers it too (`loopHandler_trace_is_low`), which retires 2i's
  note that its loop-free restriction "is the budget's, not the trace's".

  The boundary is unmoved: `unbounded_countdown_still_refused`, and
  `only_the_budget_lacks_a_loop_rule` stays true as written — there is still no rule for a
  general `.loop`, and brick 34 proves there cannot be. Standard three axioms, no `sorry`.

- **Stage 2i — the fused induction, and the trace theorem**
  (`ConfTyping/SpecFused.lean`). Stage 2d stated a conjecture: *for every program `xcheck`
  accepts, the speculative address trace is a function of the Low part of the initial
  state, under every window*. Stage 2f found it false in the model as it then stood and
  repaired the model; stage 2g proved the obvious proof strategy cannot work. **This
  stage proves it.**

  - **`jcheck_ptrLow`** — stage 2f's `PtrLow` is inductive over *whole* certified
    programs, `seq`, `ite` and `loop` included, carrying `SepInv`, `LabInv` and `uLowEqA`
    alongside. That hypothesis list is the content: stage 2g's `traceEq_is_not_inductive`
    proved that a relation omitting the two memory-safety invariants breaks at its first
    step, so nothing lighter would do.
  - **`transRun_agrees`** — the transient window is itself a certified run whose *state*
    is discarded, so `touched_agrees` fixes each command's contribution and the invariant
    carries to the next. This is where the trace theorem is actually earned; the
    architectural half was never the hard part.
  - **`jcheck_strace`** — the trace of a certified program is the same in two runs from
    states satisfying the fused invariant, **at every window and every fuel**.
  - **`certified_trace_is_low`** — the conjecture, in stage 2d's own words, via
    `allcheck_jcheck`: `allcheck` is `jcheck` rule for rule on the pointer component, so
    everything above applies to every program the five-certificate checker accepts.

  Brick 33 needed a `fence` to say this on a language with no certificates. On `UCmd` no
  new rule was needed and none was added: the rules that exclude the gadget are stage 1i's
  linearity discipline and the flow certificate, both written years of stages before
  speculation was in view. `the_hypothesis_is_load_bearing` keeps the other half on
  record — `victimU` leaks, and `xcheck` refuses it.

  Applied, not just stated: **`bigHandler_trace_is_low`** puts stage 2h's twenty-one
  operation handler under the theorem, and its trace is six addresses rather than empty.
  `brWitness` supplies what `bigHandler` could not — a certified branching program whose
  *mispredicted* branch really lengthens the trace (`[1]` at window 0, `[0, 1]` at window
  1) and whose trace agrees between two stores differing in a secret anyway.

  Honest scope, unchanged from 2d: addresses only, so no cache lines, eviction, timing or
  contention; one global window; loop guards always predicted correctly; no nested
  speculation. `allcheck` still has no loop rule, so "every program `xcheck` accepts" is
  every loop-free one — `jcheck_strace` and `jcheck_ptrLow` both handle `loop`, so that
  restriction is the budget's, not the trace's. And **the cost stays broken**:
  `transient_work_is_off_the_budget` is untouched, the count of transient commands is
  still off the certificate, and stage 2e's bound is still the only thing bounding it.

  The stage is a *proof*, so it is not `decide`-checked: the standard three axioms, no
  `sorry`. Eleven new drift guards, plus four pinning the fused invariant's fields and two
  pinning the headline measurements, each negative-tested; two new guard-selftest cases
  (16/16).

- **Stage 2h — a program worth the name** (`ConfTyping/BigHandler.lean`). Every worked
  example so far has been small enough to read in one line, and four of the last five
  stages were obstructions rather than artifacts. `bigHandler` is twenty-one operations —
  two authorization checks, two mediated reads, three allocations (one secret), pointer
  stores and loads, arithmetic, a sanitized query built and emitted, a branch, two
  dereferences, three frees — carrying **all five certificates from one run of one
  checker** at budget 24.

  Measured, not asserted:

  - the **trusted base is still two entries** at twenty-one operations, because stage 2c's
    `needs` charges what the program does rather than how long it is;
  - the **secret address is retired, not recycled** — three allocations, three frees, and
    `freed = [0, 1]`, with the `allocS` cell gone from circulation. Stage 1z's rule,
    introduced to close a two-line leak, as a fact about a real run;
  - the budget is **tight**: 24 certified, 24 spent;
  - stage 2e's **speculation bound does real work and is loose by a factor of three** —
    `bigHandler` branches, so at window 2 it really runs 26 commands against a certified
    24, and the bound allows 72. That is what "a full window per command rather than per
    branch" costs on something concrete;
  - its **trace does not grow** under misprediction, but only because the untaken branch
    touches no memory — recorded as a measurement and explicitly not a theorem, since
    stage 2g is the reason no theorem is available.

  No new rule, no new obstruction, and no new defect: everything held at three and a half
  times the previous example's size, which after four consecutive obstruction stages is
  worth recording.

  Limits kept in the module: the program is loop-free because `allcheck` has no loop rule,
  and `decide` does the work throughout, so the evidence is kernel computation on closed
  terms and says nothing about programs not run. Three of the measurements are
  **axiom-free**.

  Twelve new drift guards plus two pinning the headline numbers — the checker's result and
  the real-versus-certified cost — each negative-tested. Also added: a guard against stray
  Lean files at the repo root, after `printf >>` from the wrong directory created one four
  times in one session.

- **Stage 2g — the trace does not factor either**
  (`ConfTyping/SpecFactor.lean`). Stage 2f produced the two halves of a step case. The
  obvious next move is to lift them by induction, layered on the noninterference proof the
  repo already has. That does not work, and this stage says why as a theorem rather than
  as a difficulty.

  Write down the relation a trace argument visibly needs — low-equal stores for the branch
  guards, equal `dead`, equal `fresh`/`freed` for the allocator, agreeing public cells,
  and `PtrLow` for the addresses — and call it `TraceEq`. It omits `SepInv` and `LabInv`
  because nothing in the *statement* of trace agreement mentions separation or heap
  labels. `traceEq_is_not_inductive` shows one certified command breaks it: a `load`
  through a **Low** pointer, which `jcheck` accepts whenever the source is tracked and
  `!P p || P d`, so a Low pointer may load into a Low variable — and if the cell it points
  at is secret the two runs then disagree in a Low variable.
  `labInv_is_the_missing_hypothesis` names the exclusion, and `publicCell_labInv` confirms
  the invariant is not vacuous.

  So the trace conclusion belongs **inside** `jsecTy_sound`, which already threads
  `SepInv`, `LabInv` and `uLowEqA` through every rule, with `PtrLow` as a fifth hypothesis
  and `touched` agreement as a second conclusion. `traced_step_agrees` assembles 2f's
  halves into exactly that step case; it is the frame that has to change, not the step.

  This is **stage 1j one level up**. 1j showed noninterference and memory safety do not
  factor. The entanglement now reaches the trace: the addresses a program touches cannot
  be shown Low without the heap-label invariant, which is a memory-safety artefact. The
  core has hit that wall from three directions, which makes it a design fact rather than
  an observation about three proofs.

  Honest limits kept in the module: `TraceEq` failing does not mean no lighter relation
  works, only that the obvious one does not and for a structural reason; and the transient
  window is untouched, since `transRun`'s inheritance from the fused induction is a lemma
  nobody has written.

  Six new drift guards plus two pinning the negative result — that `TraceEq` still exists
  and still omits both invariants — each negative-tested, including by *adding* `LabInv`
  to the structure and confirming the guard fires.

- **Stage 2f — attacking the trace conjecture, and what it cost**
  (`ConfTyping/SpecTrace.lean`). Stage 2e left exactly one question: is a certified
  program's speculative trace a function of the Low part of its input? Attacking it did
  two things, and the first is a correction.

  **The conjecture was false, and speculation had nothing to do with it.** `deadS` — fail
  a mediation `check`, then allocate a secret pointer and dereference it — passes
  `xcheck`, all five certificates, and its trace at window **zero** was `[11]` against
  `[77]` for two low-equivalent stores.

  The defect was in stage 2d's trace, not in any certificate. A failed `check` sets
  `dead`; `uexec` then makes every subsequent command a no-op, so `allocS` never runs and
  `secret` keeps its *initial* value; and `touched` recorded an address anyway. A command
  that does not execute does not issue a memory operation. `touched` is now conditioned on
  `dead` — the same shape stage 1q needed for `TaintInv`, for the same reason — and
  `touchedRaw` is kept, guarded, so the retracted definition can still be pointed at
  instead of quietly disappearing. Everything stages 2d and 2e proved survives the fix
  unchanged, because none of their witness states is ever halted. That is luck rather than
  design, which is why the witness is on record.

  **The invariant the repaired conjecture needs.** Every traced address is `s.store x` for
  a tracked pointer, so what is wanted is `PtrLow V s s'`: every tracked pointer holds the
  same address in both runs. It is **not** implied by `uLowEqA`, and
  `ptrLow_is_not_implied_by_uLowEqA` proves it — `allcheck`'s `allocS` rule *requires*
  `P x = true`, so a secret-*named* variable is a legitimate tracked pointer and
  low-equivalence says nothing about its contents. The invariant holds anyway, for a
  different reason: the allocator is driven by `fresh` and `freed`, which `uLowEqA` does
  synchronise. Exactly the kind of fact that has to be carried rather than derived.

  `ptrLow_step` proves it inductive over every atomic command — both allocators, both
  faulting paths, the loop-exit case — and `touched_agrees` cashes it: two runs satisfying
  the invariant touch the same addresses. Those are the two halves of stage 2g's step
  case. What remains is the whole-program induction and the transient window.

  Ten new drift guards plus two pinning the correction itself, each negative-tested. All
  theorems audited: standard axioms only, and `ptrLow_initial` is axiom-free.

- **Stage 2e — what speculation costs, and what it cannot touch**
  (`ConfTyping/SpecBudget.lean`). Stage 2d left one genuine unsoundness — the certified
  budget ignores transient work — and one positive so narrow it barely counted. Both are
  closed here, and the second turns out to have been the wrong statement of a much
  stronger one.

  **Rollback is complete.** `rollback_is_complete`: for every program and every window,
  the architectural state after speculation is the state `uexec` reaches. Stage 2d proved
  this only for branch-free programs, as a by-product of proving something stronger about
  them. Generalising 2d's faithfulness lemma from `w = 0` to every `w` costs nothing — the
  transient parts live in the two components that lemma projects away — and makes it a
  corollary, and universal. Stage 2d's prose has been corrected accordingly in both the
  module and the README: `spec_is_uexec_extended` now reads "at every window", and a guard
  pins the general form so it cannot silently narrow again.

  **Four of the five certificates are therefore immune.** `four_of_five_are_immune` and
  `ni_transfers_to_speculation`: mediation, memory safety, structural integrity and
  noninterference are predicates on the final `UState`, and a machine reaching the same
  final state satisfies them identically. No rule changes, no side condition, no fence —
  they were never at risk, and the reason is one line long.

  That leaves the surface exactly two things wide: the cost and the trace.

  **The cost, bounded.** `spec_cost_bound`: in any run, `realCost ≤ archCost * (1 + w)`.
  The budget is not lost to speculation, it is scaled, and the multiplier is the
  misprediction window. Stated within a single run, so it needs no two-run comparison.
  `certified_cost_under_speculation` composes it with a certificate — a program checked at
  bound `k` really executes at most `k * (1 + w)` commands, transient work included — and
  `fiveProg_costs_six_even_speculating` covers the worked program, which being branch-free
  pays nothing. `the_bound_is_not_vacuous` exhibits a certified program whose real cost
  genuinely exceeds its certified one.

  `uexecS` now carries both numbers, so stage 2d's finding is sharper than it was: the
  same run reports architectural cost 2 and real cost 3.

  Looseness stated rather than implied: the bound charges a full window to every *command*
  rather than every *branch*, so `k * (1 + w)` sits far above the true
  `k + w * (branches taken)`; tightening it needs a branch count in the judgment. And the
  **trace** question is untouched — it remains stage 2d's conjecture, and separating the
  stages is what makes clear which one moved.

- **Stage 2d — speculation on the unified machine: the attack that does not land**
  (`ConfTyping/SpecUnified.lean`). Brick 33 put Spectre in the semantics and closed row
  9, but on its own small language; the five-certificate core lives on `UCmd`. This
  stage brings the machine across and asks what the certificates survive. **The answer
  was not the one the stage set out to write down** — the plan was to exhibit a
  certified program that leaks, and no such program could be constructed.

  `uexecS` is `uexec` with an address trace and misprediction: at an `ite` the untaken
  branch also runs, for a window of `w` commands, state discarded and trace kept.
  `spec_is_uexec_extended` proves the extension faithful at `w = 0`, so nothing below is
  an artifact of a substituted machine, and `victimU_leaks` shows the model is not
  vacuous — the textbook gadget, two heaps differing in one cell, two different traces.

  **The core already rejects it, via rules written for other purposes.** `slcheck`'s
  load rule requires the source to be tracked and *drops the destination*, so a loaded
  value can never afterwards be dereferenced and the gadget has no derivation
  (`gadget_rejected_by_memory_safety`) — that is stage 1i's linearity discipline. And a
  branch on a secret is refused by the joint checker, so which branch mispredicts cannot
  depend on a secret either (`secret_guard_rejected`); memory safety alone would have
  allowed that, the flow certificate is what refuses. There is no pointer arithmetic
  either, so the bounds-check-bypass half of Spectre-v1 has no analogue at all
  (`no_pointer_arithmetic_here`) — an absence in the model, recorded so it does not read
  as a result.

  **This is not a closure of row 9 on `UCmd`, and is not claimed as one.** Two
  exclusions and an absence are not a theorem: the certificates are about `UState`, the
  trace is not in `UState`, so nothing proves a certified program's trace is
  secret-independent. A search for a third route did not find one; that is a failure to
  find and is recorded as such. The conjecture is written into the module so it can be
  attacked rather than assumed.

  **What is genuinely broken: the budget.** `transient_work_is_off_the_budget`, on a
  program the core does certify — the bound is 2, the machine reports 2 at every window,
  and at window 1 a third command really ran. Stage 1n found the budget would not
  compose over *loops*; stage 2a found it was the one law that *did* compose over
  *threads*. It fails here in a third and different way: not wrong about what it counts,
  but counting the wrong thing.

  Proved positive: `branch_free_is_inert` — no `ite` means window-independence, so every
  architectural guarantee transfers under *every* misprediction, covering `fiveProg`.

  Scoping stated rather than implied: one global window at every branch rather than
  brick 33's per-branch schedule (a stronger attacker, so nothing here is weakened);
  loop guards always predicted correctly; an address trace only, so no cache lines,
  eviction, timing or contention; conditional-branch misprediction only. No fence rule
  on `UCmd` — brick 33 has one on its language and porting it is the named follow-on.

- **Stage 2c — the trusted base, computed from the program**
  (`ConfTyping/Assumptions.lean`). Stage 1s said the trusted base of a fully-certified
  program is three lines: the policy author, the query parser, the filesystem. That was a
  statement about the *language*, stated as a fixed `Discharged` record demanding all
  three of every program. Three stages flagged the missing link to stage 1e's ledger
  without making it.

  The gap was not plumbing, it was **overcharging**. A program that never calls `access`
  reads nothing, so "the deployed policy is the intended one" is not an assumption it
  needs — it is a statement about nothing.

  So the ledger is computed. `needs c` collects from the syntax exactly the obligations
  the program can incur; `needsLedger` turns them into a stage-1e `Ledger` that composes
  like any other. Two lemmas, both by fuel induction over every command, prove the
  omitted entries are omitted for cause: `no_access_no_reads` (no `access`, no reads) and
  `unwritten_sink_untouched` (a sink never written stays as it was).

  What it buys: `pureProg_deployed_with_nothing` gives all three deployment-level
  guarantees for a pure computation with the ledger **empty** — no policy author, no
  parser, no filesystem trusted. Stage 1s could not state that, because
  `deployment_reading` demanded a `Discharged` record and that is three assumptions
  whether or not the program uses them. And `fiveProg_deployed_with_two` proves the
  identical three conclusions from **two** entries instead of three, the filesystem
  conclusion holding vacuously. `discharged_covers_needs` confirms the old hypothesis
  always implies the new one, so nothing that held before stops holding.

  The limit is a theorem, not a footnote: `needs` is syntactic, and `needs_is_syntactic`
  shows an `access` in dead code is still charged. No reachability analysis is attempted
  — over-charging the trusted base is the safe direction. `an_fs_writer_is_charged` and
  `access_really_reads` negative-test the exemptions.

- **Stage 2b — ownership: why thread-local certificates cannot compose**
  (`ConfTyping/Ownership.lean`). Stage 2a's counterexample was about *runs*, which
  leaves open where the reasoning fails. This pins it at the invariant.

  **`SepInv` is not conjunctive.** `separation_is_not_conjunctive` gives one state
  satisfying `SepInv ["p"]` and `SepInv ["q"]` and *not* `SepInv ["p","q"]` — the two
  pointers alias. Two thread-local certificates therefore say nothing about the pair,
  which is exactly where 2a's faulting interleaving comes from. Same shape as stage 1i's
  `memInv_not_preserved_by_free`: a counterexample at the level of the invariant,
  showing the missing rule is an obstruction rather than an omission.

  So the object to maintain is `SepInv (V₁ ++ V₂)`, over the **union**.
  `union_gives_both` shows it delivers both thread-local invariants and
  `ownership_is_the_missing_hypothesis` shows what it adds: cross-thread address
  disjointness.

  **The frame rule decomposes into three kinds of case**, which is worth knowing before
  writing it. Most commands frame dully — they change neither `live` nor the store
  outside their own targets. `alloc` frames for an *interesting* reason: the new address
  must differ from the other thread's pointers, the freshness conjunct working across a
  thread boundary (`alloc_frames_over_a_disjoint_set`, proved). And `free` **cannot**
  frame, because it removes an address another thread may hold;
  `free_frames_when_owned` states the rule an ownership discipline would license, and
  its hypothesis is what the discipline must enforce.

  Next is a judgment indexed by an ownership split with the frame rule as its central
  lemma. Both precedents for that shape — 1j → 1k and 1w → 1x — were about a dependency
  between two *properties*; this one is between two *threads*, and the recurrence is
  itself worth noting.

## transport-calculus — the certified-morphism interface (mathlib-free)

- **Set-theory research line, notes §58 — (Q-spread) is a rate race, not an
  impossibility.** §57 localized (C2) to the level-minima and refuted the level-factored
  side, leaving the impression that the minima had no reason to reach the walk bars.
  §58 shows that reading is wrong, in three steps.

  **Lemma Y1 [ZFC]**: fiber-specialness *already* diverges the minima — under (C1),
  `{α<β : m_u(α) < N}` is finite for every `N`, by the same one-line counting that makes
  distinct levels contribute distinct elements. **Lemma Y2** (Handbook 1.16(a)) diverges
  the bars. So **Corollary Y**: (C2) compares two functions of `α` that are each
  finite-to-one below every bound — an eventual-domination between sequences of the same
  kind. The two conjuncts of §56 are therefore *not independent*: the first supplies the
  shape the second needs.

  **Lemma Y3 [ZFC]**: at any *single* down-set both conjuncts hold together — `↓u` is
  countable, so enumerating it and setting `rank(xᵢ) := max(i, ρ₁(γ(xᵢ), β))` gives (C1)
  at `u` and makes `BS(u)` **empty**. So neither conjunct alone, nor both at one `u`, is
  an obstruction: **the entire residual of (Q-spread) is simultaneity across overlapping
  down-sets**, restated as a covering condition on the unavoidable exceptions that
  Corollary X1 forces at every `S`-level. Fifth appearance of the program's
  self-similarity and the sharpest: factored side refuted, pointwise side solved, only
  the gluing open.

  **A third recorded inversion, this one deliberately provoked.** 1.16(a) is now
  load-bearing four times, so it was added to `tools/walk-check.py`. The identity-level
  half (counts monotone in `n`) passes, 15000 instances over twelve C-sequences. The
  asymptotic half — rows unbounded — is **false in the truncated model**: for `β ≤ 11`
  every `ξ` has `ρ₁(ξ,β) ≤ 3`, there being too few limits-of-limits for the expensive
  walks. The assertion was removed and the reason recorded in the tool. After §54 and
  §57, the third time the model has inverted an asymptotic claim, and the first time the
  check was run *expecting* it.

  **A guard-suite bug, caught by the guard suite.** The self-test case for "README falls
  behind the notes" hardcoded `§57`, so once the notes reached §58 the mutation stopped
  breaking anything and the case silently passed without testing. `guard-selftest`
  reported the failure on the next run; the case now computes the current highest section
  instead of pinning one. A negative test that goes stale is worse than no negative test,
  and this is exactly the failure mode the suite exists to catch — this time in itself.

- **Set-theory research line, notes §59 — where the simultaneity lives.** §58 reduced
  (Q-spread) to simultaneity across overlapping down-sets; §59 asks what governs the
  overlaps, and the answer is tighter than expected.

  **Lemma Z1**: (C2) implies the canonical necessary form — for every `β` and `C =∗ B_β`,
  `{α<β : rank(α, B_α∩C) < ρ₁(α,β)}` is finite. **Lemma Z2 (uniform discrepancy) [ZFC]**:
  for `α<β<β′`, `(B_α∩B_β) Δ (B_α∩B_{β′}) ⊆ B_β Δ (B_{β′}∩β)`, and *that finite set does
  not depend on `α`* — moving between two down-sets perturbs **every level at once, by
  subsets of a single finite set**. Machine-checked at 732000 instances over six
  C-sequences and added to `tools/walk-check.py`; it is an identity-level claim, the
  regime §58 established the truncated model is sound for.

  **Corollary Z3**: between two down-sets a rank has at most `2^{|F|}` canonical values
  per level, and the choice is dictated by `B_α ∩ F` rather than free. Two things it does
  *not* give are recorded so the reduction is not over-read: `g_β` is a pointwise
  selection among level functions, not a level function; and `|F(β₀,β)|` is not bounded
  by anything proved here.

  **The residual now reduces to a question about the C-sequence alone** — no ranks, no
  down-sets: *is `|B_{β₀} Δ (B_β ∩ β₀)|` bounded in `β` for some `β₀`?* Yes gives a single
  dominating level function below `β₀` and resolves (Q-spread) negative via Theorem X; no
  names the discrepancy as the resource a construction must spend.

- **Set-theory research line, notes §60 — CORRECTION to §59 (seventeenth flip).** §59's
  closing claim — that a bound on `|B_{β₀} Δ (B_β ∩ β₀)|` would resolve (Q-spread)
  negative via Theorem X, so the residual reduced to a question about the C-sequence
  alone — **does not hold**, and is withdrawn. Two independent gaps:

  *Bounded is not finitely many.* The Theorem-X route needs the perturbations drawn from
  a **fixed finite** family; a bound `|F| ≤ k` does not supply one, since up to `k`
  elements may be added from the infinite pool `β₀ \ B_{β₀}`, so the family
  `{B_β ∩ β₀ : β>β₀}` can be infinite and the sup of ranks over it unbounded.

  *A countable initial segment cannot contradict Theorem X.* Even granted a level
  function `M` below `β₀`, what follows concerns a **countable** set of levels; extend `M`
  above `β₀` by anything and the hypothesis fails immediately. Theorem X's proof runs on
  the regularity of `ℵ₁`.

  What would actually suffice is `sup_{β>α} rank(α, B_α ∩ B_β) < ∞` cofinally — a
  condition on the **rank**, not on the sequence — so the reduction to a property of the
  sequence is withdrawn.

  **Salvaged: Lemma W1**, free of hypotheses. For every `β₀` there is a single
  `X =∗ B_{β₀}` with `B_β ∩ β₀ = X` for *uncountably many* `β`, because the trace takes
  only countably many values on a countable initial segment. Also recorded: two natural
  routes from W1 to triviality both fail for the same reason — two uncountable subsets of
  `ω₁` need not meet — which is worth having written down, since both look like they
  should work.

  Lemmas Z1, Z2 and Corollary Z3 stand unaffected; the budget reading of §59 is intact.
  First flip in this line caught within one section of being written, and the prompt was
  mechanical: the claim asserted an implication with two quantifier steps in it and
  neither had been written out.

- **Set-theory research line, notes §61 — the W1 route.** §60 salvaged Lemma W1 and left
  it unused; it turns out to be exactly what the Theorem-X route needed. On the
  uncountable `T` where the trace on `β₀` is constant, the canonical elements **freeze**:
  `B_α ∩ B_β = B_α ∩ X` for every `α<β₀` and `β ∈ T`, so `g_β` is one function `G` with no
  `β` in it. A pigeonhole on the finite exceptional sets over the uncountable `T` then
  gives **Theorem W2 [ZFC]**: if (C2) holds, for every `β₀` all but finitely many `α<β₀`
  have an **uncountable** column `Col(α,G(α)) = {β : ρ₁(α,β) ≤ G(α)}`.

  Contrapositively, **(Q-spread) is answered NO if `ρ₁` has countable columns at
  `S`-levels** — the new question **(Q-col)**, about the walk alone. This is the reduction
  §59 aimed at and missed, reached by a different move: not *bounding* the discrepancy but
  finding where it is **constant**, which W1 supplies for free in every coherent sequence.

  Kept honest: (Q-col) is **not** answered, and the obvious attack is shown to fail —
  `ρ₁(α,β) ≥ |C_β ∩ α|` controls only the first step of the walk, and uncountably many
  ladders may avoid `α`. (Q-col) is asymptotic, the regime the truncated model has
  inverted three times, so no numeric evidence is offered. After §60, every quantifier
  step in the chain is written out.

- **Set-theory research line, notes §62 — CORRECTION to §61 (eighteenth flip).** (Q-col)
  is settled, against the route. **Lemma W3a [ZFC]**: for every `β₀` there are a finite
  `D` and a `G` with `Col(α,G(α))` uncountable for every `α ∈ β₀\D` — with **no rank, no
  (C2), no `S`**. `ρ₁` is coherent, so `D_β := {α<β₀ : ρ₁(α,β) ≠ ρ₁(α,β₁)}` is finite, and
  a pigeonhole over the countably many finite subsets of the countable `β₀` freezes the
  whole row on an uncountable set. So **Theorem W2's conclusion is a ZFC triviality**: the
  implication is true and the contrapositive can never fire.

  **Salvaged, and stronger than W1: Lemma W3 (double freezing).** Pigeonholing the *pair*
  `(B_β ∩ β₀, D_β)` — countable × countable — gives an uncountable `T∗` on which the trace
  `B_β ∩ β₀` **and** the bar `ρ₁(·,β)↾β₀` are both constant. **Corollary W4**: inside such
  a family (C2) reads as one inequality between two `β`-independent functions and is
  satisfiable outright, so **no frozen family obstructs**. The residual therefore lives in
  the interaction *between* families — a countable amount of exceptional data per level,
  and the first form of the wall that does not mention the rank at all.

  **Method note, a second distinct failure mode.** §60's error was an unwritten quantifier;
  §61's chain was valid and the error was one level up — a consequent treated as a
  refutation target without first asking whether it was a theorem. The guard is different
  and equally cheap: *before relying on a contrapositive, try to prove the consequent.*

  `ρ₁` coherence added to `tools/walk-check.py` (13284 pairs; identity-level content only,
  its unboundedness deliberately not asserted).

- **Set-theory research line, notes §63 — the per-element constraint and the first
  explicit candidate rank.** §62 put the residual in the interaction between frozen
  families; §63 carries that out for a *single element* and gets (C2)'s canonical half in
  final form, with no `β₀`, no family and no down-set in it.

  With `W(A) := {β > α : B_α ∩ B_β = A}` the **coherence fibre** of `(α,A)`, Lemma Z1 says
  exactly: for every `β ∈ W(A)`, either `α` is one of `β`'s finitely many exceptions or
  `rank(α,A) ≥ ρ₁(α,β)`. So the canonical half of (C2) is *dominate `ρ₁(α,·)` on every
  coherence fibre*. That has an obvious least solution —
  `rank(α,A) := sup{ρ₁(α,β) : β ∈ W(A)}` — the **first explicit candidate rank** in the
  program, meeting the canonical half with no exceptions provided the sup is finite. That
  is the scalar question **(Q-fib)**.

  **The determinism form is false**, machine-checked: 1552 multi-member fibres over six
  C-sequences, one of size 239 at `α=12` carrying `ρ₁` values 0 … 11. So the fibre is a
  coarse invariant of the walk, and — applying §62's guard before adopting the target —
  (Q-fib)'s consequent is *not* a triviality. Neither direction is provable by the
  freezing argument: W3 bounds `ρ₁(α,·)` on an uncountable *sub*-fibre only, and the
  measured spread shows sub-fibres are strictly coarser than fibres.

  Stated so the candidate is not over-sold: even granted (Q-fib), the candidate must still
  satisfy **(C1)**, on which nothing here bears — and §58 already showed the two conjuncts
  can pull apart, the natural symmetric-difference rank having (C2)'s shape and failing
  (C1). The wall is now two scalar questions about one explicit function, the smallest it
  has been.

- **Set-theory research line, notes §64 — (Q-fib) is the dividing line.** **Lemma V1
  [ZFC]**: if `sup{ρ₁(α,β) : β ∈ W(A)}` is finite, §63's candidate meets the canonical
  half of (C2) at that element *with no exceptions*; if it is infinite, then **every**
  rank has `α ∈ E_β` for infinitely many `β`, because `rank(α,A)` is a single number. A
  chain-free strengthening of §57's Corollary X2: it names which elements are forced into
  the exceptional sets, and why.

  **A scaling experiment**, run at four model sizes: the widest coherence fibre spans
  `ρ₁`-values `0 … max−1` in *every* model (spreads 5, 11, 13, 15 against model maxima
  6, 12, 14, 16). The fibre constrains the cost hardly at all.

  **Labelled as unreliable, deliberately.** Each row is identity-level and sound; the
  *trend* is not. (Q-fib) is a supremum over an infinite fibre — the asymptotic regime the
  truncated model has inverted three times — and the table's last column is itself the
  kind of growth §58 recorded the model getting backwards at small `N`. So this is
  evidence for **(Q-fib) NO** of exactly the kind that misled §54 and §57, recorded to
  direct the next attempt and not to settle anything.

  Either horn leaves a determinate next step, which is the point of settling the dichotomy
  before the question: **YES** collapses the problem to (C1) for one explicit function;
  **NO** turns (C2) into a scheduling problem for forced exceptions — §58's covering
  reformulation, with the exceptions now identified element by element rather than
  inferred from chains.

- **Set-theory research line, notes §65 — CORRECTION to §63 (nineteenth flip).** Three
  results, the first two prompted by a review of §63–§64.

  **Theorem V2 [ZFC]: the candidate rank is dead**, and not for want of (Q-fib). Every
  `u = (β,C)` has infinitely many level-`α` elements `A := (B_α ∩ C) ∪ {ξ}` with
  `ξ ∈ C \ α`; each is `=∗ B_α` and `⊆ C`, but is **not a subset of `B_α`**, while
  `B_α ∩ B_{β′} ⊆ B_α` for every `β′` — so the fibre is empty and the rank is `sup ∅ = 0`.
  (C1) fails at a single level. This is the *same* flaw §58 recorded for the
  symmetric-difference rank, and §63 asserted "(C1), on which nothing here bears".
  **Third distinct guard**, after §60's and §62's: *before posing a new condition on a
  candidate, check the conditions already known to kill candidates of that shape.*

  **Lemma V3: the two open conditions were one.** Indexing fibres by the defect
  `F := B_α \ A` and writing `n_F := sup{ρ₁(α,β) : β ∈ W_F}`, (Q-fib) is exactly
  *totality* of `F ↦ n_F` and (C1) at level `α` is exactly its *finite-to-one-ness*. So
  the wall is one condition, and the tension is a sentence: (Q-fib) pushes every fibre
  into some bounded stratum, (C1) forbids infinitely many fibres landing in the same one.

  **A fourth limitation of the numeric tool, of a new kind.** The realized defect set is
  the single class `∅` at every level sampled — 4095 of 4096 subsets unrealized at
  `α = 12` — because the model's C-sequences are `⊆`-increasing in range. §54/§57/§58 were
  asymptotic *inversions*; this is a **degeneracy**, the phenomenon having measure zero in
  the model, so there is nothing to get right or wrong. Recorded at the top of
  `tools/walk-check.py`, since it needs the tool rebuilt on a genuinely mod-finite
  sequence rather than a caveat.

  The repaired candidate — a per-level enumeration of defect classes — makes `F ↦ n_F`
  finite-to-one by fiat and preserves (C2)'s canonical half, but a global rank cannot
  carry a per-`u` enumeration, so it lands back inside Corollary Y2's simultaneity
  residual rather than past it. §63–§64 is therefore a closed detour, not a dangling one.

- **Set-theory research line, notes §66 — CORRECTION to §65, and a knock-on to §64
  (twentieth flip).** §65's third claim — that the numeric model cannot see coherence
  defects — is **false**. Defects are everywhere: 13272 of 38367 pairs have
  `B_α \ B_β ≠ ∅` at the standard parameters, across 20 classes.

  **Cause**: the measurement sampled `α ∈ {12,20,28}`, and with `A,M = 6,14` the first two
  decode as `(0,0,12)` and `(0,1,6)` — **successor** ordinals, where `C_x = {x-1}` makes
  the walk trivial and the defect vacuously empty. Two of three samples structurally
  disqualified, no check that they were limits, and the result then stated as a property
  of the tool.

  **Corrected census** at limit levels: one or two realized defect classes per level
  (sizes 0; 0,3; 0,10; 0,18) against `2^{|B_α|}` subsets. Defects are real but **extremely
  thin** — which is exactly the sparsity the review predicted, and it kills the
  *restricted* candidate too: every unrealized class has `n_F = sup ∅ = 0`, so `F ↦ n_F`
  is far from finite-to-one and (C1) fails again, by a second mechanism.

  **Knock-on to §64.** Its scaling table measured the largest `ρ₁`-spread inside a single
  fibre and read it as "the fibre constrains the cost hardly at all". With one or two
  classes per level the widest fibre is essentially all of `(α,ω₁)`, so the finding says
  little beyond "`ρ₁` takes many values". The table stands as data; the interpretation is
  withdrawn. Lemma V1 is a proof and is unaffected.

  **Fourth distinct method note**: §60 write out the quantifiers; §62 try to prove the
  consequent; §65 check the known killers for the shape; §66 **check that the sample
  instantiates the hypothesis**. All four failures were in measurements or their reading,
  none in a proof.

  The false caveat §65 added to the top of `tools/walk-check.py` is replaced by an accurate
  one: defects are visible, they are thin, and sampling must be at limit levels.

- **Set-theory research line, notes §67 — a source pass, and it found a tool.** §62's
  instrument was pinned eleven sections before it was used, so §58–§66 were derived
  without consulting sources and this is the pass. Everything §50–§66 uses about the walk
  is `ρ₁`'s two properties: 1.16(a) rows finite-to-one and 1.16(b) coherence. The same
  Handbook chapter carries four more, for `ρ` (2.1), which **dominates** `ρ₁`:
  **subadditivity** (2.2(b),(c)), finer coherence (2.3), row-injectivity of the stretching
  `ρ̄` (2.5(a)), and eventual monotonicity in the *second* variable (11.9) — the
  coordinate §61 had no handle on.

  **Subadditivity is the relevant one.** §58's residual is simultaneity across overlapping
  down-sets; pigeonhole and freezing fix data on one uncountable set at a time and say
  nothing about how two relate. A triangle inequality on the bars is exactly what
  propagates a bound between them, and `ρ₁` is not known to have one.

  **The substitution is legitimate in one direction**: `ρ ≥ ρ₁` pointwise, so (C2) with the
  `ρ`-bar *implies* (C2) with the `ρ₁`-bar. A construction may target `ρ` and gain the
  inequality. That is a strengthening of the target, not a free lunch, and a negative
  result for `ρ` would say nothing about `ρ₁` — stated explicitly because §59 already got
  a direction backwards once.

  **Raised, not settled**: is `ρ₁` itself subadditive under the program's conditions? No
  counterexample in 90024 triples, which given §66's degeneracies is worth little; a
  refutation test now stands in `tools/walk-check.py`, asserting only that none was found.

  Method note: the sources *were* read — 1.16 was quoted repeatedly from the page carrying
  2.2. The failure is that a derivation run longer than about five sections drifts onto
  the tools it started with. A source pass belongs at that cadence, not at the point of
  being stuck.

- **Set-theory research line, the independence program (notes §40–§52).**
  The terminus decided (§49, sixteenth flip): tree-transport invariance
  retracted at its exact scope (the game's data — deviation sets, value
  comparisons — is value-category, not tree-category; the PFA 0–1 law
  withdrawn), separating the canonical walk sequence ρ₃ from the CH-wild
  trees. Standing picture: Question 1 conjectured **false under MA_ω₁**
  with witness ρ₃ — Todorcevic's `T(ρ₃)` is coherent, nontrivial, and
  Lipschitz in ZFC, so the schedule forcing's ccc is a ZFC question — and
  **open under CH**, where it reduces (§50–§51) to fiber-specialness of
  `D(ρ₃)`: gated by "is `T(ρ₃)` special?" (Theorem J), Tukey-cheap
  (Theorem K: `D(ρ₃) ≡_T [ω₁]^{<ω}` in ZFC). §52 settles one subproblem:
  **Q-rows is false** — successor rows ride their fans
  (`B_{γ+1} = B_γ ∪ {γ}`), every fan's canonical row family is jointly
  absorbed — benignly, since fiber-specialness reduces to limit levels,
  where the absorption game descends to a one-sided domination game for
  the canonical threshold sequence θ(ρ₃) (coherent, finite-to-one,
  ω-valued on fan-tops). Theorem O: Con(CH + `T(ρ₃)` special), so the
  CH-kill needs strictly more than CH. Both ρ₃ sources verified
  first-hand; one in-source typo caught (JIMJ footnote 10).
- **Escapee framework, machine-checked and axiom-free (`EscapeeTheory`
  section).** Theorem I forward (notes §38): `Phi O` — every legal
  constraint system on a directed order has a monotone dominator — follows
  from a monotone dominating retraction (`phi_of_domRetraction`), and the
  three sufficient routes are its instances (`phi_of_top` the ⊤-route,
  `phi_of_join` the bounded-complete/Theorem-H route). Abstract
  (`DirOrder`, `LegalSystem`, `Dominator`, `DomRetraction`) and dependent
  on **no axioms at all** — pure constructive order theory. The converse
  (open uniformization, §39) is deliberately not formalized. The PFA-side
  **forcing bridge** is machine-checked too (`phi_of_generic`, axioms
  `Classical.choice`): a `GenericDom` — the covering, cross-monotone family
  of partial dominators a proper `P(Σ)`'s generic filter provides — yields
  `Φ`; proving `P(Σ)` proper is the open checkpoint and is *not* formalized,
  and the bridge isolates it as the single structure hypothesis. The
  set-theory research line reached the Tukey/cofinal-types frame
  (Todorcevic: 5 types under PFA, `2^{ℵ₁}` under CH) as the correct
  order-theoretic home for the residual (notes §36–§39, fifteen recorded
  verdict flips including two wrong frames caught and corrected).
- **Dip-schedulability skeleton, machine-checked (`DipSchedule` section).**
  Theorem A (trivial ⟹ strongly schedulable) and Lemma F (below-level
  absorption) — two index-agnostic pillars of the set-theoretic
  development — formalized over the `CoherentSeq` abstraction:
  `thmA_leftover_subset`/`thmA_schedulable` (canonical dips route every
  surviving `upDefect` at a top into one finite set) and
  `lemmaF_below_subset`/`lemmaF_below_finite` (the fiber inequality
  `s_x ≤ s_u` transfers through the floors below the element's level;
  the finiteness form is choice-free, `propext, Quot.sound`). These are
  the proved results the open heart (Question 5) rests on; hardening
  them leaves the residual — a `lim¹`-type independence (notes §24–§26)
  — as the only open point. No `sorry`.
- **Set-theory research line (notes §14–§26, problem statement).** The
  qualitative residual driven to a single named question in five
  equivalent forms (wildness cap / finite-row incidence covering /
  finite-fan / profile-diagonal / poset-ccc): Lemma F, Theorems E (the
  game is Φ-complete), F (block-wild cap), G (finite-fan ⟹ coverable);
  the ◊ results C (a non-schedulable coherent sequence) and D (its
  lethal pressure is illegal); and the §22–§26 reductions locating the
  residual as a `lim¹`/derived-limit independence, ccc of the frozen-dip
  realization poset `P(Σ)` against walk oscillation. Eleven recorded
  verdict flips, each argument-forced; the ZFC skeleton is proved, the
  heart handed to set theory in final form.
- **0.1** — first cut: a `Bridge` carrying a certificate, `Bridge.comp`
  accumulating it; existence demonstrated by *composition* of two certified
  bridges (not a single morphism). Zero axioms.
- **0.2 (the eighth catch)** — corrected `Grade` → `GradedAction`: contact with
  mathlib's real `LipschitzWith` revealed that grade and distance are *two*
  types (`ℝ≥0` acting on `ℝ≥0∞`), a conflation the degenerate `Nat` (`M = D`)
  instance had hidden. The first correction delivered by an external object
  rather than internal review.
- field `coeff` → `cert`, and the over-claiming "genus / existence proof"
  framing dropped to "a common interface," once the Hölder instance showed the
  certificate need not be numeric.
- **the qualitative frontier, bracketed** — the non-monotone escapee question
  resolved into: complete lattice ⇒ factors; image-family sups ⇒ factors (and
  are not necessary); non-directed `D` ⇒ escapee (`D3`); directed + finite /
  bounded ⇒ factors; countable cofinality ⇒ factors (cofinal ℕ-ruler,
  cub-monotonized). Residual: uncountable cofinality.
- **the transfinite theorem, proved — "unformalizable" was wrong.** The
  uncountable-cofinality selection, previously called "plausible — unchecked,
  and unformalizable here (transfinite recursion, cardinals)", is now a
  mathlib-free theorem (`prefix_bounded_cofinal_factors`): selection over any
  well-ordered index needs **no limit steps** (`wruler_defeats_bounded_escapee`,
  `Classical.choice` only), and monotonization runs on Lean-core
  `WellFounded.fix` under `PrefixBounded` — `κ`-directedness stated without
  cardinals, weakened to segment-indexed families. `prefixBounded_of_directed`
  proves directedness supplies it at `ω` (re-deriving the countable case);
  uncountably it is not a theorem. The residual is now exactly one hypothesis
  wide: whether `Directed` without `PrefixBounded` admits an escapee.
- **the hunt — two walls proved, no capture.** Candidates die informatively
  (`ω₁ × ℕ` and ideal-of-sets orders are conditionally complete; chain designs
  self-dominate; gap encodings can't force a dominator *under* anything). Wall
  one: `sigma_directed_cofinal_factors` — σ-directedness + an ω₁-like cofinal
  family (`CountableSegments`) forces factorization, so an escapee there must
  contain a countable unbounded family. Wall two: `lists_not_sigma_directed` +
  `lists_bounded_factors` — `List Nat` under membership-inclusion fails
  σ-directedness yet factors everything (filtered bounding list = least upper
  bound), so failing σ-directedness is not sufficient. Residual profile: break
  conditional completeness unovershootably, with only-global failure
  (Aronszajn/gap shape); existence may be independent of ZFC.
- **the coherent-sequence encoding — the profile is realizable, up to set
  theory.** On paper: the fiber order `D_coh(e)` over a nontrivial coherent
  sequence (ZFC, via walks) is directed with finite joins, not σ-directed,
  and join-incomplete (bounded families with *no minimal* upper bound) — the
  first structure passing every wall. The escapee question on it reduces to a
  coherent-sequence uniformization principle (level-monotone bounded coherent
  sequences are provably trivial, so the canonical dominator is obstructed;
  MA/◊-sensitive, plausibly independent of ZFC). Formalized shadow: `Fb`
  (levels ℕ∪{∞}, finite patches over a constant floor) — directed, not
  σ-directed, bounded family with no minimal ub (`fb_no_minimal_ub`,
  choice-free), yet factors via an explicit ladder ruler (`fb_factors`). So
  the dip pathology alone is also non-lethal at countable cofinality; the
  hunt's remaining question lives at ω₁, outside a mathlib-free repo.
- **the ◊-side attempt (`NOTES-coherent-escapee.md`) — canonical dominators
  die; one bridge remains.** Prose rigor: two ZFC lemmas (level-preserving
  systems always factor; representative systems ⇒ everything factors, with
  "trivial ⇒ factors" as corollary) and one ◊ theorem (a coherent sequence
  with *no* representative system — block-diagonal lowering against
  ◊-guessed partial systems). The bridge from rep-death to an escapee did
  not close: pressure needs boundable infinite families, legality makes
  their requirements mod-finite-satisfiable, fibers absorb finite defects,
  and every coherence-extraction from a dominator needs the reps whose
  absence powers the kill. Open core, one sentence: does factors-everything
  imply reps? The note records the legal pressure system `Σ_succ`, the "+1
  trap", the self-obstruction phenomenon, and the two decisive follow-ups.
- **the ◊ theorem collapses to ZFC: reps ⟺ trivial.** Checking whether the
  walk sequences already lack reps answered far more strongly — *every*
  nontrivial coherent sequence lacks representative systems, in ZFC
  (coherence pins pairwise rep-differences finite; level-monotonicity
  concentrates countably many witnesses at one countable level, so movement
  below any α is finite; the escape set has finite initial segments, hence
  bounded; bounded escape trivializes). The ◊ construction is retired as
  unnecessary (kept in the note for the record); "canonical dominators
  exist iff trivial" is a ZFC dichotomy; the independence suspicion
  retreats to non-canonical dominators only; and the Bridge is restated as
  a pure ZFC question over the walks' `ρ₁`. If it holds, the transport
  escapee exists in ZFC.
- **the dip-side attempt — correction, chain-freeness, flipped verdict.**
  `Σ_succ` factors after all (uniform one-level shift dominator) — the
  prior "pressure" claim is retracted; limit-raising systems are legal
  exactly over block-tame sequences, whose tameness builds the dominator
  (absorption pattern, fourth instance). New ZFC theorem: `D_coh(e)` has
  an ω₁-chain with cofinal levels iff `e` is trivial (a chain is a
  club-indexed rep system) — over nontrivial sequences the fiber order is
  provably chain-free, explaining every failed chain-mediated argument.
  Kill schemes close into the legality circle at every entry (per-element
  budgets, countable-union accumulation, slice-illegality under floor
  sabotage). Verdict flipped: evidence now favors ZFC-factoring of all
  fiber orders; the escapee, if anywhere, needs a different species of
  directed order. Missing lemma named: global coordination of per-element
  finite gap-fill corrections.
- **the coordination lemma attempted — residue isolated, verdict
  oscillates.** A ⊑-refining ω₁-recursion with a finite-ledger invariant
  works except at one point; requirement-excess inherits uniformly (ZFC
  lemma — all past `M`-contributions land in one finite set `F_u`); the
  residue is exactly past-floor inversions on gap regions against moving
  targets, with level-overshoot provably useless. Sufficient condition
  named (uniformizing dip system; trivial sequences have one), which
  almost-extracts a rep system (one fiber-control gap). The Bridge is
  squeezed between per-`u` absorption (necessary) and uniform dips
  (sufficient) — one Fodor step and one extraction repair apart. If both
  close: dominator ⇒ trivial, and the escapee exists in ZFC.
- **the Fodor step attempted — the circle proves itself; the core goes
  Aronszajn.** Pressing down is sound; its input is unobtainable: probe
  systems exerting cofinal floor-pressure are legal iff sup-coherence
  already holds (the circle is an equivalence now). New ZFC lemmas:
  single-target dips free; bounded families never obstruct; the
  chain-continuation lemma (dips against a chain's own sup serve every
  continuation — the moving target is fake for chains). But the reduction
  is self-similar under per-element targets; club targets die over the
  ◊-sequence; and §7's "overshoot useless" is corrected — overshooting
  parks values on post-kill floors, making a dominator a `D`-indexed
  rep-like selection whose kill needs chains that chain-freeness forbids.
  Both directions lose their weapon at the last step. Hard core isolated:
  monotone fiber-valued selection with pairwise-finite deviations on the
  chain-free order — Aronszajn-type uniformization. Third flip: lean is
  now independence, one named gap per side.
- **the ◊-side gap attempted — a no-go theorem for the kill template
  (fourth flip).** Kills are structurally thin (coherence: finite below
  every lower level, inherited above), so they never accumulate;
  staggered kills contradict pairwise coherence; committed-value forcing
  needs img-levels cofinal in the kill stage, which legality forbids,
  markers block (infinite markers ∉ fiber), and delayed levels cannot
  reach (coherence caps late deviation at finite). Template no-go: legal
  forcing is bounded-family forcing; bounded families are absorbable;
  kills need unabsorbable forcing — covers all five kill designs tried.
  First one-sided evidence in the arc. Lean, fourth revision:
  ZFC-factoring; the MA-side route re-read as a candidate ZFC proof with
  its missing piece named (forcing-locality).
- **forcing-locality proved; the Bridge becomes a game on `e` alone.**
  The anti-kill (fiberhood-forcing, the one pattern the no-go missed)
  breaks nothing by pairwise coherence — so nothing legal forces values
  above eventual floors. Systems and dominators eliminate: down-sets have
  ⊑-cofinal ω-chains; requirement-sups are legality-bounded; the sole
  residue is floor-baking along chains, finite per pair and fractally
  self-similar across chains. Result: factors-everything(e) ⟺
  dip-schedulable(e), a two-quantifier combinatorial game on the coherent
  sequence alone. The seven-session hunt ends at one line: is every
  dip-schedulable coherent sequence trivial? Handed to set theory in
  final form.
- **`PROBLEM-dip-schedulability.md`** — the standalone problem statement
  for set theorists: definitions from scratch, the strong/weak game, the
  implication diagram with rigor-graded arrows (the strong/weak split and
  the realizability gap presented honestly rather than papered over),
  four numbered questions, four proved ZFC lemmas with proofs, the
  thinness remark (why naive ◊-attacks fail), and the
  independence-boundary discussion. Pure ω₁ combinatorics; no knowledge
  of the program required.
- **the reps theorem machine-checked in shadow.** `reps_implies_trivial`:
  over an abstract index with least witnesses, σ-directedness, and
  countable segments (the three ω₁ properties the proof uses), a coherent
  sequence with a level-monotone representative system is trivial —
  axiom-clean, no sorry, with a mathlib-free pigeonhole and
  totality-from-least-witnesses (axiom-free) as supporting lemmas. Paired
  with the boundary: ℕ fails σ-directedness and the concentration step
  provably fails there (`omega_concentration_fails` — the χ family moves
  at every coordinate). The hunt's engine is now machine-checked, and its
  regularity hypothesis demonstrably load-bearing.
- **Theorem B: uniformizing dip systems ⟺ trivial (ZFC); Question 1′
  proved.** The §7 H-extraction is refuted (wasteful dips hide columns
  below ω-cofinality levels) and replaced by the honest-column argument:
  monotone along honest levels; never-honest points finite per level
  automatically (they sit in `X_γ ∪ U_γ`); unbounded columns killed by
  witness-concentration at one level; the max honest value trivializes,
  sandwiched at a late honest level. Relativizes to cofinal level sets;
  corollary: level-factored strong schedulability ⟹ trivial. Question 1
  of the problem statement is rescoped to element-dependent schedules.
  Phase-0 hygiene: stale Dobrushin claims fixed in transport-calculus
  README; `tools/check-claims.sh` drift guard added.
- **Phase 1 closed; literature first sweep clean.** Lemma E (cofinal
  restriction: schedules push into any cofinal level set via min-above +
  dip absorption; adversaries may attack `ρ₁` on any club). The
  set-based schedule condition has a genuine multiplicity hole (bounds
  leaking coordinates, not values — the recursion can blow up pointwise);
  fixed by the value-form definition, under which strongly-schedulable ⟹
  Φ is written at careful-prose rigor (notes §12) and the diagram arrow
  upgrades. First literature sweep (BLH 1902.02736 §2, Bannister
  2302.07222, derived-limits searches): Definition 2.10 dictionary
  confirmed; BLH's engine is pressing-down, not concentration; Bannister
  is ω^κ/Δ-systems; no uniformization-implies-triviality statement of
  Theorem B's shape found — preliminary no-subsumption verdict, with the
  three named residual reads as the remaining Phase-4 gate.
- **gate cleared; Phase 2 translation layer done.** Second sweep
  (BHL-circle 2411.15856: triviality via cofinality bounds, degenerate at
  ω₁; higher-walks intro 2410.00607: no monotonicity-after-deletions
  machinery, no games; Bannister full HTML: PHₙ is Ramsey/Δ-systems on
  ω^κ, trivialities structural): no subsumption across four probes; one
  footnote — PHₙ's literal statement needs a PDF read of Bannister §5,
  nice-to-have not blocker. Problem statement gains: the Def 2.10
  dictionary with the ω-vs-ℤ remark, the positioning paragraph
  (Theorem B: level-schedules ARE trivializations; Question 1: does
  element-freedom add power), Question 3(b) in H¹-vocabulary with the
  ρ₂ =ᶜ nuance, coherent-tree citations at Lemma D, and a verified
  related-work section. Phase-4 pitch drafted in the notes.

- **§53 — (Q-thr) falls; Theorem B has a downward dual; the dense failure
  mode of the residual dies.** Source round 4 (Handbook 1.16 verbatim — the
  finite-to-one + coherence pair for ρ₁; 1.17 read and recorded as *asserting*
  `T(ρ₁)` special **without proof**, so no analogue may be cited; 3.11's
  nontriviality definition and "coherent + nontrivial ⟹ `T(a)` Aronszajn"; the
  previously-unopened 3.12–3.13, ρ₃ nowhere dense with `ω₁ = ⋃ₙ (Λ+n)` each
  orthogonal to ρ₃ — a free ZFC σ-decomposition of the *index* shaped exactly
  like what fiber-specialness wants of the *fiber order*). **Theorem P: θ(ρ₃)
  is nontrivial in ZFC** — (T2)+(T3) alone, by the classical engine that makes
  ρ₁ nontrivial; §52 had missed it by asking only about implications between
  θ's and ρ₃'s nontriviality, where the direct argument needs neither. So §52's
  descent lands on a coherent **Aronszajn** tree `T(θ)`, not a degenerate
  object. **Theorem B⁻**: downward dip systems (`D⁻(μ,γ) := {ξ < μ : e_μ(ξ) <
  e_γ(ξ)}`) also force triviality — strictly easier than Theorem B (decreasing
  ℕ-values stabilize; no witness-concentration), and the form matched to (M1)'s
  one-sided pruning. **Theorem Q**: combining them, the *dense* failure mode of
  (Q-rows-lim) is impossible in ZFC — joint absorption of the full family of
  limit rows below β, cofinally often, would be a downward dip system for θ and
  trivialize it. Any counterexample is **sparse**; the CH-adversary must select
  rather than absorb uniformly. New named open: **(Q-T-θ)**, is `T(θ)` special.
  Machine-checked alongside: `omega1_finiteToOne_not_trivial` /
  `omega1_finiteToOne_no_reps` (see transport-kernel Tier 5).

- **§54 — going at the central question: the dial made explicit, one route
  closed as vacuous, the index set halved.** Unfolding Handbook 1.4 gives the
  **trace formula** `λ_F(λ,β) = max_i max(C_{β_i} ∩ λ)` over the walk's stops,
  against `ρ₁(λ,β) = max_i |C_{β_i} ∩ λ|` — under (d) the same data read as
  position vs place, so N2's two dials are one object. **Theorem V**: a fan
  above the trace is β-expensive — `ρ₃(μ+n,β) = 0` for every `n ≤ ρ₁(λ,β)`,
  hence `thr_β(μ) ≥ ρ₁(λ,β)+1` (M(3) plus arrival rigidity; `W ≥ 1` is sharp).
  **Corollary V1**: front-loading past the β-cheap region is automatic. **So the
  natural attack — transferring N1/N2 from the moving `thr_α` to the fixed
  `thr_β` — is VACUOUS**, its hypothesis contradicting V; recorded as a closed
  route, with **Corollary V2** the surviving walk-computable criterion (a leak
  needs the inner walks cheaper than the outer one). Under the harmless extra
  normalization (e) `C_{δ+ω} = {δ+n+1}`: **Theorem S** `B_{δ+ω} = B_δ ∪
  [δ,δ+ω)` — Lemma I one level up, fan-tops ride their whole fan (and without
  (e), `ρ₃(δ,δ+ω)=1` iff `|C_{δ+ω} ∩ δ| = 0`, so (e) is exactly what is needed)
  — whence **Theorem T** (those rows are strongly unbounded, by 3.8(2) at n=0)
  and **Theorem U**: **(Q-rows-lim) reduces to limits of limits**, parallel to
  Lemma I′ one level up. New `tools/walk-check.py` re-verifies every walk
  formula on randomized (a),(c),(d),(e)-conforming C-sequences below `ω²·3` —
  the first model in this program with limits *of* limits (§52's stopped below
  `ω·25`): trace formula 972 instances, Theorem V 3108, M(3) 36065, all pass.
  Recorded methodological caveat: a direct numeric probe of (Q-rows-lim) reports
  that most limit rows are absorbed — **an artefact**, since truncation destroys
  the 3.8(2) finiteness that is Theorem T's engine; numeric checks over the
  model are sound for identities and worthless for finiteness phenomena. **The
  central question — is `ρ₃` strongly dip-schedulable under CH — is not
  decided.**

- **§55 — the frames audited; two move.** **Theorem W**: for coherent trees
  *special ⟹ Lipschitz* (Lipschitz-maps Lemma 1.10, an unmarked ZFC iff, plus
  footnote 9). Hence **`T(ρ₁)` is a coherent ZFC-Lipschitz tree** — correcting
  **§46**, whose search for that resource ran ρ₂→ρ₃ and never examined ρ₁. The
  MA-side ccc argument needs only Lipschitz-ness, so it now has two witnesses;
  and Theorem J's necessary gate "`T(e)` special" is **open for `ρ₃`** but
  **passed in ZFC for `ρ₁`**, so `ρ₃` may be dead at the gate while `ρ₁` is not.
  Cost stated: the entire §50–§54 apparatus is ρ₃-specific and does not transfer.
  Caveat: Handbook 1.17 asserts `T(ρ₁)` special without proof, so the ρ₁ line is
  graded accordingly. **PID landscape** (Kuzeljević–Todorcevic, verified
  first-hand): PID is independent of CH and implies SH, but is consistent with a
  non-special Aronszajn tree — so **PID cannot supply the gate**. It can speak
  where MA_{ω₁} cannot (MA contradicts CH, PID does not): PID on the fiber order,
  with the ideal generated by the down-sets, makes alternative (2) *exactly*
  fiber-specialness, reducing the CH-side consistency question to **(Q-PID)** —
  is that ideal a P-ideal in the mod-finite sense? — which is strictly weaker
  than the σ-directedness of `D(e)` that provably fails. Two further frames named
  with first steps (build the witness by recursion under CH/◊; audit whether
  fiber-specialness is actually *sufficient*, §50's unaudited "plausibly"). Also
  recorded: a down-set of `D(e)` meets every single level infinitely often, so no
  level-organised decomposition can be fiber-special. Central question open.

- **§56 — the sufficiency claim audited, and it fails.** §50's load-bearing
  step, "fiber-special ⟹ the block game dies ⟹ `ρ₃` *plausibly* schedules",
  **does not hold as stated**. Writing the diagonal ranking down as an explicit
  dip assignment and computing the leftover `L_u` gives `L_u ∩ (Λ+k)` finite for
  **every k** — the block-localized form of condition (i), strictly weaker than
  (i), which demands `L_u` finite. A leftover spread over infinitely many blocks,
  finitely in each, violates (i) and is invisible to §50's permanent-leak
  mechanism (which needs infinitely many points in *one* block). So the crux is a
  **conjunction**: (C1) fiber-specialness — all §51–§54 narrowed — **and** (C2)
  block-spread control. **Theorem A4** (proved; 9432 instances in
  `tools/walk-check.py`) localizes (C2): an above-trace drop `ξ = μ+n` of `α`
  against `β` has `n ≤ ρ₁(α,β)` or `ρ₁(ξ,α) = 0`, and the latter set is finite by
  Handbook 1.16(a) and foldable into the dips — so above the trace **(C2) ⟺ the
  ranking dominates the walk bars along every down-set**, both sides divergent
  (bars by M3, rank by fiber-specialness). Named **(Q-spread)**; it is once again
  a monotone dominating selection, the program's own signature. **Consequence:
  settling (Q-rows-lim) or (Q-T) affirmatively would not settle schedulability** —
  §51–§54 remain correct mathematics aimed at half the target. Discharged
  positively on the way: for binary-valued `e` the value-form (ii) is
  *equivalent* to the set-form (i), so §50's "modulo the value-form bookkeeping"
  hedge costs nothing over `ρ₃`. Method note recorded: the gap survived four
  sections because "finite in every block" and "finite" read the same in prose —
  every "⟹ plausibly" should be cashed out as an explicit construction before the
  next section builds on it.

- **§57 — (Q-spread) localized, and its level-factored side refuted.**
  Assuming (C1), **(C2) ⟺ the level-minima `m_u(α) := min{rank(x) : x ⊑ u,
  γ(x)=α}` dominate `ρ₁(α,γ(u))` off finitely many levels, for every `u`** — at
  each level all but finitely many elements of `↓u` already outrank any fixed
  bar, so (C1) does most of (C2) for free and the whole content is the minima.
  Down-sets are level-full (`(α, B_α ∩ C) ⊑ (β,C)`), so the reduction bites.
  **Theorem X [ZFC]**: there is **no** `g : ω₁ → ω` with `{α<β : g(α) <
  ρ₁(α,β)}` finite for every `β` — Handbook 1.16(a) plus regularity of ℵ₁, the
  same three lines as `ρ₁`'s nontriviality and Theorem P, now in a third role.
  **Corollary X2**: the domination (C2) requires cannot come from any *level*
  function, so all of (Q-spread) lies in per-element freedom — **Question 1's own
  dichotomy one level down**, with the level-factored side refuted on both sides
  (Theorem B's corollary there, Theorem X here); first time the program's
  self-similarity is proved rather than observed. **Corollary X1**:
  `{α : sup_β ρ₁(α,β) = ∞}` is infinite below every large `β`, so the bars
  diverge in the second argument too — whence a checkable **necessary condition**:
  any (C2)-rank has exceptional sets growing without bound along every
  ⊑-increasing ω-chain, which kills every fixed-`k` block-guarding scheme.
  Second numeric caveat recorded: the truncated model shows `ρ₁(α,·)` eventually
  constant, which would make the whole section vacuous — an artefact, refuted in
  ZFC by Corollary X1, and caught only because the proof was already in hand.

- **The bundle layer: `GradedAction.prod` / `Bridge.pair`.** Five instance
  families inhabit the interface, and the security program added cost budgets —
  but each accumulates *one* certificate, so the interface could not express
  "this artifact is 2-Lipschitz **and** costs at most 40 **and** mediates every
  access". The product supplies it, and the content is that the composition law
  is unchanged: **`Bridge.pair_comp_cert`** proves composing a bundled bridge is
  componentwise composition — no interaction term, no extra hypothesis — so
  carrying `n` guarantees costs `n` independent accumulations and nothing more.
  Non-vacuity is witnessed with two genuinely different monoids on one carrier
  (`bundle_accumulates_componentwise`): a single composition advances an additive
  budget `3 + 4 = 7` and a worst-case bound `max 5 2 = 5` side by side. Axioms:
  `propext` (plus `Quot.sound` where `omega` is used); no `sorry`. **This is the
  first stage of the composable-core work** — the security program is currently
  16 separate toy languages with zero cross-brick composition, and this is the
  algebra the unification needs.

## transport-kernel — mathlib instances

- **Tier 1** — mathlib olean cache stood up (the infra that gates importing
  anything).
- **Tier 2a** — `comp_reconstructs_lipschitz`: the genus receives mathlib's
  `LipschitzWith` and reconstructs `LipschitzWith.comp`.
- **Tier 2b** — `comp_reconstructs_holder`: a *non-scalar* pair certificate
  `(C, r)` with a semidirect-product law; the same `Bridge.comp` reconstructs
  `HolderWith.comp`. Two accumulation algebras, one composition law.
- **Tier 3** — Markov-kernel / Dobrushin (total variation), finite state spaces:
  the data-processing inequality `dpi` proved from scratch (coupling/overlap
  argument — mathlib has no DPI), `Bridge.ofKernel`, and
  `comp_reconstructs_dobrushin`: advanced composition as generic certificate
  accumulation. The quantitative centre, no longer prose.
- **Tier 3b** — the measure-theoretic Dobrushin contraction, arbitrary
  measurable state spaces: `tvDist` (TV distance for measures — absent from
  mathlib) and `tvDist_comp_le`, the DPI for `ProbabilityTheory.Kernel`
  pushforward `κ ∘ₘ μ`, via Hahn decomposition + the coupling argument in
  additive integral form (subtraction-free; no Fubini). Lands in the *same*
  graded action as Lipschitz (`lipGA`), and `Bridge.comp` reproduces
  submultiplicativity (`comp_reconstructs_dobrushin_measure`), also at kernel
  level through mathlib's own `∘ₖ` (`tvDist_kernel_comp_le`). The "finite-state
  only" caveat is discharged.
- **Tier 3c** — the discretization consistency lemma: `Dist.toMeasure` (Dirac
  embedding) with `tvDist_toMeasure` proving the finite `tvd` and the
  measure-theoretic `tvDist` are the same number, `toMeasure_push` matching the
  finite pushforward with `κ ∘ₘ ·`, and `dpi_via_measure` re-deriving the finite
  DPI as a corollary of the measure-theoretic one. The "not yet formally
  linked" caveat is discharged; the two Dobrushin developments provably agree
  where they overlap.
- **Tier 4 recon (Q0) — the quantum slot, gap confirmed.** Physlib
  (leanprover-community, ex Lean-QuantumInfo + PhysLean) inventoried:
  `MState`, `TrDistance` (basic properties only), strong `traceNorm` API,
  first-class PTP-vs-CPTP distinction, Jordan pos/neg parts via cfc, and
  a sandwiched-Rényi DPI — but **no trace-distance contractivity and no
  Dobrushin coefficient**. Same toolchain as this repo (v4.31.0). The
  mathlib-had-no-DPI situation replays one level up; Q1 (PTP-generality
  trace-distance DPI) is a confirmed open slot with all ingredients
  present. Plan Q0–Q5 recorded in `NOTES-quantum-tier4.md`; drift guard
  extended to transport-kernel notes.
- **Tier 4 (Q1+Q2) — the quantum DPI, done and received.**
  `QuantumDobrushinReceive.lean` against Physlib (pinned; mathlib revs
  identical, cache shared): the Jordan form of the trace norm
  (`‖A‖₁ = tr A⁺ + tr A⁻`), the quantum DPI at positive-trace-preserving
  generality (`traceNorm_map_le` — complete positivity not assumed;
  Ruskai), trace-distance contraction for `PTPMap`s on states, the
  quantum Dobrushin bound with the DPI as its η = 1 instance, and the
  reception `Bridge.ofPTPChannel` + `comp_reconstructs_quantum_dobrushin`
  in `dobrushinGA` — the same graded action as the finite classical tier.
  Finite kernels, measure kernels, quantum channels: one composition law.
  Axiom-clean (standard three) against the full Physlib cone — none of
  Physlib's 48 sorries are in it. Q3 (diagonal consistency) and Q4
  (quantum-DP two-row check) remain.
- **Tier 4 complete (Q3–Q5).** Q3: `QuantumDobrushinConsistency.lean` —
  diagonal embedding `Dist.toMState`, `trDistance_toMState` (quantum
  trace distance on diagonals = classical `tvd`), `Kernel.toQChannel`,
  intertwining, and `classical_contraction_via_quantum`; the tower
  closes — finite ↪ measure and finite ↪ quantum, all machine-checked to
  agree; axiom-clean. Q4 (research pass): quantum (ε,δ)-DP is the
  hockey-stick condition; HRSF's sequential composition is a product of
  contraction coefficients — exactly this tier's certificate
  accumulation — but no general adaptive composition theorem and no
  tensorizing f-DP analogue exist: literature gap or genuine interface
  boundary, deliberately left open. Q5 decision: the five DPI-core
  declarations (zero TransportKernel dependencies) are PR-shaped for
  Physlib upstreaming; the Bridge reception stays in-repo.
- **Tier 5 — the reps theorem at actual ω₁ (`OmegaOneCoherent.lean`).**
  `TransportCalculus` added as a lake path dependency; `OmegaOne :=
  ω₁.ToType` (Type 0) models the abstract index: least witnesses from
  well-foundedness, σ-directedness from the regularity of ℵ₁
  (`Ordinal.iSup_lt_of_lt_cof`), countable segments from `#o.ToType =
  o.card` below ℵ₁, no top from countability under successors.
  `finiteP_iff_finite` bridges list-coverage finiteness to `Set.Finite`,
  so the statement reads in standard vocabulary:
  `omega1_reps_implies_trivial` — every coherent sequence on ω₁ with a
  pointwise level-monotone representative system is trivial;
  contrapositive `nontrivial_coherent_no_reps`. To our knowledge the
  first machine-checked theorem about coherent sequences on ω₁. The
  mathlib-free engine and its mathlib model are verified separately and
  compose. Axiom-clean.
- **Tier 5b — the obstruction made unconditional (`omega1_finiteToOne_not_trivial`).**
  `nontrivial_coherent_no_reps` was conditional on an imported negative
  existential — "Todorcevic's walk families are nontrivial" — whose proof is
  precisely the classical finite-to-one argument. That argument is now
  machine-checked at ω₁: `FiniteToOne C := ∀ w n, {u | u < w ∧ C.e w u ≤
  n}.Finite` is Handbook Lemma 1.16(a) verbatim, and
  `omega1_finiteToOne_not_trivial` proves **coherent + finite-to-one rows ⟹
  nontrivial**, via `countable_of_segments_finite` (a segment-finite set of
  countable ordinals is countable because `u ↦ |S ∩ Iio u|` is strictly
  monotone into `ℕ` — order type ≤ ω with no enumeration constructed) and
  `bounded_of_countable` (regularity of ℵ₁, reusing the existing σ-directedness
  instance). Composite: `omega1_finiteToOne_no_reps` — a coherent finite-to-one
  sequence on ω₁ admits **no** monotone representative system, with no cited
  nontriviality. What remains cited is only the positive,
  computation-checkable existence of such a sequence (Handbook 1.16(a)+(b) for
  ρ₁); the Lean statement is an implication, so non-vacuity still rests on
  that. Axiom-clean (standard three), no `sorry`. Set-theoretic side: notes §53
  (Theorem P).
- **Tier 5c — Theorem B⁻ machine-checked (`omega1_downDip_iff_trivial`).** The
  program's first formal *dip* theorem: `DownDip C` bundles finite per-level
  corrections whose leftover is finite at every top, and the equivalence says
  such a system exists **iff** the sequence is trivial. Substantive direction
  `omega1_downDip_trivial` follows the §53 prose step for step —
  `honest_antitone`, `bad_finite` (regularity of ℵ₁ concentrating countably many
  bounds), `eval_eq_of_honest` (stabilization by `sInf` leastness plus
  antitonicity) — with `DownDip.ofTrivial` the converse, which also settles
  non-vacuity. This matters because notes §53's **Theorem Q** (the kill of
  (Q-rows-lim)'s dense failure mode) depends on B⁻: that kill now rests on a
  formal theorem plus Theorem P rather than two fresh prose arguments. The
  *upward* Theorem B stays careful-prose — its witness-concentration step for
  unbounded columns is exactly the part the downward dual avoids. Axiom-clean,
  no `sorry`.

## Consolidation

- Merged the three previously-separate repos into this monorepo with a top-level
  README and CHANGELOG. Aligned the `cert` field name and the framing across
  `transport-calculus` and `transport-kernel` (the two had drifted —
  `coeff`/`cert` and stale "genus" language — while developed separately).
