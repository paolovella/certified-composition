# Changelog — certified composition

Top-level arc across the three sub-projects. Each subdir keeps its own detailed
`CHANGELOG.md`; this traces the line of work as a whole. Dates are when the work
landed.

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
  names the discrepancy as the resource a construction must spend. First time this
  program's residual has reduced to a property of the sequence itself.

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
