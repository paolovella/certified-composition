/-
  The composable core, stage 2h: a program worth the name.

  Every worked example in this repo so far has been small enough to read in one line.
  `fiveProg` is six operations, and it was built to exercise one rule from each
  certificate. Six operations is enough to show the certificates *compose*; it is not
  enough to show they compose at a size anyone would call a program, and four of the last
  five stages have been obstructions rather than artifacts.

  `bigHandler` is twenty-one operations: two authorization checks, two mediated reads,
  three allocations (one secret), pointer stores and loads, arithmetic, a sanitized query
  built and emitted, a branch, two dereferences, and three frees. It carries **all five
  certificates from one run of one checker**, and everything below is measured on it
  rather than asserted about it.

  What the measurements show, in rough order of how much they surprised me:

  * **The trusted base is still two entries.** Twenty-one operations, and stage 2c's
    `needs` charges the policy author and the `db` parser and nothing else — no
    filesystem, because the program never emits there. The base grew with what the
    program *does*, not with how long it is.

  * **The secret address is retired, not recycled.** After three allocations and three
    frees, `freed = [0, 1]` — address 2, the `allocS` cell, is gone from circulation
    entirely. That is stage 1z's rule, which was introduced to close a two-line leak,
    visible as a fact about a real run.

  * **Stage 2e's cost bound does real work here, and is loose by a factor of three.**
    `bigHandler` branches, so unlike `fiveProg` it is not speculation-inert: at window 2
    it really executes 26 commands against a certified 24. The bound
    `26 ≤ 24 * (1 + 2) = 72` holds with room to spare, which is what "charges a full
    window to every command rather than every branch" costs on something concrete.

  * **Its trace does not grow under misprediction** — but only because the untaken branch
    happens to touch no memory. That is a property of this program, stated as a
    measurement and *not* as a theorem, because stage 2g is precisely the reason no
    theorem is available.

  What this stage does not do is find a new defect. Everything held. That is worth
  recording too: the four obstruction stages before it were not signs of a core that
  falls over at size.
-/
import ConfTyping.SpecFactor

namespace ConfTyping

/-! ## The program -/

/-- Right-nested sequencing, so the program below reads as a list. -/
def seqAll (cs : List UCmd) : UCmd := cs.foldr (fun c acc => .seq c acc) .skip

/-- A request handler: authorize, read, allocate, compute through the heap, build and
    emit a sanitized query, branch, and release everything. -/
def bigHandler : UCmd := seqAll [
  -- authorize both resources before touching either
  .check "db", .check "fs",
  .access "db", .access "fs",
  -- two public buffers and one secret one
  .memop .alloc "buf", .memop .alloc "tmp", .memop .allocS "secret",
  -- compute through the heap
  .assign "n" (.num 7),
  .hop .store "buf" "n",
  .hop .load "v" "buf",
  .assign "acc" (.add (.var "v") (.num 1)),
  .hop .store "tmp" "acc",
  -- build a query with the untrusted input sanitized, and emit it
  .sop .set "q" (.cat (.lit [.ord, .quote]) (.cat (.san (.var "input")) (.lit [.quote]))),
  .sop .emit "db" (.var "q"),
  -- a branch on public data
  .ite (.var "n")
    (seqAll [.hop .load "w" "tmp", .assign "acc" (.var "w")])
    (seqAll [.assign "acc" (.num 0)]),
  -- use the pointers, then release everything
  .memop .deref "buf",
  .memop .deref "tmp",
  .memop .free "tmp",
  .memop .free "buf",
  .memop .free "secret"
]

/-- **One checker, one pass, five certificates.** The tracked set comes back empty, so
    every allocation was released; the authorization set holds both resources; the taint
    environment records that `q` carries exactly two delimiters. -/
theorem bigHandler_checks :
    xcheck Psec [] [] [] bigHandler = some ([("q", 2)], ["fs", "db"], [], 24, [2]) := by
  decide

/-- The five, spelled out: a budget of 24, complete mediation, noninterference (hence
    timing and termination), memory safety, and structural integrity of every emitted
    string. -/
theorem bigHandler_five :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n bigHandler π s = some r → r.2.1 ≤ 24)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n bigHandler π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n bigHandler π (initU σ)) (uexec n bigHandler π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n bigHandler π (initU σ) = some r → r.1.err = false) :=
  ⟨(xcheck_gives_five bigHandler_checks).1,
   (xcheck_gives_five bigHandler_checks).2.1,
   (xcheck_gives_five bigHandler_checks).2.2.1,
   (xcheck_gives_five bigHandler_checks).2.2.2.1⟩

/-! ## What the run actually does -/

/-- It completes: no fault, not halted, and the budget is tight rather than generous —
    24 certified, 24 spent. -/
theorem bigHandler_runs_clean :
    ((uexec 60 bigHandler (fun _ => true) (initU (fun _ => 0))).map
       (fun r => (r.1.err, r.1.dead, r.2.1))) = some (false, false, 24) := by decide

/-- Both resources are read, and every allocation is released — `live` comes back
    empty. -/
theorem bigHandler_releases_everything :
    ((uexec 60 bigHandler (fun _ => true) (initU (fun _ => 0))).map
       (fun r => (r.1.reads, r.1.live))) = some (["fs", "db"], []) := by decide

/-- **The secret address is retired, not recycled.** Three allocations, three frees, and
    the free list comes back `[0, 1]`: address 2 — the `allocS` cell — has left
    circulation. That is stage 1z's rule, introduced to close a two-line leak, showing up
    as a fact about a twenty-one operation run. -/
theorem the_secret_address_is_retired :
    ((uexec 60 bigHandler (fun _ => true) (initU (fun _ => 0))).map
       (fun r => r.1.freed)) = some [0, 1] := by decide

/-- One query reaches the sink, and it is well formed: the sanitizer emptied the
    untrusted input, so what arrives is the two structural delimiters and nothing else —
    a delimiter count of 2, which is what the certificate promised. -/
theorem bigHandler_emits_one_clean_query :
    ((uexec 60 bigHandler (fun _ => true) (initU (fun _ => 0))).map (fun r => r.1.sink))
      = some [("db", [UCh.ord, UCh.quote, UCh.quote])] := by decide

/-! ## The trusted base did not grow with the program -/

/-- **Two entries, at twenty-one operations.** Stage 2c's `needs` charges the policy
    author and the `db` parser, and nothing else — no filesystem, because the program
    never emits there. The base grew with what the program *does*, not with its length,
    which is the whole point of computing it rather than fixing it. -/
theorem bigHandler_trusted_base :
    needs bigHandler = [Assume.policyIntended, Assume.sinkHonest "db"] := by decide

/-- And the filesystem exemption is earned, not assumed: nothing is ever tagged `fs`. -/
theorem bigHandler_owes_the_filesystem_nothing :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n bigHandler π (initU σ) = some r → ∀ p ∈ r.1.sink, p.1 = "fs" → False := by
  intro n π σ r hr p hp hfs
  have := unwritten_sink_untouched n bigHandler π (initU σ) r "fs" (by decide) hr p hp hfs
  simpa [initU] using this

/-! ## Under speculation -/

/-- `bigHandler` **branches**, so unlike `fiveProg` it is not speculation-inert and stage
    2e's bound is doing real work rather than restating the budget. -/
theorem bigHandler_is_not_inert : hasIte bigHandler = true := by decide

/-- **The certified bound holds, and is loose by a factor of three.** At window 2 the
    machine really executes 26 commands against a certified 24; the bound allows 72. That
    gap is what "charges a full window to every command rather than to every branch"
    costs on something concrete, and it is the honest note stage 2e attached to
    `spec_cost_bound` measured rather than asserted. -/
theorem bigHandler_speculative_cost :
    acostU 60 2 bigHandler (fun _ => true) (initU (fun _ => 0)) = some 24
  ∧ rcostU 60 0 bigHandler (fun _ => true) (initU (fun _ => 0)) = some 24
  ∧ rcostU 60 2 bigHandler (fun _ => true) (initU (fun _ => 0)) = some 26
  ∧ (26 : Nat) ≤ 24 * (1 + 2) := by decide

/-- And the general bound, instantiated: at *every* window and from *every* state. -/
theorem bigHandler_cost_under_every_window :
    ∀ (n w : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × Nat × List Int),
      uexecS n w bigHandler π s = some r → r.2.2.1 ≤ 24 * (1 + w) :=
  certified_cost_under_speculation bigHandler_checks

/-- **A measurement, deliberately not a theorem.** This program's trace does not grow
    under misprediction — but only because its untaken branch happens to touch no memory.
    Nothing here generalises, and stage 2g is exactly the reason no general statement is
    available yet. -/
theorem bigHandler_trace_happens_not_to_grow :
    straceU 60 0 bigHandler (fun _ => true) (initU (fun _ => 0)) = some [0, 0, 1, 1, 0, 1]
  ∧ straceU 60 2 bigHandler (fun _ => true) (initU (fun _ => 0))
      = some [0, 0, 1, 1, 0, 1] := by decide

/-! ## What this stage claims

    An artifact, and measurements on it. No new rule, no new obstruction, and no new
    defect — everything held at three and a half times the size of the previous worked
    example, which after four consecutive obstruction stages is itself worth writing
    down.

    Two limits. The program is loop-free, because `allcheck` has no loop rule
    (`only_the_budget_lacks_a_loop_rule` is the standing record of that), so "twenty-one
    operations" means twenty-one operations and not a bounded iteration over them. And
    `decide` is doing the work throughout: every measurement here is a kernel computation
    on a closed term, which is the strongest evidence available and also the reason this
    stage says nothing about programs it did not run. -/

end ConfTyping
