/-
  The composable core, stage 1p: the sink becomes observable, and one program carries
  five certificates.

  Stage 1o added strings and a structural-integrity certificate, and left the sink
  **outside** the noninterference observation. That was a real weakness rather than a
  scoping choice: a sink is an *output channel*, so leaving it unobserved made every
  string operation trivially noninterferent and the guarantee weaker than it looked. A
  program could emit a secret and still be "noninterferent".

  Stage 1p puts it in. `uLowEqA` gains the Low part of the string store and the sink,
  `JSecTy` gains three rules — `setH` (writing a High string variable is invisible),
  `setL` and `emit` (both need a Low value, via `sexprLow`) — and `jsecTy_sound` threads
  the two new conjuncts through every case. `emit_of_secret_rejected` is the leak that
  is now caught.

  **`sexprLow` does not treat `san` as declassification**, and that is the security
  decision of this stage. Sanitising removes *delimiters*, not *secrets*. Getting it
  backwards would be a real vulnerability dressed as a discharge, so it is worth having
  a theorem: `sanitising_does_not_declassify` shows the structural checker accepts
  `emit (san secret)` — it is perfectly well-formed as a query — while the
  noninterference checker refuses it. The two certificates catch different things, and
  that is exactly why the bundle carries both.

  Then the merge. `xcheck` runs the two checkers and pairs the results.
  **The fifth certificate does factor**, unlike the third: stage 1j found that
  noninterference and memory safety could not be established separately and conjoined,
  but structural integrity and the other four *can*, because the conditions an `emit`
  must satisfy — a known delimiter count, and a Low value — are about different parts of
  the state. So `xcheck` is a pairing and not a new judgment, and `factoring_holds_here`
  records the contrast with `ni_and_memory_do_not_factor` so the two are not confused.

  `fiveProg` is the result: check a permission, allocate, read the mediated resource,
  build a sanitised query, emit it, free. Five certificates — budget (tight, 6),
  mediation, noninterference, memory safety, structural integrity — from two checkers
  and one program.
-/
import ConfTyping.TaintCert

namespace ConfTyping

/-! ## Running both checkers -/

/-- The whole composable core in one call. It is a *pairing*, deliberately: see
    `factoring_holds_here`. -/
def xcheck (P : Partition) (C : TaintEnv) (A V : List String) (c : UCmd) :
    Option (TaintEnv × List String × List String × Nat × List Nat) :=
  match allcheck P A V c, tcheck C c with
  | some (A', V', k), some (C', Ks) => some (C', A', V', k, Ks)
  | _, _ => none

/-- **Five certificates from one program.** The budget, mediation, noninterference
    (hence timing and termination, since the clock and the halting bit are in the
    observation — and now the sink too), memory safety, and structural integrity of
    every emitted string. -/
theorem xcheck_gives_five {P : Partition} {c : UCmd}
    {C' : TaintEnv} {A' V' : List String} {k : Nat} {Ks : List Nat}
    (h : xcheck P [] [] [] c = some (C', A', V', k, Ks)) :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n c π s = some r → r.2.1 ≤ k)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ Ks) := by
  simp only [xcheck] at h
  rcases ea : allcheck P [] [] c with _ | p
  · rw [ea] at h; simp at h
  · rcases et : tcheck [] c with _ | q
    · rw [ea, et] at h; simp at h
    · rw [ea, et] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨hb, hm, hn, hs⟩ := allcheck_gives_four (by rw [ea])
      exact ⟨hb, hm, hn, hs, tcheck_no_injection (by rw [et])⟩

/-! ## The sink is observed now -/

/-- **The leak stage 1o could not see.** Emitting a secret is refused: the sink is an
    output channel, so its contents must be Low. Before stage 1p this program was
    "noninterferent" because nothing looked at the sink. -/
theorem emit_of_secret_rejected :
    allcheck Psec [] [] (.sop .emit "db" (.var "secret")) = none := by decide

/-- **Sanitising is not declassification**, and the two certificates disagree about
    this program on purpose. `emit (san secret)` is *structurally* perfect — the
    delimiter count is zero, so it cannot break a query — and it still leaks the
    secret. The taint checker accepts it; the noninterference checker refuses it.
    Neither is wrong; they are answering different questions, which is the argument for
    carrying both. -/
theorem sanitising_does_not_declassify :
    tcheck [] (.sop .emit "db" (.san (.var "secret"))) = some ([], [0])
  ∧ allcheck Psec [] [] (.sop .emit "db" (.san (.var "secret"))) = none := by decide

/-- Writing a secret into a *High* string variable is fine — nothing observable
    changes — so the rule refuses emission, not computation. -/
theorem high_string_assignment_is_fine :
    allcheck Psec [] [] (.sop .set "secret" (.var "secret")) = some ([], [], 1) := by
  decide

/-! ## The fifth certificate factors — unlike the third -/

/-- **A contrast worth stating.** Stage 1j found that noninterference and memory safety
    *cannot* be established separately and conjoined: the NI rule for `deref` needs the
    memory invariant, so the judgment had to be indexed by the tracked set. Structural
    integrity is not like that. The two conditions an `emit` must meet — a known
    delimiter count, and a Low value — constrain different parts of the state, so
    running the checkers separately and pairing the results is sound, and `xcheck` is a
    pairing rather than a sixth judgment.

    The point of recording both is that "these compose" is not a default one may assume:
    it held four times, failed once, and holds again here — each time for a reason. -/
theorem factoring_holds_here (P : Partition) (C : TaintEnv) (A V : List String)
    (c : UCmd) (C' A' V' : _) (k : Nat) (Ks : List Nat) :
    xcheck P C A V c = some (C', A', V', k, Ks) ↔
      (allcheck P A V c = some (A', V', k) ∧ tcheck C c = some (C', Ks)) := by
  constructor
  · intro h
    simp only [xcheck] at h
    rcases ea : allcheck P A V c with _ | p
    · rw [ea] at h; simp at h
    · rcases et : tcheck C c with _ | q
      · rw [ea, et] at h; simp at h
      · rw [ea, et] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
  · intro ⟨ha, ht⟩
    simp only [xcheck, ha, ht]

/-! ## The artifact -/

/-- Check a permission, allocate a buffer, read the mediated resource, build a
    sanitised query, emit it, release the buffer. -/
def fiveProg : UCmd :=
  .seq (.check "db")
   (.seq (.memop .alloc "buf")
    (.seq (.access "db")
     (.seq (.sop .set "q" (.cat (.lit [.ord, .quote])
                            (.cat (.san (.var "input")) (.lit [.quote]))))
      (.seq (.sop .emit "db" (.var "q")) (.memop .free "buf")))))

theorem fiveProg_checks :
    xcheck Psec [] [] [] fiveProg = some ([("q", 2)], ["db"], [], 6, [2]) := by decide

/-- **One program, five certificates.** -/
theorem fiveProg_five :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n fiveProg π s = some r → r.2.1 ≤ 6)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n fiveProg π (initU σ)) (uexec n fiveProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r → r.1.err = false)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n fiveProg π (initU σ) = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ [2]) :=
  xcheck_gives_five fiveProg_checks

/-- And it runs: nothing faults, nothing is refused, exactly the mediated resource is
    read, the buffer is released, the emitted query has its two delimiters, and the
    budget is **tight** — certified six, spends six. -/
theorem fiveProg_runs :
    ((uexec 15 fiveProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.dead, r.1.reads, r.1.live))) = some (false, false, ["db"], [])
  ∧ ((uexec 15 fiveProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.sink.map (fun p => qcount p.2), r.2.1))) = some ([2], 6) := by
  constructor
  · decide
  · decide

/-! ## What is left

    The composable core now carries five certificates on the loop-free fragment. Three
    things remain, all named rather than implied.

    * **Loops.** Noninterference, memory safety and mediation compose over loops; the
      budget cannot (`only_the_budget_lacks_a_loop_rule`, stage 1n) and structural
      integrity has no loop rule yet (the count environment needs stage 1l's narrowing —
      mechanical, but a stage of its own).
    * **Path traversal**, row 14. Now expressible — it is the same shape with a path
      separator in place of the delimiter — and not written.
    * **The ledger.** Stage 1e's `UCertL` lifts any of these relative to a trusted base;
      it is not threaded through `xcheck`, so a program's assumptions are still tracked
      by hand. -/

end ConfTyping
