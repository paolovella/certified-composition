/-
  The composable core, stage 2d: speculation on the unified machine.

  Brick 33 put Spectre in the semantics on its own small language and closed row 9 of
  `VULN-COVERAGE.md`. It has never been brought onto `UCmd`, which leaves the repo
  awkwardly placed: the *core* carries five certificates and says nothing about
  transient execution, while the result that says something about transient execution
  lives on a language with no certificates at all.

  Following the stage-2a template — for a change that touches the observation, find the
  obstruction before building the proof — this stage brings the machine over and asks
  what the five certificates do and do not survive. **The answer was not the one this
  stage set out to write down**, and that is worth stating plainly: the plan was to
  exhibit a certified program that leaks, and no such program could be constructed.

  **The machine.** `uexecS` is `uexec` with two additions: an **address trace**
  recording every heap cell touched, and **misprediction** — at an `ite` the untaken
  branch also runs, for a window of `w` commands, with its state discarded and its trace
  kept. Rolled-back state, surviving trace: that asymmetry is the whole of Spectre and
  the whole of this model. `spec_is_uexec_extended` proves the extension faithful — at
  `w = 0` the state and the cost are `uexec`'s — so nothing below is an artifact of a
  different machine having been substituted.

  **The machine can express the leak.** `victimU_leaks`: the textbook gadget, two heaps
  differing in one cell, two different traces, while `architecturally_indistinguishable_U`
  gives identical architectural traces. The model is not vacuous.

  **But the core already rejects it, via rules written for other reasons.**

  * `gadget_rejected_by_memory_safety` — `slcheck`'s load rule requires the *source* to
    be a tracked pointer and **drops the destination** from the tracked set, so a loaded
    value can never afterwards be dereferenced. The value-to-address flow that is the
    gadget has no derivation. That rule is stage 1i's linearity discipline, written long
    before speculation was in view.
  * `secret_guard_rejected` — a branch on a secret is refused by the joint checker, so
    *which* branch mispredicts cannot depend on a secret either. Memory safety alone
    would have allowed it; the flow certificate is what refuses.
  * `no_pointer_arithmetic_here` — and the bounds-check-bypass half of Spectre-v1 has no
    analogue at all, since addresses are produced by `alloc` and copied, never computed.
    An absence in the model, recorded so it does not read as a result.

  **What is not closed.** Two exclusions and an absence are not a theorem. The five
  certificates are statements about `UState`; the trace is not in `UState`; so nothing
  here proves a certified program's trace is secret-independent. The conjecture is
  stated in the body so it can be attacked rather than assumed.

  **What is genuinely broken.** `transient_work_is_off_the_budget`, on a program the
  core *does* certify: the bound is 2, the machine reports 2 at every window, and at
  window 1 a third command really ran. Stage 1n found the budget would not compose over
  loops; stage 2a found it was the one law that did compose over threads. It fails here
  in a third and different way — not wrong about what it counts, but counting the wrong
  thing.

  **The positive.** `branch_free_is_inert`: with no `ite`, `uexecS` is independent of
  `w` — trace and real cost included — so the machine is literally unchanged by
  speculation. That covers the worked program (`fiveProg_is_speculatively_inert`). Stage
  2e supersedes the *architectural* half of this for all programs: rollback is complete,
  so the state agrees at every window whether or not the program branches. What stays
  special about branch-free programs is that their trace and real cost agree too.

  **Scoping, stated rather than implied.** One global window applies at every branch
  rather than brick 33's per-branch schedule; that is a *stronger* attacker, so it
  weakens nothing here, and brick 33 keeps the finer model. Loop guards are always
  predicted correctly. The microarchitectural state is an address trace — no cache
  lines, no eviction, no timing, no contention. Only conditional-branch misprediction is
  modelled. No fence rule is proved on `UCmd`: brick 33 has one on its own language, and
  porting it is named as the follow-on rather than claimed here.
-/
import ConfTyping.Assumptions

namespace ConfTyping

/-! ## The trace, and the transient window -/

/-- The heap cells a single command touches. Recorded **regardless of liveness**: a
    transient access to a dangling address still moves the address through the machine,
    which is the entire reason a trace is not part of `UState`. -/
def touched : UCmd → UState → List Int
  | .memop .deref x, s => [s.store x]
  | .hop .load _ y,  s => [s.store y]
  | .hop .store x _, s => [s.store x]
  | _,               _ => []

/-- Flatten a command into its sequence of steps. `seq` is transparent; everything else,
    including a nested `ite` or `loop`, is one step — nested speculation is out of scope
    by the syntax rather than silently ignored by the semantics. -/
def flatten : UCmd → List UCmd
  | .seq c₁ c₂ => flatten c₁ ++ flatten c₂
  | c          => [c]

/-- Run a transient window: at most `w` commands, keeping only the trace. State is
    threaded so that a load's *value* can become the next load's *address* — that flow
    is the gadget — but the state itself is discarded on rollback. -/
def transRun : Nat → List UCmd → MedPolicy → UState → List Int
  | 0,     _,       _, _ => []
  | _ + 1, [],      _, _ => []
  | w + 1, c :: cs, π, s =>
      touched c s ++ (match uexec 30 c π s with
                      | none   => []
                      | some r => transRun w cs π r.1)

/-- How many commands the transient window actually ran. `transRun` records what they
    touched; this records that they ran at all, which is the thing the budget misses. -/
def transSteps : Nat → List UCmd → MedPolicy → UState → Nat
  | 0,     _,       _, _ => 0
  | _ + 1, [],      _, _ => 0
  | w + 1, c :: cs, π, s =>
      1 + (match uexec 30 c π s with
           | none   => 0
           | some r => transSteps w cs π r.1)

/-- A transient window runs at most `w` commands. -/
theorem transSteps_le : ∀ (w : Nat) (cs : List UCmd) (π : MedPolicy) (s : UState),
    transSteps w cs π s ≤ w
  | 0,     _,       _, _ => Nat.le_refl 0
  | _ + 1, [],      _, _ => Nat.zero_le _
  | w + 1, c :: cs, π, s => by
      show 1 + (match uexec 30 c π s with
                | none => 0
                | some r => transSteps w cs π r.1) ≤ w + 1
      rcases e : uexec 30 c π s with _ | r
      · simp only [e]; omega
      · simp only [e]
        have := transSteps_le w cs π r.1
        omega

/-! ## The machine -/

/-- `uexec` with an address trace and misprediction. At an `ite` the untaken branch runs
    for `w` commands with its state discarded and its trace kept. Cost is the
    architectural cost: transient commands are deliberately *not* counted, which is
    itself one of the findings below. -/
def uexecS : Nat → Nat → UCmd → MedPolicy → UState →
    Option (UState × Nat × Nat × List Int)
  | 0,     _, _, _, _ => none
  | n + 1, w, c, π, s =>
      match c with
      | .seq c₁ c₂ =>
          (uexecS n w c₁ π s).bind fun r₁ =>
            (uexecS n w c₂ π r₁.1).map fun r₂ =>
              (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2.1 + r₂.2.2.1, r₁.2.2.2 ++ r₂.2.2.2)
      | .ite e c₁ c₂ =>
          if evalE e s.store ≠ 0 then
            (uexecS n w c₁ π s).map fun r =>
              (r.1, 1 + r.2.1, 1 + transSteps w (flatten c₂) π s + r.2.2.1,
               transRun w (flatten c₂) π s ++ r.2.2.2)
          else
            (uexecS n w c₂ π s).map fun r =>
              (r.1, 1 + r.2.1, 1 + transSteps w (flatten c₁) π s + r.2.2.1,
               transRun w (flatten c₁) π s ++ r.2.2.2)
      | .loop e c₀ =>
          if evalE e s.store ≠ 0 then
            (uexecS n w c₀ π s).bind fun r₁ =>
              (uexecS n w (.loop e c₀) π r₁.1).map fun r₂ =>
                (r₂.1, 1 + r₁.2.1 + r₂.2.1, 1 + r₁.2.2.1 + r₂.2.2.1,
                 r₁.2.2.2 ++ r₂.2.2.2)
          else some (s, 1, 1, [])
      | c => (uexec 1 c π s).map fun r => (r.1, r.2.1, r.2.1, touched c s)

/-- The speculative trace, which is what an attacker sees. -/
def straceU (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState) : Option (List Int) :=
  (uexecS n w c π s).map (fun r => r.2.2.2)

/-- The **architectural** cost: what the certificate bounds. -/
def acostU (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState) : Option Nat :=
  (uexecS n w c π s).map (fun r => r.2.1)

/-- The **real** cost: architectural commands plus every transient one. -/
def rcostU (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState) : Option Nat :=
  (uexecS n w c π s).map (fun r => r.2.2.1)

/-- Unfolding lemmas, so proofs elsewhere need not restate the machine. -/
theorem uexecS_ite_eq (n w : Nat) (e : Expr) (c₁ c₂ : UCmd) (π : MedPolicy) (s : UState) :
    uexecS (n + 1) w (.ite e c₁ c₂) π s
      = (if evalE e s.store ≠ 0 then
           (uexecS n w c₁ π s).map fun r =>
             (r.1, 1 + r.2.1, 1 + transSteps w (flatten c₂) π s + r.2.2.1,
              transRun w (flatten c₂) π s ++ r.2.2.2)
         else
           (uexecS n w c₂ π s).map fun r =>
             (r.1, 1 + r.2.1, 1 + transSteps w (flatten c₁) π s + r.2.2.1,
              transRun w (flatten c₁) π s ++ r.2.2.2)) := rfl

theorem uexecS_loop_eq (n w : Nat) (e : Expr) (c₀ : UCmd) (π : MedPolicy) (s : UState) :
    uexecS (n + 1) w (.loop e c₀) π s
      = (if evalE e s.store ≠ 0 then
           (uexecS n w c₀ π s).bind fun r₁ =>
             (uexecS n w (.loop e c₀) π r₁.1).map fun r₂ =>
               (r₂.1, 1 + r₁.2.1 + r₂.2.1, 1 + r₁.2.2.1 + r₂.2.2.1,
                r₁.2.2.2 ++ r₂.2.2.2)
         else some (s, 1, 1, [])) := rfl

/-! ## The extension is faithful -/

/-- **This is `uexec`, on state and architectural cost, at every window.** Not merely at
    `w = 0`: the transient parts live entirely in the two components this projection
    drops, so nothing below is an artifact of a different machine having been
    substituted, and the agreement is not conditional on there being no misprediction.

    That is a stronger statement than stage 2d needed and it is what stage 2e builds on:
    the state half is completeness of rollback, the cost half says the *architectural*
    cost is window-free — which is exactly why the budget failed to notice the transient
    work. -/
theorem spec_is_uexec_extended : ∀ (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState),
    (uexecS n w c π s).map (fun r => (r.1, r.2.1))
      = (uexec n c π s).map (fun r => (r.1, r.2.1))
  | 0,     _, _, _, _ => rfl
  | n + 1, w, c, π, s => by
      cases c with
      | skip => rfl
      | assign _ _ => rfl
      | check _ => rfl
      | access _ => rfl
      | memop _ _ => rfl
      | sop _ _ _ => rfl
      | hop _ _ _ => rfl
      | seq c₁ c₂ =>
          show (Option.map _ ((uexecS n w c₁ π s).bind _)) = (Option.map _ ((uexec n c₁ π s).bind _))
          have h₁ := spec_is_uexec_extended n w c₁ π s
          rcases e₁ : uexecS n w c₁ π s with _ | ⟨s₁, k₁, t₁⟩ <;> rw [e₁] at h₁
          · rcases e₁' : uexec n c₁ π s with _ | r₁' <;> rw [e₁'] at h₁
            · rfl
            · simp at h₁
          · rcases e₁' : uexec n c₁ π s with _ | ⟨s₁', k₁', t₁'⟩ <;> rw [e₁'] at h₁
            · simp at h₁
            · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁
              obtain ⟨hst, hk⟩ := h₁
              subst hst; subst hk
              simp only [Option.bind_some]
              have h₂ := spec_is_uexec_extended n w c₂ π s₁
              rcases e₂ : uexecS n w c₂ π s₁ with _ | ⟨s₂, k₂, t₂⟩ <;> rw [e₂] at h₂
              · rcases e₂' : uexec n c₂ π s₁ with _ | r₂' <;> rw [e₂'] at h₂
                · rfl
                · simp at h₂
              · rcases e₂' : uexec n c₂ π s₁ with _ | ⟨s₂', k₂', t₂'⟩ <;> rw [e₂'] at h₂
                · simp at h₂
                · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₂
                  obtain ⟨hst2, hk2⟩ := h₂
                  subst hst2; subst hk2
                  rfl
      | ite e c₁ c₂ =>
          by_cases hg : evalE e s.store ≠ 0
          · show (Option.map _ (if _ then (uexecS n w c₁ π s).map _ else _)) = _
            rw [if_pos hg, uexec_ite_eq, if_pos hg]
            have h₁ := spec_is_uexec_extended n w c₁ π s
            rcases e₁ : uexecS n w c₁ π s with _ | r₁ <;> rw [e₁] at h₁
            · rcases e₁' : uexec n c₁ π s with _ | r₁' <;> rw [e₁'] at h₁
              · rfl
              · simp at h₁
            · rcases e₁' : uexec n c₁ π s with _ | r₁' <;> rw [e₁'] at h₁
              · simp at h₁
              · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, h₁.1, h₁.2,
                  true_and, and_self]
          · show (Option.map _ (if _ then _ else (uexecS n w c₂ π s).map _)) = _
            rw [if_neg hg, uexec_ite_eq, if_neg hg]
            have h₂ := spec_is_uexec_extended n w c₂ π s
            rcases e₂ : uexecS n w c₂ π s with _ | r₂ <;> rw [e₂] at h₂
            · rcases e₂' : uexec n c₂ π s with _ | r₂' <;> rw [e₂'] at h₂
              · rfl
              · simp at h₂
            · rcases e₂' : uexec n c₂ π s with _ | r₂' <;> rw [e₂'] at h₂
              · simp at h₂
              · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₂
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, h₂.1, h₂.2,
                  true_and, and_self]
      | loop e c₀ =>
          by_cases hg : evalE e s.store ≠ 0
          · show (Option.map _ (if _ then (uexecS n w c₀ π s).bind _ else _)) = _
            rw [if_pos hg, uexec_loop_eq, if_pos hg]
            have h₁ := spec_is_uexec_extended n w c₀ π s
            rcases e₁ : uexecS n w c₀ π s with _ | ⟨s₁, k₁, t₁⟩ <;> rw [e₁] at h₁
            · rcases e₁' : uexec n c₀ π s with _ | r₁' <;> rw [e₁'] at h₁
              · rfl
              · simp at h₁
            · rcases e₁' : uexec n c₀ π s with _ | ⟨s₁', k₁', t₁'⟩ <;> rw [e₁'] at h₁
              · simp at h₁
              · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₁
                obtain ⟨hst, hk⟩ := h₁
                subst hst; subst hk
                simp only [Option.bind_some]
                have h₂ := spec_is_uexec_extended n w (.loop e c₀) π s₁
                rcases e₂ : uexecS n w (.loop e c₀) π s₁ with _ | ⟨s₂, k₂, t₂⟩ <;> rw [e₂] at h₂
                · rcases e₂' : uexec n (.loop e c₀) π s₁ with _ | r₂' <;> rw [e₂'] at h₂
                  · rfl
                  · simp at h₂
                · rcases e₂' : uexec n (.loop e c₀) π s₁ with _ | ⟨s₂', k₂', t₂'⟩ <;> rw [e₂'] at h₂
                  · simp at h₂
                  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h₂
                    obtain ⟨hst2, hk2⟩ := h₂
                    subst hst2; subst hk2
                    rfl
          · show (Option.map _ (if _ then _ else some (s, 1, 1, ([] : List Int)))) = _
            rw [if_neg hg, uexec_loop_eq, if_neg hg]; rfl

/-! ## The machine can express the leak -/

/-- The Spectre-v1 gadget: a load whose **address** is the previous load's **value**. -/
def gadgetU : UCmd := .seq (.hop .load "x" "p") (.hop .load "y" "x")

/-- The victim. The guard is false, so architecturally the gadget never runs. -/
def victimU : UCmd := .ite (.num 0) gadgetU .skip

/-- A state holding a live cell at address 3 whose contents differ between the two
    worlds. Only `heap 3` differs; everything else is identical. -/
def specState (v : Int) : UState :=
  { store := fun x => if x = "p" then 3 else 0, auth := [], reads := [], dead := false,
    heap := fun a => if a = 3 then v else 0, live := [3], fresh := 100, err := false,
    freed := [], hlab := fun _ => false, sstore := fun _ => [], sink := [] }

/-- **Architecturally indistinguishable.** With no misprediction the trace is empty in
    both worlds: the guard is false and the gadget never runs. -/
theorem architecturally_indistinguishable_U :
    straceU 12 0 victimU (fun _ => true) (specState 42) = some []
  ∧ straceU 12 0 victimU (fun _ => true) (specState 99) = some [] := by decide

/-- **And under misprediction the trace is the secret.** The first transient load
    touches address 3 in both worlds; the second touches the *contents* of 3, which is
    42 in one world and 99 in the other. The model is therefore not vacuous — it can
    express the leak, which is what makes the rejection below worth something. -/
theorem victimU_leaks :
    straceU 12 2 victimU (fun _ => true) (specState 42) = some [3, 42]
  ∧ straceU 12 2 victimU (fun _ => true) (specState 99) = some [3, 99]
  ∧ ¬ (straceU 12 2 victimU (fun _ => true) (specState 42)
        = straceU 12 2 victimU (fun _ => true) (specState 99)) := by decide

/-- It needs a window of two. One transient command moves the secret into a register;
    it takes a second to turn that register into an address. At window one the two
    worlds agree. -/
theorem leak_needs_window_two_U :
    straceU 12 1 victimU (fun _ => true) (specState 42) = some [3]
  ∧ straceU 12 1 victimU (fun _ => true) (specState 99) = some [3] := by decide

/-! ## But the core already rejects it, for reasons written for other purposes -/

/-- **The gadget is not certifiable.** `slcheck`'s load rule is
    `load d p => if memStr p V then some (dropStr d V) else none`: the *source* must be a
    tracked pointer and the *destination* is dropped from the tracked set. So a loaded
    value can never afterwards be used as a pointer, and the second half of the gadget
    has no derivation. The rule was written for linearity in stage 1i, years of stages
    before speculation was on the table. -/
theorem gadget_rejected_by_memory_safety :
    slcheck ["p"] (.hop .load "x" "p") = some ["p"]
  ∧ slcheck ["p"] gadgetU = none
  ∧ slcheck ["p"] victimU = none
  ∧ xcheck Psec [] ["p"] ["p"] victimU = none := by decide

/-- **And the other route in is closed too.** A branch on a secret is rejected by the
    joint checker, so an attacker cannot make *which* branch mispredicts depend on a
    secret either. Memory safety alone would have allowed it — it is the flow
    certificate that refuses. -/
theorem secret_guard_rejected :
    slcheck ["p", "q"] (.ite (.var "secret") (.memop .deref "p") (.memop .deref "q"))
      = some ["p", "q"]
  ∧ xcheck Psec [] ["p", "q"] ["p", "q"]
      (.ite (.var "secret") (.memop .deref "p") (.memop .deref "q")) = none := by decide

/-- There is also no pointer arithmetic in the model, so the *first* half of Spectre-v1
    — the bounds-check bypass — has no analogue: every address comes from `alloc` and is
    copied, never computed, and `deref` accepts only what `live` holds. Recorded because
    the absence is a property of the model rather than a result. -/
theorem no_pointer_arithmetic_here :
    ((uexec 3 (.memop .deref "p") (fun _ => true)
        { specState 0 with store := fun _ => 4 }).map (fun r => r.1.err)) = some true := by
  decide

/-! ## What is not closed

    Two exclusions and one absence are not a theorem. The five certificates are
    statements about `UState`; the trace is not in `UState`; so nothing here *proves*
    that a certified program's trace is secret-independent. What is established is that
    the two standard routes to a transient leak are already blocked by rules written for
    other reasons, and that a search for a third route did not find one. That is a
    failure to find, and it is recorded as such.

    The conjecture worth trying next, stated so it can be attacked rather than assumed:
    **for every program `xcheck` accepts, the speculative trace is a function of the Low
    part of the initial state, under every window.** Proving it means an induction over
    `transRun` with the tracked-set invariant in hand, and the payoff would be row 9
    closed on `UCmd` rather than on brick 33's separate language. -/

/-! ## What is genuinely broken: the budget -/

/-- A branching program the core *does* certify, with a Low guard and two live
    pointers. -/
def brLow : UCmd := .ite (.var "l") (.memop .deref "p") (.memop .deref "q")

def twoLive : UState :=
  { store := fun x => if x = "p" then 3 else if x = "q" then 5 else 0,
    auth := [], reads := [], dead := false, heap := fun _ => 0, live := [3, 5],
    fresh := 100, err := false, freed := [], hlab := fun _ => false,
    sstore := fun _ => [], sink := [] }

/-- **Transient work is off the budget**, and this one is not blocked by anything. The
    certificate bounds the cost at 2, the machine reports 2 whatever the window, and yet
    at window 1 the machine really executed a third command — the trace grew from one
    entry to two, one per command run.

    Stage 1n found the budget was the law that would not compose over *loops*; stage 2a
    found it was the one law that *did* compose over *threads*. It fails here in a third
    way, and a different one: not wrong about what it counts, but counting the wrong
    thing. A resource bound that ignores transient execution is not a bound on the work
    the machine does. -/
theorem transient_work_is_off_the_budget :
    xcheck Psec [] ["p", "q"] ["p", "q"] brLow = some ([], ["p", "q"], ["p", "q"], 2, [])
  ∧ acostU 12 0 brLow (fun _ => true) twoLive = some 2
  ∧ rcostU 12 0 brLow (fun _ => true) twoLive = some 2
  ∧ acostU 12 1 brLow (fun _ => true) twoLive = some 2
  ∧ rcostU 12 1 brLow (fun _ => true) twoLive = some 3 := by decide

/-- And the trace shows the third command was a real memory access, not bookkeeping. -/
theorem the_extra_command_touches_memory :
    straceU 12 0 brLow (fun _ => true) twoLive = some [5]
  ∧ straceU 12 1 brLow (fun _ => true) twoLive = some [3, 5] := by decide

/-! ## The positive: branch-free programs are inert -/

/-- Does the program branch at all? Only `ite` can mispredict in this model. -/
def hasIte : UCmd → Bool
  | .ite _ _ _   => true
  | .seq c₁ c₂   => hasIte c₁ || hasIte c₂
  | .loop _ c    => hasIte c
  | _            => false

/-- **No branch, no speculation.** Without an `ite` the machine is independent of the
    window, so `spec_is_uexec_extended` carries every architectural guarantee across
    verbatim, under *every* misprediction rather than some. -/
theorem branch_free_is_inert : ∀ (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState),
    hasIte c = false → uexecS n w c π s = uexecS n 0 c π s
  | 0,     _, _, _, _, _  => rfl
  | n + 1, w, c, π, s, hc => by
      cases c with
      | skip => rfl
      | assign _ _ => rfl
      | check _ => rfl
      | access _ => rfl
      | memop _ _ => rfl
      | sop _ _ _ => rfl
      | hop _ _ _ => rfl
      | ite _ _ _ => simp [hasIte] at hc
      | seq c₁ c₂ =>
          simp only [hasIte, Bool.or_eq_false_iff] at hc
          show (uexecS n w c₁ π s).bind _ = (uexecS n 0 c₁ π s).bind _
          rw [branch_free_is_inert n w c₁ π s hc.1]
          rcases e₁ : uexecS n 0 c₁ π s with _ | r₁
          · rfl
          · simp only [Option.bind_some, branch_free_is_inert n w c₂ π r₁.1 hc.2]
      | loop e c₀ =>
          simp only [hasIte] at hc
          by_cases hg : evalE e s.store ≠ 0
          · show (if _ then (uexecS n w c₀ π s).bind _ else _)
                  = (if _ then (uexecS n 0 c₀ π s).bind _ else _)
            rw [if_pos hg, if_pos hg, branch_free_is_inert n w c₀ π s hc]
            rcases e₁ : uexecS n 0 c₀ π s with _ | r₁
            · rfl
            · simp only [Option.bind_some,
                branch_free_is_inert n w (.loop e c₀) π r₁.1 (by simp [hasIte, hc])]
          · show (if _ then _ else some (s, 1, 1, ([] : List Int)))
                  = (if _ then _ else some (s, 1, 1, ([] : List Int)))
            rw [if_neg hg, if_neg hg]

/-- **The worked program is speculation-proof**, because it never branches. Narrow, but
    it is a real statement about a real program: `fiveProg`'s five certificates hold on
    the speculative machine under every misprediction. -/
theorem fiveProg_is_speculatively_inert :
    hasIte fiveProg = false
  ∧ ∀ (n w : Nat) (π : MedPolicy) (s : UState),
      uexecS n w fiveProg π s = uexecS n 0 fiveProg π s :=
  ⟨by decide, fun n w π s => branch_free_is_inert n w fiveProg π s (by decide)⟩

/-! ## What this stage claims

    A machine, faithful at `w = 0`; two obstructions; one positive. It does **not**
    claim a fence rule on `UCmd` — brick 33 has one on its own language, and porting it
    is the follow-on this stage names rather than performs. It does not claim the leak
    is the only one: the trace is addresses only, so cache-line granularity, eviction,
    timing and contention are all outside it.

    What it does establish is where the next rule has to act. Both findings are about
    the same thing: `UState` rolls back and the trace does not, so a judgment over
    `UState` — which all five certificates are — cannot see either of them. That is not
    a defect in the certificates. It means the observation has to grow a component, and
    by stage 1z's rule of thumb, changes that touch the observation are the expensive
    ones. Knowing that before starting is the point of stopping here. -/

end ConfTyping
