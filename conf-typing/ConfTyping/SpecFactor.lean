/-
  The composable core, stage 2g: the trace does not factor either.

  Stage 2f produced the two halves of a step case — `ptrLow_step`, which keeps the
  pointer invariant, and `touched_agrees`, which turns it into agreement of the addresses
  touched. The obvious next move is to lift them to whole programs by induction, layered
  on top of the noninterference proof the repo already has.

  **That does not work, and this stage says why in the form of a theorem rather than a
  difficulty.**

  Write down the relation a trace argument visibly needs: low-equal stores (for the
  branch guards), equal `dead`, equal `fresh` and `freed` (for the allocator), agreeing
  public heap cells, and `PtrLow` (for the addresses). Call it `TraceEq`. It omits
  `SepInv` and `LabInv`, because nothing in the *statement* of trace agreement mentions
  separation or heap labels.

  `traceEq_is_not_inductive` shows `TraceEq` is not preserved by a single certified
  command. The witness is a `load` through a **Low** pointer: `jcheck`'s rule accepts
  `load d p` when `p` is tracked and `!P p || P d`, so a Low pointer may load into a Low
  variable — and if the *cell* it points at is secret, the two runs disagree afterwards
  in a Low variable. `labInv_is_the_missing_hypothesis` identifies the exclusion:
  `LabInv P V s` says `s.hlab (s.store x) = P x`, so a Low tracked pointer never points
  at a secret cell, and the witness violates exactly that.

  So the trace conclusion has to be **fused into** `jsecTy_sound`, which already carries
  `SepInv` and `LabInv` through its induction, rather than layered on top of it. That is
  a statement about where the next proof goes, and it is worth having before writing four
  hundred lines in the wrong place.

  **This is stage 1j one level up.** 1j showed noninterference and memory safety do not
  factor — the `deref` rule needs the memory invariant. The same entanglement now reaches
  the trace: the addresses a program touches cannot be shown Low without the heap-label
  invariant, which is a memory-safety artefact. Three properties, one induction, and the
  repo has now hit that wall from three different directions.

  **What is positive here.** `traced_step_agrees` assembles 2f's two halves into exactly
  the step lemma the fused induction will consume: given the four invariants and the
  pointer one, a certified atomic command touches the same addresses in both runs *and*
  leaves the pointer invariant standing. The step case is done; it is the frame around it
  that has to change.
-/
import ConfTyping.SpecTrace

namespace ConfTyping

/-! ## The relation a layered proof would use -/

/-- Everything a trace argument visibly needs, and nothing else. Low-equal stores for the
    branch guards, `dead` for whether anything executes at all, `fresh`/`freed` for the
    allocator, public cells for the values that flow, and `PtrLow` for the addresses.

    `SepInv` and `LabInv` are deliberately absent: nothing in the *statement* of trace
    agreement mentions separation or heap labels. -/
structure TraceEq (P : Partition) (V : List String) (s s' : UState) : Prop where
  store  : lowEq P s.store s'.store
  dead   : s.dead = s'.dead
  fresh  : s.fresh = s'.fresh
  freed  : s.freed = s'.freed
  labels : s.hlab = s'.hlab
  cells  : ∀ a, s.hlab a = false → s.heap a = s'.heap a
  ptrs   : PtrLow V s s'

/-! ## It is not inductive -/

/-- A **Low** pointer `p` aimed at a **secret** cell. Everything else is identical
    between the two worlds; only the secret cell's contents differ. -/
def secretCell (v : Int) : UState :=
  { store := fun x => if x = "p" then 3 else 0, auth := [], reads := [], dead := false,
    heap := fun a => if a = 3 then v else 0, live := [3], fresh := 100, err := false,
    freed := [], hlab := fun a => a == 3, sstore := fun _ => [], sink := [] }

theorem secretCell_traceEq : TraceEq Psec ["p"] (secretCell 42) (secretCell 99) := by
  refine ⟨fun x _ => rfl, rfl, rfl, rfl, rfl, ?_, fun _ x hx => rfl⟩
  intro a ha
  have : ¬ (a = 3) := by
    intro h; rw [h] at ha; exact absurd ha (by decide)
  simp only [secretCell, ite_eq_right this]

/-- The command is certified: `jcheck`'s load rule wants the source tracked and
    `!P p || P d`, and a Low pointer satisfies that whatever the destination is. -/
theorem the_load_is_certified :
    jcheck Psec ["p"] (.hop .load "d" "p") = some ["p"]
  ∧ allcheck Psec [] ["p"] (.hop .load "d" "p") = some ([], ["p"], 1) := by decide

/-- **`TraceEq` is not inductive.** One certified command takes two states satisfying it
    to two states that disagree in the Low variable `d`, because the Low pointer was
    aimed at a secret cell. A trace argument layered on this relation cannot get past its
    first step. -/
theorem traceEq_is_not_inductive :
    TraceEq Psec ["p"] (secretCell 42) (secretCell 99)
  ∧ jcheck Psec ["p"] (.hop .load "d" "p") = some ["p"]
  ∧ ((uexec 1 (.hop .load "d" "p") (fun _ => true) (secretCell 42)).map
        (fun r => r.1.store "d")) = some 42
  ∧ ((uexec 1 (.hop .load "d" "p") (fun _ => true) (secretCell 99)).map
        (fun r => r.1.store "d")) = some 99
  ∧ Psec "d" = false :=
  ⟨secretCell_traceEq, by decide, by decide, by decide, by decide⟩

/-- **And `LabInv` is the missing hypothesis.** It says a tracked pointer's cell carries
    the pointer's own label, so a Low pointer never points at a secret cell — which is
    precisely what the witness does. The exclusion is not incidental: it is the same
    invariant stage 1x introduced to make the heap two-level. -/
theorem labInv_is_the_missing_hypothesis :
    ¬ LabInv Psec ["p"] (secretCell 42) := by
  intro h
  have := h rfl "p" (List.mem_cons_self ..)
  exact absurd this (by decide)

/-- For contrast, a state where the Low pointer aims at a **public** cell does satisfy
    `LabInv`, so the invariant is not vacuous and the witness above is not the only
    shape a Low pointer can have. -/
def publicCell : UState :=
  { store := fun x => if x = "p" then 3 else 0, auth := [], reads := [], dead := false,
    heap := fun _ => 0, live := [3], fresh := 100, err := false,
    freed := [], hlab := fun _ => false, sstore := fun _ => [], sink := [] }

theorem publicCell_labInv : LabInv Psec ["p"] publicCell := by
  intro _ x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; rfl
  · cases h

/-! ## The step lemma the fused induction will consume -/

/-- **2f's two halves, assembled.** Given the invariants, a certified atomic command
    touches the same addresses in both runs *and* leaves the pointer invariant standing.
    This is exactly the step case of the theorem stage 2h has to prove; what stage 2g
    establishes is that the *frame* around it must be `jsecTy_sound`'s, carrying `SepInv`
    and `LabInv`, rather than a lighter one built for the trace alone. -/
theorem traced_step_agrees {P : Partition} {V V' : List String} {c : UCmd}
    {π : MedPolicy} {s s' : UState} {r r' : UState × Nat × List Bool}
    (hc : jcheck P V c = some V') (hlow : uLowEqA P s s') (hp : PtrLow V s s')
    (hr : uexec 1 c π s = some r) (hr' : uexec 1 c π s' = some r') :
    touched c s = touched c s' ∧ PtrLow V' r.1 r'.1 :=
  ⟨touched_agrees hc hlow.2.2.1 hp, ptrLow_step hc hlow hp hr hr'⟩

/-! ## What this settles

    The remaining work on the trace is not a new idea, it is a place. `jsecTy_sound` is
    the induction that already threads `SepInv`, `LabInv` and `uLowEqA` through every
    rule; the trace conclusion belongs inside it, with `PtrLow` added as a fifth
    hypothesis and `touched` agreement as a second conclusion. `traced_step_agrees` is
    the step case, already proved.

    Two honest notes. First, `TraceEq` not being inductive does not mean *no* lighter
    relation works — it means the obvious one does not, and the reason is structural
    rather than a missing lemma. Second, the transient window is untouched by any of
    this: `transRun` runs a checked command list from a state the same invariants hold
    at, so it inherits whatever the fused induction proves, but that inheritance is a
    lemma nobody has written.

    Stage 1j found that noninterference and memory safety do not factor. This is the same
    wall from a third direction, and the recurrence is now frequent enough to be a design
    fact about the core rather than an observation about three proofs. -/

end ConfTyping
