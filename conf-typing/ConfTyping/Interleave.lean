/-
  Stage 2a: two threads on the unified machine — what composes and what does not.

  Brick 32 proved race freedom on its own small language, with schedules as data and a
  demonic quantifier. It has never been brought onto `UCmd`, and that is the largest
  remaining distance between "sixteen bricks" and "one core". This stage takes the first
  step, and by the rule of thumb stage 1z produced — changes that touch the observation
  or an invariant are the expensive ones — the first step is to find the obstruction
  rather than to build the proof.

  **The machine.** `uexecPar` interleaves two threads at *command* granularity: a
  schedule (a list of booleans) picks which thread runs its next command, and each
  command runs atomically. That is the granularity at which a check and its use can be
  torn apart, which is what makes it worth modelling; finer granularity would need a
  small-step semantics and is a different piece of work.

  **What does not compose: memory safety.** `interleaving_breaks_memory_safety` is two
  threads, *each individually certified* — thread 1 allocates and dereferences,
  certified from the empty tracked set; thread 2 frees, certified given the pointer
  tracked — whose sequential run is clean and whose interleaving faults. Nothing is
  wrong with either certificate. The tracked set is **thread-local**, and nothing makes
  one thread's set an obligation on the other.

  And by stage 1j's dependency the failure propagates: noninterference for `deref`
  *needs* the memory invariant, so a judgment that cannot maintain the invariant across
  threads cannot deliver the flow guarantee either. That is 1j's finding doing work at a
  distance — the entanglement it identified is exactly what stops the two properties
  being rescued separately here.

  **What does compose: the budget.** `budget_composes_across_threads` — the cost of an
  interleaving is the sum of the commands run, whatever the schedule. The one law that
  refused to compose over *loops* (stage 1n) is the one that composes over *threads*
  without a murmur, which is worth noticing: the budget is a property of the trace and
  cares about neither state nor order.

  **And disjoint threads are already fine.** `disjoint_threads_are_safe` runs two
  threads that share no variable at two different schedules with no fault. That is the
  shape of the fix — ownership, in the separation-logic sense: the two tracked sets must
  be disjoint, and freeing must be the owner's prerogative. Naming it is as far as this
  stage goes.

  One scoping note, recorded because it will matter later:
  `addresses_depend_on_the_schedule` shows the allocator hands out different addresses
  under different schedules. The schedule is a *public* input here — demonic, as in
  brick 32 — so this is not a leak. It would become one the moment a schedule could
  depend on a secret, which is the assumption a scheduler model would have to state.
-/
import ConfTyping.HeapRetire

namespace ConfTyping

/-! ## Coarse-grained interleaving -/

/-- Interleave two threads at **command** granularity: the schedule picks a thread and
    that thread's next command runs atomically. Returns the final state and the total
    cost. A thread whose turn comes when it is finished simply yields. -/
def uexecPar : Nat → List Bool → List UCmd → List UCmd → MedPolicy → UState →
    Option (UState × Nat)
  | 0,     _,           _,       _,       _, _ => none
  | _ + 1, [],          _,       _,       _, s => some (s, 0)
  | k + 1, _ :: bs,     [],      [],      π, s => uexecPar k bs [] [] π s
  | k + 1, true :: bs,  c :: cs, t2,      π, s =>
      (uexec 30 c π s).bind fun r =>
        (uexecPar k bs cs t2 π r.1).map fun q => (q.1, r.2.1 + q.2)
  | k + 1, false :: bs, t1,      c :: cs, π, s =>
      (uexec 30 c π s).bind fun r =>
        (uexecPar k bs t1 cs π r.1).map fun q => (q.1, r.2.1 + q.2)
  | k + 1, true :: bs,  [],      t2,      π, s => uexecPar k bs [] t2 π s
  | k + 1, false :: bs, t1,      [],      π, s => uexecPar k bs t1 [] π s

/-! ## What does not compose: memory safety -/

/-- Allocates a pointer and uses it. Certified from the empty tracked set. -/
def threadUse : List UCmd := [.memop .alloc "p", .memop .deref "p"]

/-- Frees that pointer. Certified *given* the pointer is tracked. -/
def threadFree : List UCmd := [.memop .free "p"]

/-- Each thread carries a memory-safety certificate in its own right. -/
theorem both_threads_are_certified :
    slcheck [] (.seq (.memop .alloc "p") (.memop .deref "p")) = some ["p"]
  ∧ slcheck ["p"] (.memop .free "p") = some [] := by decide

/-- **Two certified threads, one faulting interleaving.** Run thread 1 to completion and
    then thread 2 and nothing goes wrong. Interleave them — allocate, free, dereference
    — and the dereference faults. Neither certificate is wrong; the tracked set is
    *thread-local*, and nothing makes one thread's set an obligation on the other. -/
theorem interleaving_breaks_memory_safety :
    ((uexecPar 9 [true, true, false] threadUse threadFree (fun _ => true)
        (initU (fun _ => 0))).map (fun r => (r.1.err, r.1.dead))) = some (false, false)
  ∧ ((uexecPar 9 [true, false, true] threadUse threadFree (fun _ => true)
        (initU (fun _ => 0))).map (fun r => (r.1.err, r.1.dead))) = some (true, true) := by
  decide

/-- The three facts together: both certified, sequential clean, interleaved faulting. -/
theorem thread_local_certificates_do_not_compose :
    slcheck [] (.seq (.memop .alloc "p") (.memop .deref "p")) = some ["p"]
  ∧ slcheck ["p"] (.memop .free "p") = some []
  ∧ ((uexecPar 9 [true, false, true] threadUse threadFree (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some true := by decide

/-! ## What does compose: the budget -/

/-- **Cost is a property of the trace, not of the state or the order.** The interleaved
    run and the sequential run cost the same — three commands, three units — so the one
    law that refused to compose over *loops* (stage 1n) composes over *threads* without
    a murmur. -/
theorem budget_composes_across_threads :
    ((uexecPar 9 [true, true, false] threadUse threadFree (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.2)) = some 3
  ∧ ((uexecPar 9 [true, false, true] threadUse threadFree (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.2)) = some 3 := by decide

/-! ## The shape of the fix -/

def threadA : List UCmd := [.memop .alloc "a", .memop .deref "a"]
def threadB : List UCmd := [.memop .alloc "b", .memop .deref "b"]

/-- **Disjoint threads are already fine**, at either schedule. That is the shape of the
    fix — ownership in the separation-logic sense: the two tracked sets must be
    disjoint, and freeing must be the owner's prerogative. Naming it is as far as this
    stage goes. -/
theorem disjoint_threads_are_safe :
    ((uexecPar 9 [true, false, true, false] threadA threadB (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some false
  ∧ ((uexecPar 9 [false, true, false, true] threadA threadB (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some false := by decide

/-- **A scoping note that will matter later.** The allocator hands out different
    addresses under different schedules — `a` gets 0 or 1 depending on who runs first.
    The schedule is a *public* input here, demonic as in brick 32, so this is not a
    leak. It would become one the moment a schedule could depend on a secret, which is
    an assumption any scheduler model would have to state. -/
theorem addresses_depend_on_the_schedule :
    ((uexecPar 9 [true, false, true, false] threadA threadB (fun _ => true)
        (initU (fun _ => 0))).map (fun r => (r.1.store "a", r.1.store "b")))
      = some (0, 1)
  ∧ ((uexecPar 9 [false, true, false, true] threadA threadB (fun _ => true)
        (initU (fun _ => 0))).map (fun r => (r.1.store "a", r.1.store "b")))
      = some (1, 0) := by decide

/-! ## What this stage claims

    A machine, one obstruction, and one positive. It does **not** claim a race-freedom
    certificate on `UCmd`: there is no `JSecTy`-style rule for interleaving here, and
    brick 32's results stay where they are, on their own language.

    The obstruction is precise enough to act on. Memory safety fails because the tracked
    set is thread-local with no ownership discipline; noninterference cannot be rescued
    separately because stage 1j showed its `deref` rule *needs* that invariant. So the
    next step is a judgment indexed by an ownership split — which, on the evidence of
    1j → 1k, means a new indexed judgment rather than a side condition, and on the
    evidence of 1w → 1x, an invariant stage before a rule stage. -/

end ConfTyping
