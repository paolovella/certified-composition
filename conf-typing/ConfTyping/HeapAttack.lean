/-
  Stage 1y: attacking the labelled heap.

  Stage 1t's discipline, applied to the three stages that have just landed. Two
  questions: is the new guarantee vacuous the way the string one was, and does anything
  reasonable get refused for a bad reason?

  **The guarantee is not vacuous.** Stage 1t found that noninterference exported from
  `initU` said nothing about strings, because `initU` gives every string variable the
  same empty value — the statement was true and empty. The heap could have gone the same
  way, since `initU` gives both runs the same heap. It does not:
  `secret_write_is_not_vacuous` runs a certified program from two `initU` states
  differing only in a High variable and lands with **different values in the secret
  cell** (3 against 0) while remaining Low-equal. The per-address observation is doing
  work.

  **And a real gap: a secret cell can never be freed.** Not because either rule is
  wrong, but because two correct rules compose into something too strong:

  * stage 1u: `free` needs a **Low** pointer, since the free list decides the next
    address and is therefore observed;
  * stage 1w: a secret cell is reached through a **High** pointer, since the label must
    match the pointer's level.

  So `free` and "secret cell" cannot both apply, and secret memory leaks by
  construction. `secret_cells_can_never_be_freed` states it, and
  `public_cells_can_be_freed` shows the restriction is specific rather than a general
  failure of deallocation.

  The fix is identifiable and is a stage of its own, so it is named rather than
  attempted: give secret allocation its **own counter and own free list**, neither
  observed, over a disjoint address range (public addresses non-negative, secret ones
  negative). Freeing a secret pointer then perturbs only unobserved state, which is
  exactly what stage 1u's argument needs. It splits the address space, so it touches
  separation — `SepInv`'s freshness conjunct becomes two conjuncts — and that is why it
  is not a patch.
-/
import ConfTyping.HeapSecret

namespace ConfTyping

/-! ## The guarantee is not vacuous -/

/-- Two High names: a secret value and a secret pointer. `Psec` has only one, and the
    allocation would overwrite it — which is why this probe needs its own partition. -/
def Ptwo : Partition := fun x => x == "h" || x == "sp"

/-- Allocate a secret cell and write the secret into it. -/
def secretWrite : UCmd := .seq (.memop .allocS "sp") (.hop .store "sp" "h")

theorem secretWrite_checks : allcheck Ptwo [] [] secretWrite = some ([], ["sp"], 2) := by
  decide

/-- **The heap observation earns its keep.** From two `initU` states differing only in
    the High variable `h`, the certified program leaves **different values in the secret
    cell** — 3 against 0 — and the two runs are still Low-equal. Contrast stage 1t's
    finding, where the analogous statement about strings was true and empty because
    `initU` made the two runs identical in that dimension. Here it does not. -/
theorem secret_write_is_not_vacuous :
    ((uexec 5 secretWrite (fun _ => true)
        (initU (fun y => if y == "h" then 3 else 0))).map
      (fun r => (r.1.heap 0, r.1.hlab 0))) = some (3, true)
  ∧ ((uexec 5 secretWrite (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.heap 0, r.1.hlab 0))) = some (0, true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Ptwo σ σ' →
      uOptLowEq Ptwo (uexec n secretWrite π (initU σ))
                     (uexec n secretWrite π (initU σ'))) :=
  ⟨by decide, by decide, (allcheck_gives_four secretWrite_checks).2.2.1⟩

/-! ## The gap: secret memory cannot be released -/

/-- **The gap this stage found, and stage 1z's answer.** As of stage 1y a secret cell
    could never be freed: `free` needed a Low pointer (stage 1u — the free list decides
    the next address and is observed) while a secret cell is reached through a High
    pointer (stage 1w — the label matches the pointer's level). Each condition was
    right and jointly they were unsatisfiable.

    Stage 1z removed the conflict by changing the *model* rather than either rule: a
    secret address is **retired** instead of recycled, so freeing through a secret
    pointer touches only `live`, which is unobserved. The statement below is what the
    finding turned into. -/
theorem secret_cells_can_now_be_freed :
    jcheck Ptwo ["sp"] (.memop .free "sp") = some []
  ∧ allcheck Ptwo [] [] (.seq (.memop .allocS "sp") (.memop .free "sp"))
      = some ([], [], 2) := by decide

/-- The restriction is specific, not a general failure of deallocation: a public cell is
    allocated and freed without complaint. -/
theorem public_cells_can_be_freed :
    allcheck Ptwo [] [] (.seq (.memop .alloc "buf") (.memop .free "buf"))
      = some ([], [], 2) := by decide

/-- Memory safety never objected — `slcheck` frees the secret pointer happily, because
    liveness does not care about labels. That is what located the gap on the
    information-flow side, and it is why the fix was a change to the allocator rather
    than to either typing rule. -/
theorem memory_safety_always_allowed_it :
    slcheck ["sp"] (.memop .free "sp") = some [] := by decide

/-- The three together, after the fix: safe to free, *now* accepted for flow reasons
    too, and the public case unaffected. -/
theorem the_gap_closed :
    slcheck ["sp"] (.memop .free "sp") = some []
  ∧ jcheck Ptwo ["sp"] (.memop .free "sp") = some []
  ∧ allcheck Ptwo [] [] (.seq (.memop .alloc "buf") (.memop .free "buf"))
      = some ([], [], 2) := by decide

/-! ## What the fix would be

    Give secret allocation its own counter and its own free list, neither observed, over
    a disjoint address range — public addresses non-negative, secret ones negative.
    Freeing a secret pointer then perturbs only unobserved state, which is exactly what
    stage 1u's argument requires, and `alloc`/`allocS` never contend for an address.

    It is not a patch: `SepInv`'s freshness conjunct becomes two conjuncts over two
    ranges, and the disjointness of the ranges becomes part of the separation argument
    rather than a consequence of one counter. On the evidence of 1w and 1x, that is an
    invariant stage followed by a short rule stage.

    Recorded here rather than attempted, because the pattern of the last three stages is
    that guessing at the size of a change to the memory model has been unreliable — the
    reuse of stage 1u was cheaper than predicted and the labels of 1w were dearer. -/

/-- A note kept as a theorem: the two rules that combine badly are each still doing
    their job, so neither can simply be dropped. Stage 1u's rule stops a real leak, and
    stage 1w's is what makes the flow rules syntactic. -/
theorem both_rules_are_load_bearing :
    -- 1u: freeing a High pointer diverges the allocators (the witness from that stage)
    ((uexec 5 freeThenAlloc (fun _ => true) ptrFive).map (fun r => r.1.store "pub"))
      = some 5
  ∧ ((uexec 5 freeThenAlloc (fun _ => true) ptrSeven).map (fun r => r.1.store "pub"))
      = some 7
    -- 1w: the label must match, or the invariant is not inductive
  ∧ allcheck Psec [] [] (.memop .allocS "buf") = none := by decide

end ConfTyping
