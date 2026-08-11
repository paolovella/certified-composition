/-
  Stage 1z: closing stage 1y's gap — secret addresses are retired, not recycled.

  Stage 1y found a gap made by two correct rules. `free` needed a **Low** pointer
  (stage 1u: the freed address goes on the free list, and the free list decides the next
  allocation, so it is observed). A secret cell is reached through a **High** pointer
  (stage 1w: the label matches the pointer's level). Jointly unsatisfiable, so a secret
  cell could never be freed and secret memory leaked by construction.

  Stage 1y named a fix — a separate unobserved counter and free list for secret
  allocation over a disjoint address range — and guessed it would cost an invariant
  stage plus a rule stage. **That guess was wrong, and expensively so if it had been
  followed.** A much smaller change does the whole job: when a *secret* cell is freed,
  put its address nowhere. Retire it.

  Then freeing through a secret pointer perturbs only `live`, which is not observed, and
  `free` needs no level condition at all. `SepInv` did not change — pushing fewer
  addresses onto the free list can only make its conjuncts easier — and no new invariant
  was needed. The whole stage is one branch in `uexec` and one dropped hypothesis.

  **What it costs, stated plainly**: secret addresses are never reused.
  `public_is_recycled_secret_is_retired` shows the difference — after a public
  allocate-free-allocate the address comes back, after a secret one it does not. That is
  address-space consumption, not a safety property, and this model makes no claim about
  address-space exhaustion. It is the honest price and it is much cheaper than the split
  address space would have been.

  **What became of stage 1u's leak.** `Reuse.freeing_a_secret_pointer_leaks` is still
  true — it is a statement about two concrete states. What changed is that those states
  are now provably unreachable by a checked program: `ptrFive` aims a *secret* pointer
  at a cell labelled public, and `the_leaking_state_violates_the_label_invariant` shows
  that is exactly what `LabInv` forbids. The leak was real in the model that admitted
  such a state; stage 1w's invariant is what rules it out.
-/
import ConfTyping.HeapAttack

namespace ConfTyping

/-! ## A secret cell now has a full lifecycle -/

/-- Allocate a secret cell, write the secret into it, read it back, release it. Before
    stage 1z the last step was untypable. -/
def secretLifecycle : UCmd :=
  .seq (.memop .allocS "sp")
   (.seq (.hop .store "sp" "h") (.seq (.hop .load "h" "sp") (.memop .free "sp")))

theorem secretLifecycle_checks :
    allcheck Ptwo [] [] secretLifecycle = some ([], [], 4) := by decide

/-- And it runs: the secret goes into the cell and comes back out, nothing faults, and
    the cell is released. -/
theorem secretLifecycle_runs :
    ((uexec 9 secretLifecycle (fun _ => true)
        (initU (fun y => if y == "h" then 3 else 0))).map
      (fun r => (r.1.store "h", r.1.live, r.1.freed, r.1.err)))
      = some (3, [], [], false) := by decide

/-- **The gap is closed**, and it took no new condition: `free` carries none at all. -/
theorem free_has_no_level_condition :
    jcheck Ptwo ["sp"] (.memop .free "sp") = some []
  ∧ jcheck Ptwo ["buf"] (.memop .free "buf") = some [] := by decide

/-! ## The price -/

/-- **Public addresses are recycled; secret ones are retired.** After a public
    allocate-free-allocate the same address comes back. After a secret lifecycle the
    next public allocation gets a *fresh* address — the secret one is gone for good.
    That is address-space consumption, not a safety property, and it is the whole cost
    of closing the gap. -/
theorem public_is_recycled_secret_is_retired :
    ((uexec 11 (.seq (.seq (.memop .alloc "b1") (.memop .free "b1")) (.memop .alloc "b2"))
        (fun _ => true) (initU (fun _ => 0))).map (fun r => (r.1.store "b2", r.1.fresh)))
      = some (0, 1)
  ∧ ((uexec 11 (.seq secretLifecycle (.memop .alloc "buf")) (fun _ => true)
        (initU (fun _ => 0))).map (fun r => (r.1.store "buf", r.1.freed, r.1.fresh)))
      = some (1, [], 2) := by decide

/-! ## What became of the earlier rule

    Stage 1u's `free`-needs-a-Low-pointer was correct for stage 1u's model, and its
    witness is still a true statement about two concrete states. Stage 1w's invariant is
    what makes those states unreachable, and stage 1z's retirement is what makes the
    rule unnecessary. Three stages, and the middle one is doing the load-bearing work —
    which was not visible when it was written, because 1w had no payoff of its own. -/

/-- The three facts in one place: the old leak is still a leak in its own terms, the
    state it needs is forbidden by the label invariant, and the rule that used to guard
    against it is gone. -/
theorem the_rule_is_no_longer_needed :
    ((uexec 5 freeThenAlloc (fun _ => true) ptrFive).map (fun r => r.1.store "pub"))
      = some 5
  ∧ ¬ LabInv Psec ["secret"] ptrFive
  ∧ jcheck Ptwo ["sp"] (.memop .free "sp") = some [] :=
  ⟨by decide, the_leaking_state_violates_the_label_invariant, by decide⟩

/-! ## The estimate, and what it was worth

    Stage 1y predicted this would need "an invariant stage followed by a short rule
    stage", by analogy with 1w and 1x. It needed one branch in the evaluator and one
    dropped hypothesis, and no new invariant at all.

    That is the third memory-model estimate in a row to be wrong — 1u cheaper than
    predicted, 1w dearer, 1z much cheaper — and the pattern in the misses is worth more
    than any single one: the expensive changes were the ones that touched the
    *observation* or an *invariant*, and the cheap ones were the ones that touched only
    the semantics. Retiring an address changes what the machine does; it changes nothing
    about what is observed or what must be maintained, which is why `SepInv` did not
    move. That is a usable rule of thumb rather than another guess. -/

end ConfTyping
