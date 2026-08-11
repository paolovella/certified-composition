/-
  Stage 1x: spending the label invariant — the heap stops being public.

  Stage 1v made the heap real and, to stay sound, made it entirely public: no secret
  could be stored at any address. Stage 1w built the invariant that lifts that —
  `LabInv`, every tracked pointer points at a cell of its own level — and deliberately
  did not use it. This uses it.

  Two changes, both small because 1w did the work:

  * **The observation is now per address.** `uLowEqA`'s `s.heap = s'.heap` becomes
    `s.hlab = s'.hlab ∧ (∀ a, s.hlab a = false → s.heap a = s'.heap a)`: the labels are
    public, the *public cells* are public, and secret cells are not observed.
  * **`JSecTy.storeH`**: a secret may be stored through a secret pointer. `LabInv` is
    what makes the rule syntactic — the pointer's level tells the analysis the cell's
    level, so `P p = true` is enough to know the write lands somewhere unobserved.

  `jsecTy_sound` gained the two `LabInv` hypotheses and `JSecTy.toLabInv` supplies them
  at every intermediate state; nothing else about the proof changed shape. That is the
  argument for having split the stages: the hard part was the invariant, and it was
  audited before anything depended on it.

  **What is now allowed, and what still is not.** `secret_through_a_secret_pointer` is
  the new ground. `public_pointer_still_cannot_carry_a_secret` is the boundary that
  remains, and it is the right one: a public pointer points at a public cell, so writing
  a secret there really would leak. `secret_cell_cannot_be_read_into_a_public_variable`
  closes the other direction. Together they say the heap is now **two-level** rather
  than public — which is what per-address labels were for.
-/
import ConfTyping.HeapLabel

namespace ConfTyping

/-! ## The new ground -/

/-- **A secret may now live in the heap.** Allocate a secret cell, write a secret
    through it: accepted. Stage 1v refused every such program. -/
theorem secret_through_a_secret_pointer :
    jcheck Psec ["secret"] (.hop .store "secret" "secret") = some ["secret"] := by decide

/-- A whole secret round trip: allocate a secret cell, store into it, read back into a
    secret variable. -/
theorem secret_round_trip_checks :
    allcheck Psec [] []
      (.seq (.memop .allocS "secret")
        (.seq (.hop .store "secret" "v") (.hop .load "secret" "secret")))
      = some ([], [], 3) := by decide

/-- Storing a *public* value through a secret pointer is fine too — the rule is about
    where the write lands, not what is written. -/
theorem public_value_into_a_secret_cell :
    jcheck Psec ["secret"] (.hop .store "secret" "v") = some ["secret"] := by decide

/-! ## The boundaries that remain, and why they are the right ones -/

/-- **A public pointer still cannot carry a secret.** `LabInv` says a public pointer
    points at a *public* cell, and public cells are observed — so this really would
    leak. Stage 1v's `storing_a_secret_is_refused` is this theorem, and it survived the
    stage unchanged. -/
theorem public_pointer_still_cannot_carry_a_secret :
    jcheck Psec ["p"] (.hop .store "p" "secret") = none := by decide

/-- And the other direction: a secret cell cannot be read into a public variable. -/
theorem secret_cell_cannot_be_read_into_a_public_variable :
    allcheck Psec [] []
      (.seq (.memop .allocS "secret")
        (.seq (.hop .store "secret" "v") (.hop .load "pub" "secret"))) = none := by decide

/-- The four together: the heap is **two-level** now, not public. -/
theorem the_heap_is_two_level :
    jcheck Psec ["secret"] (.hop .store "secret" "secret") = some ["secret"]
  ∧ jcheck Psec ["secret"] (.hop .store "secret" "v") = some ["secret"]
  ∧ jcheck Psec ["p"] (.hop .store "p" "secret") = none
  ∧ allcheck Psec [] []
      (.seq (.memop .allocS "secret")
        (.seq (.hop .store "secret" "v") (.hop .load "pub" "secret"))) = none := by decide

/-! ## What the split bought

    The whole of stage 1x is one observation change and one rule. Everything it needs —
    labels fixed at allocation, allocation zeroing so a recycled cell cannot carry its
    old contents across a relabelling, and `LabInv` proved inductive over all twenty
    rules — was built and audited in stage 1w without anything depending on it. That is
    why this stage is short.

    The remaining restriction is not a gap but a design point: labels are **fixed at
    allocation** and there is no declassification, so a cell cannot change level and a
    secret cannot be released. Adding a declassifying operation would be a policy
    decision of the kind stage 1e's ledger exists to record, not another typing rule. -/

/-- Labels are fixed at allocation: there is no operation that relabels a cell, so no
    program can launder a secret cell into a public one. Stated as the absence it is —
    `MemOp` and `HOp` have no relabelling constructor, and the checkers therefore have
    no rule to offer. -/
theorem no_relabelling_operation_exists :
    allcheck Psec [] [] (.seq (.memop .allocS "secret") (.memop .alloc "secret")) = none
  ∧ allcheck Psec [] [] (.seq (.memop .alloc "buf") (.memop .allocS "buf")) = none := by
  decide

end ConfTyping
