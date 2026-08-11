/-
  Stage 1w: per-address heap labels — the invariant.

  Stage 1v made the heap real and, to keep noninterference sound, made it entirely
  public: `storing_a_secret_is_refused`. Lifting that needs a **label per address**, and
  the payoff rules — storing a secret through a secret pointer, loading with the
  destination's level determined by the cell's — can only be *syntactic* if the analysis
  can read a cell's level off the program text. That is what this stage establishes, and
  it is deliberately the whole of this stage: the rules that spend the invariant come
  next.

  The pieces:

  * `UState` gains `hlab : Int → Bool`, fixed at allocation, and `MemOp` gains `allocS`
    so the allocation *site* declares the cell's level.
  * **Allocation zeroes its cell.** This is not tidiness. With reuse (stage 1u), a freed
    *secret* cell handed back out as a *public* one would expose its old contents — a
    public address whose value differs between runs. Zeroing is what makes relabelling
    on reuse safe, and it is an interaction between two stages that neither produced
    alone.
  * `LabInv P V s` — **every tracked pointer points at a cell of its own level** — with
    `JSecTy.toLabInv` proving it inductive. Separation (stage 1i) is what makes it work:
    no two tracked pointers can share a cell, so no cell has two levels.
  * `JSecTy.alloc` gains `P x = false` and `allocS` requires `P x = true`. That is the
    price, and it is a *consistency* condition, not a secrecy one — see the corrected
    note on `alloc_rule_rests_on_low_guards`.

  **What this stage does not do**, stated plainly because the field would otherwise look
  like it earns more than it does: the observation still has `s.heap = s'.heap`, so the
  heap is still public and `storing_a_secret_is_refused` still holds. `LabInv` is proved
  and unused by noninterference. Stage 1x replaces the heap conjunct with
  "labels agree, and public cells agree" and adds the rules; this stage exists so that
  when it does, the invariant it needs is already there and audited.
-/
import ConfTyping.HeapValue

namespace ConfTyping

theorem allcheck_maintains_labels {P : Partition} {c : UCmd} {A' V' : List String}
    {k : Nat} (h : allcheck P [] [] c = some (A', V', k)) :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n c π (initU σ) = some r → LabInv P V' r.1 :=
  fun n π σ r hr =>
    (allcheck_sound c [] [] A' V' k h).joint.toLabInv n π (initU σ) r
      SepInv.initU LabInv.initU hr

/-! ## Witnesses -/

/-- A public buffer and a secret one, side by side. -/
def twoCells : UCmd := .seq (.memop .alloc "buf") (.memop .allocS "secret")

theorem twoCells_checks : allcheck Psec [] [] twoCells = some ([], ["secret", "buf"], 2) := by
  decide

/-- **The labels really are set, and they differ.** The public cell is labelled `false`
    and the secret one `true`, at distinct addresses. -/
theorem twoCells_labels :
    ((uexec 5 twoCells (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.store "buf", r.1.store "secret",
                 r.1.hlab (r.1.store "buf"), r.1.hlab (r.1.store "secret"))))
      = some (0, 1, false, true) := by decide

/-- The allocation site must agree with the pointer's level: a public allocation into a
    secret variable, or the reverse, is refused. -/
theorem allocation_site_must_match_the_level :
    allcheck Psec [] [] (.memop .alloc "secret") = none
  ∧ allcheck Psec [] [] (.memop .allocS "buf") = none := by decide

/-- **Allocation zeroes.** With reuse, a recycled cell must not carry its old contents
    across a relabelling — so `alloc` clears it. Write 7 through a pointer, free it,
    allocate again, and the new cell reads 0 rather than 7. -/
theorem allocation_zeroes :
    ((uexec 13 (.seq (.memop .alloc "p")
                (.seq (.assign "v" (.num 7))
                 (.seq (.hop .store "p" "v")
                  (.seq (.memop .free "p")
                   (.seq (.memop .alloc "q") (.hop .load "d" "q"))))))
        (fun _ => true) (initU (fun _ => 0))).map (fun r => (r.1.store "d", r.1.err)))
      = some (0, false) := by decide

/-! ## What is not claimed

    The observation still contains `s.heap = s'.heap`: the heap is public, and
    `HeapValue.storing_a_secret_is_refused` still holds. `LabInv` is proved and *not yet
    used* by noninterference — which is the honest description of an invariant stage.

    Stage 1x is the other half: replace the heap conjunct with "labels agree, and public
    cells agree", and add the rules that spend the invariant — `storeH` (a secret
    through a secret pointer is invisible) and a label-aware `loadL`. Splitting it this
    way means the invariant is audited before anything depends on it, which is the order
    stages 1j and 1k used for the analogous problem. -/

/-- The scope, as a theorem. **Renamed by stage 1x**: when this was written the heap was
    entirely public and this said so. Stage 1x made the heap two-level, and the same
    statement now means something narrower and still true — a *public* pointer points at
    a public cell, so it cannot carry a secret. See
    `HeapSecret.public_pointer_still_cannot_carry_a_secret`. -/
theorem public_pointer_cannot_carry_a_secret :
    jcheck Psec ["p"] (.hop .store "p" "secret") = none := by decide

end ConfTyping
