/-
  The composable core, stage 1m: the last open question, dissolved rather than decided.

  Stage 1j left one item on the conservatism list and framed it as a design fork:
  allocation into a **Low** variable publishes the allocation counter, so `allocL`
  seemed to need `fresh` in the observation — a decision about whether addresses are
  visible to a Low adversary, with the honest alternatives (a public allocator, or an
  address-renaming bisimulation) differing a lot in cost.

  Neither was necessary. This type system has **no High-guarded control flow**: every
  `ite` and `loop` guard must be `exprLow`. So two Low-equal runs perform the same
  allocations in the same order and their counters never drift. Instead of widening the
  observation, `jsecTy_sound` now carries `s.fresh = s'.fresh` as a **relational
  invariant** — and allocation becomes noninterferent with *no side condition at all*.

  So stage 1m removes a rule's hypothesis rather than adding a rule: `JSecTy.allocH`
  (which required `P x = true`) is replaced by `JSecTy.alloc`, and `jcheck`'s
  allocation case loses its test. The public guarantees are unchanged in statement —
  `uOptLowEqA.toLowEq` projects the strengthened relation back down, and two runs
  starting from `initU` agree on the counter for free.

  Two witnesses keep the argument honest, because "the invariant holds" is the kind of
  claim that is easy to assert and easy to get wrong.

  * `allocation_sync_is_load_bearing` — stage 1j's `allocL_would_be_unsound` is *still
    true*. Nothing about it was refuted; it is now exactly the statement that the
    relational invariant cannot be dropped, since Low-equal states with different
    counters really are separated by a Low allocation.
  * `high_branch_desynchronises_the_allocator` — and the invariant is not free: one
    High-guarded branch makes the counters differ. That branch is untypable here
    (`highBranch_is_untypable`), which is *why* the argument works — so if the language
    ever gains High-guarded control flow, this stage's rule must be revisited. Stated
    as a theorem rather than a comment, so the dependency cannot quietly rot.
-/
import ConfTyping.HeapWiden

namespace ConfTyping

/-! ## Allocation into a Low variable, now typable -/

/-- A public buffer: allocate it, use it. Under `Psec` the variable `buf` is Low, so
    stage 1j's rule could not type this at all. -/
def lowAllocProg : UCmd := .seq (.memop .alloc "buf") (.memop .deref "buf")

/-- **The rule that was open is now unconditional.** The joint checker types a Low
    allocation; the stage-1d checker still rejects the program, because it rejects
    every heap operation — so this is genuinely new ground, not a re-derivation. -/
theorem low_alloc_now_typable :
    jcheck Psec [] lowAllocProg = some ["buf"]
  ∧ jcheckW Psec 6 [] lowAllocProg = some ["buf"]
  ∧ ucheckNI Psec lowAllocProg = false := by decide

/-- Both guarantees for it, and they are the *same* statements as before: the
    synchronised relation is an internal device, not a weakened promise. -/
theorem lowAllocProg_both :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n lowAllocProg π (initU σ))
                       (uexec n lowAllocProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n lowAllocProg π (initU σ) = some r → r.1.err = false) :=
  jcheck_gives_both low_alloc_now_typable.1

/-- And it runs clean, with the buffer live at the end. -/
theorem lowAllocProg_runs :
    ((uexec 5 lowAllocProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.live))) = some (false, [0]) := by decide

/-! ## Why the relational invariant is needed, and what it rests on -/

/-- **Stage 1j's counterexample survives, with a changed job.** It was the reason
    `allocL` looked undecidable; it is now precisely the statement that the
    synchronisation invariant cannot be dropped — Low-equal states with different
    counters *are* separated by a Low allocation. Nothing was refuted; the same fact
    changed from an obstacle into a side-condition. -/
theorem allocation_sync_is_load_bearing :
    uLowEq Psec noAlloc noAlloc'
  ∧ ¬ (noAlloc.fresh = noAlloc'.fresh)
  ∧ (∃ r r' : UState × Nat × List Bool,
      uexec 1 (.memop .alloc "p") (fun _ => true) noAlloc = some r
    ∧ uexec 1 (.memop .alloc "p") (fun _ => true) noAlloc' = some r'
    ∧ ¬ lowEq Psec r.1.store r'.1.store) := by
  refine ⟨noAlloc_lowEq, by decide, ?_⟩
  obtain ⟨r, r', _, _, h1, h2, h3⟩ := allocL_would_be_unsound
  exact ⟨r, r', h1, h2, h3⟩

/-- Two states agreeing on everything Low *and* on the allocator, differing only in a
    secret. -/
def secretOne : UState :=
  { store := fun y => if y == "secret" then 1 else 0, auth := [], reads := [],
    dead := false, heap := fun _ => 0, live := [], fresh := 0, err := false, sstore := fun _ => [], sink := []  }

def secretZero : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false,
    heap := fun _ => 0, live := [], fresh := 0, err := false, sstore := fun _ => [], sink := []  }

theorem secret_states_lowEqA :
    uLowEqA Psec secretOne secretZero := by
  refine ⟨?_, rfl, rfl, rfl, fun _ _ => rfl, rfl⟩
  intro y hy
  show (if y == "secret" then (1 : Int) else 0) = 0
  have : ¬ (y == "secret") = true := by simpa [Psec] using hy
  simp [this]

/-- A branch on a secret, allocating in one arm only. -/
def highBranch : UCmd := .ite (.var "secret") (.memop .alloc "t") .skip

/-- **The invariant is not free — it rests on the absence of High-guarded control
    flow.** From two states that agree on the Low store *and* on the allocator, one
    secret-guarded branch leaves the counters different. This is the mechanism the
    stage-1m argument rules out, and the next theorem records how. -/
theorem high_branch_desynchronises_the_allocator :
    uLowEqA Psec secretOne secretZero
  ∧ ((uexec 3 highBranch (fun _ => true) secretOne).map (fun r => r.1.fresh)) = some 1
  ∧ ((uexec 3 highBranch (fun _ => true) secretZero).map (fun r => r.1.fresh)) = some 0 :=
  ⟨secret_states_lowEqA, by decide, by decide⟩

/-- And that branch is untypable, which is *why* stage 1m's rule is sound. The guard
    is not Low, so no `iteL`/`whileW` derivation admits it. Recorded as a theorem so
    that adding High-guarded control flow to `UCmd` would break a build rather than
    silently invalidate `JSecTy.alloc`. -/
theorem highBranch_is_untypable :
    exprLow Psec (.var "secret") = false
  ∧ jcheck Psec [] highBranch = none
  ∧ jcheckW Psec 6 [] highBranch = none := by decide

/-- The dependency, in one statement: allocation is unconditionally noninterferent
    **because** guards are Low. Drop the second and the first goes with it. -/
theorem alloc_rule_rests_on_low_guards :
    (∀ (P : Partition) (V : List String) (x : String),
        JSecTy P V (.memop .alloc x) (x :: V))
  ∧ exprLow Psec (.var "secret") = false
  ∧ ((uexec 3 highBranch (fun _ => true) secretOne).map (fun r => r.1.fresh))
      ≠ ((uexec 3 highBranch (fun _ => true) secretZero).map (fun r => r.1.fresh)) :=
  ⟨fun P V x => JSecTy.alloc (P := P) V x, by decide, by decide⟩

/-! ## The conservatism list is empty

    Stage 1j opened three items: High allocation (closed there), `deref`/`free` without
    an unconditional rule (closed in 1k by indexing the judgment), and `allocL` (closed
    here). Stage 1k opened one more, the exact loop rule, closed in 1l by widening.

    What remains is not conservatism but *scope*: `UCmd` has no strings, so the
    injection and path-traversal rows are still inexpressible on this machine, and the
    bundle's other certificates (budget, mediation, ledger) are carried by `UCert`
    rather than by `JSecTy`. Uniting those two judgments is the next structural step,
    and unlike every step since 1h it is not forced by a counterexample — the two are
    independent, as stages 1c–1e established, so it is packaging rather than
    discovery. -/

end ConfTyping
