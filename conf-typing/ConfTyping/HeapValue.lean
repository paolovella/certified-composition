/-
  Stage 1v: the heap gets real load and store — and becomes public.

  Stage 1t's second finding was that `uexec` never read or wrote the `heap` field, so
  "memory safety" meant the liveness of addresses and nothing about stored values, while
  a `heap : Int → Int` field in `UState` implied more. This gives the heap real
  operations: `load d p` is `d := *p`, `store p v` is `*p := v`, and both fault if the
  pointer is not live.

  **What it cost, in the same shape as stage 1u.** Memory safety extended without
  difficulty — `SepCert.load` and `SepCert.store` need the pointer tracked and nothing
  else, because the separation invariant never mentioned heap *contents*. Noninterference
  did not extend for free: once a value can travel from the heap into the store, the heap
  is part of what an adversary sees, so `uLowEqA` gained `s.heap = s'.heap` and three
  rules appeared where there had been none:

  * `loadL` — through a **Low** pointer the loaded value is Low, so any destination will
    do;
  * `loadH` — through a **High** pointer the address is unpredictable, so the
    destination must be High;
  * `storeL` — storing needs **both** operands Low, and there is deliberately no High
    counterpart.

  That last absence is the finding. Making the whole heap Low-observable is the simplest
  sound choice, and its consequence is that **the heap is a public resource**:
  `storing_a_secret_is_refused` shows a secret value cannot be written to it at all.
  That is more restrictive than a real system needs, and the honest way to lift it is
  per-address labels — a heap of *labelled* cells, with the label consulted at both ends
  — which is a different design rather than another rule. Naming it beats pretending the
  present rule set is the last word.

  `the_heap_is_live` is the witness that stage 1t's `heap_is_never_touched` no longer
  holds: allocate, store 42, load it back, and 42 comes back.
-/
import ConfTyping.Reuse

namespace ConfTyping

/-! ## The heap holds values now -/

/-- Allocate, write 42 through the pointer, read it back. -/
def roundTrip : UCmd :=
  .seq (.memop .alloc "p")
   (.seq (.assign "v" (.num 42))
    (.seq (.hop .store "p" "v") (.hop .load "d" "p")))

/-- **Stage 1t's defect 2, closed.** The heap is no longer a fiction: a value written
    through a pointer comes back when it is read, and nothing faults. The theorem
    `heap_is_never_touched` that used to stand here is now false, which is the point. -/
theorem the_heap_is_live :
    ((uexec 9 roundTrip (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.store "d", r.1.err))) = some (42, false) := by decide

/-- And the round trip is certified on both counts — memory-safe and noninterferent. -/
theorem roundTrip_certified :
    slcheck [] roundTrip = some ["p"] ∧ jcheck Psec [] roundTrip = some ["p"] := by decide

/-! ## Faults, and the analysis that rules them out -/

/-- Storing through a pointer that was never allocated faults, exactly as a wild
    dereference does — so the two new operations really can go wrong. -/
theorem wild_store_faults :
    ((uexec 2 (.hop .store "p" "v") (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.dead))) = some (true, true) := by decide

theorem wild_store_rejected : slcheck [] (.hop .store "p" "v") = none := by decide

/-! ## The heap is public, and that is a real restriction -/

/-- **The finding, as it stood at stage 1v.** The whole heap was in the observation, so
    writing a secret into it would make the two runs' heaps differ; there was no
    `storeH` rule, and a secret value could not be put in the heap at all.

    **Stage 1x narrowed this.** With per-address labels the heap is two-level, and a
    secret *can* be stored — through a secret pointer
    (`HeapSecret.secret_through_a_secret_pointer`). The statement below survived
    unchanged because its pointer is public, and a public pointer points at a public
    cell; what changed is that it is now a boundary rather than a blanket ban. -/
theorem storing_a_secret_is_refused :
    jcheck Psec ["p"] (.hop .store "p" "secret") = none := by decide

/-- Storing a *public* value through a public pointer is fine, so the restriction is
    aimed at the flow and not at the operation. -/
theorem storing_a_public_value_is_fine :
    jcheck Psec ["p"] (.hop .store "p" "v") = some ["p"] := by decide

/-- **Loading through a secret pointer taints the destination.** The address is
    unpredictable, so the value read may differ between runs: a public destination is
    refused and a secret one is accepted. This is `loadH` doing work — the rule exists
    precisely so that secret pointers remain usable without leaking. -/
theorem secret_pointer_needs_a_secret_destination :
    jcheck Psec ["secret"] (.hop .load "pub" "secret") = none
  ∧ jcheck Psec ["secret"] (.hop .load "secret" "secret") = some [] := by decide

/-- The three together: what the heap being public does and does not forbid. -/
theorem the_heap_is_a_public_resource :
    jcheck Psec ["p"] (.hop .store "p" "secret") = none
  ∧ jcheck Psec ["p"] (.hop .store "p" "v") = some ["p"]
  ∧ jcheck Psec ["secret"] (.hop .load "pub" "secret") = none
  ∧ jcheck Psec ["secret"] (.hop .load "secret" "secret") = some [] := by decide

/-! ## Scope

    Making the entire heap Low-observable is the simplest sound choice and it is
    genuinely restrictive: no secret may be stored, whatever the address. Lifting that
    needs a **label per address** — a heap of labelled cells, with the label read at the
    `load` and checked at the `store` — which changes the state and the observation
    rather than adding a rule, so it is a stage of its own and is not attempted here.

    What did *not* need changing is worth noting too. `SepCert` never mentioned heap
    contents, so memory safety extended to `load` and `store` with two short proofs and
    no new invariant. The two properties reacted very differently to the same change,
    which is the same lesson stages 1j and 1q taught from the other direction. -/

/-- Memory safety needed nothing new: the separation invariant never mentioned heap
    contents, so both operations reduce to "the pointer is tracked". -/
theorem memory_safety_extended_for_free :
    (∀ (V : List String) (d p : String), memStr p V = true →
        SepCert V (.hop .load d p) (dropStr d V))
  ∧ (∀ (V : List String) (p v : String), memStr p V = true →
        SepCert V (.hop .store p v) V) :=
  ⟨fun V d p hp => SepCert.load d p hp, fun V p v hp => SepCert.store p v hp⟩

end ConfTyping
