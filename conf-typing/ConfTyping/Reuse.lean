/-
  Stage 1u: the allocator reuses addresses — and that opens a channel.

  Stage 1t found that `uexec`'s allocator only ever advanced a counter, so a freed
  address was never handed out again, and that stage 1i's use-after-free result quietly
  depended on it. Real allocators reuse. This makes ours reuse: `free` puts the address
  on a free list, `alloc` takes from the free list before touching the counter.

  **What survived.** The separation argument. I expected it to need rebuilding, and it
  did not — it needed two more conjuncts in `SepInv`:

  * every freed address is **not live** (`memInt a s.freed → memInt a s.live = false`),
  * every freed address is below the counter.

  With those, `alloc` still hands out an address distinct from every tracked one: from
  the free list by disjointness, from the counter by freshness. The old proof used only
  the second route, so the new one is a genuine case split rather than a re-derivation.
  `stale_pointer_refused_after_reuse` shows the ABA hazard is handled: after
  `alloc p; free p; alloc q`, the two variables hold **the same address**, `q` is usable
  and `p` is refused — the stale pointer is rejected even though its address is live
  again, which is exactly what a reusing allocator makes dangerous.

  **What did not survive: a new leak.** With reuse, the free list decides the next
  address. Freeing a **High** pointer therefore makes the two runs' allocators diverge,
  and the next allocation into a Low variable publishes the difference.
  `freeing_a_secret_pointer_leaks` is the witness: two Low-equal states whose secret
  pointers hold 5 and 7, one `free` and one `alloc`, and a Low variable ends up holding
  5 in one run and 7 in the other.

  So `JSecTy.free` gains a hypothesis it did not need before — `P x = false`, the
  pointer being freed must be Low — and all three checkers gained the test. Under the
  old non-reusing allocator that hypothesis was unnecessary, which is why it was absent.
  Making the model more realistic did not weaken a proof; it revealed a rule that had
  been missing because the model was too kind.

  One consequence worth stating plainly: stage 1t recorded "the allocator never reuses"
  as a *limitation*. It was also load-bearing. Removing a limitation cost a new typing
  restriction, and that is the honest exchange rate.
-/
import ConfTyping.Attack

namespace ConfTyping

/-! ## Reuse is real -/

/-- Allocate, free, allocate again. -/
def aba : UCmd :=
  .seq (.memop .alloc "p") (.seq (.memop .free "p") (.memop .alloc "q"))

/-- **The allocator reuses.** After `alloc p; free p; alloc q` the two variables hold
    *the same address*, the free list is empty again, and the counter advanced only
    once. Under the stage-1t allocator `q` would have been a fresh address. -/
theorem the_allocator_reuses :
    ((uexec 7 aba (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.store "p", r.1.store "q", r.1.live, r.1.freed, r.1.fresh)))
      = some (0, 0, [0], [], 1) := by decide

/-- **And the ABA hazard is handled.** The reused address is live again, so the naive
    reading of "is this address allocated?" would accept the stale pointer `p`. The
    tracked set does not: `p` left it at the `free`, so `deref p` is refused while
    `deref q` — the same address, reached through the live pointer — is accepted. -/
theorem stale_pointer_refused_after_reuse :
    slcheck [] (.seq aba (.memop .deref "q")) = some ["q"]
  ∧ slcheck [] (.seq aba (.memop .deref "p")) = none := by decide

/-! ## The channel reuse opens -/

/-- Two states agreeing on everything Low, whose *secret* pointers hold different live
    addresses. -/
def ptrFive : UState :=
  { store := fun y => if y == "secret" then 5 else 0, auth := [], reads := [],
    dead := false, heap := fun _ => 0, live := [5], fresh := 8, err := false,
    freed := [], hlab := fun _ => false, sstore := fun _ => [], sink := [] }

def ptrSeven : UState :=
  { store := fun y => if y == "secret" then 7 else 0, auth := [], reads := [],
    dead := false, heap := fun _ => 0, live := [7], fresh := 8, err := false,
    freed := [], hlab := fun _ => false, sstore := fun _ => [], sink := [] }

theorem ptr_states_lowEqA : uLowEqA Psec ptrFive ptrSeven := by
  refine ⟨?_, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
  intro y hy
  show (if y == "secret" then (5 : Int) else 0) = (if y == "secret" then (7 : Int) else 0)
  have : ¬ (y == "secret") = true := by simpa [Psec] using hy
  simp [this]

theorem ptr_states_sepInv : SepInv ["secret"] ptrFive ∧ SepInv ["secret"] ptrSeven := by
  have mk : ∀ (t : UState) (v : Int), t.err = false → t.dead = false →
      t.store "secret" = v → t.live = [v] → t.freed = [] → v < t.fresh →
      SepInv ["secret"] t := by
    intro t v he _ hs hl hf hv
    refine ⟨he, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · intro x hx
      rcases List.mem_cons.mp hx with h | h
      · subst h; rw [hs, hl]; simp [memInt]
      · simp at h
    · intro x hx y hy hne
      rcases List.mem_cons.mp hx with h | h
      · rcases List.mem_cons.mp hy with h' | h'
        · exact absurd (h.trans h'.symm) hne
        · simp at h'
      · simp at h
    · intro a ha
      rw [hl] at ha
      have : v = a := by simpa [memInt] using ha
      omega
    · intro a ha; rw [hf] at ha; simp [memInt] at ha
    · intro a ha; rw [hf] at ha; simp [memInt] at ha
  exact ⟨mk ptrFive 5 rfl rfl rfl rfl rfl (by decide),
         mk ptrSeven 7 rfl rfl rfl rfl rfl (by decide)⟩

/-- Free the secret pointer, then allocate into a public one. -/
def freeThenAlloc : UCmd := .seq (.memop .free "secret") (.memop .alloc "pub")

/-- **The leak reuse introduces.** Both states are Low-equal and memory-safe, and both
    runs are memory-safe throughout. But the freed address goes on the free list and is
    handed straight back out, so the *public* variable ends up holding the secret's old
    address: 5 in one run, 7 in the other. Nothing about this is a fault — it is a
    perfectly well-behaved program leaking through the allocator. -/
theorem freeing_a_secret_pointer_leaks :
    uLowEqA Psec ptrFive ptrSeven
  ∧ ((uexec 5 freeThenAlloc (fun _ => true) ptrFive).map (fun r => r.1.store "pub"))
      = some 5
  ∧ ((uexec 5 freeThenAlloc (fun _ => true) ptrSeven).map (fun r => r.1.store "pub"))
      = some 7
  ∧ Psec "pub" = false :=
  ⟨ptr_states_lowEqA, by decide, by decide, by decide⟩

/-- **So the rule had to change — and stage 1z changed it back.** At stage 1u freeing
    was restricted to Low pointers, because the freed address went straight onto the
    observed free list. Stage 1z retires secret addresses instead of recycling them, so
    the restriction is no longer needed and `free` carries no level condition.

    The witness above did not become false — it is a statement about two concrete
    states. What changed is that those states are **unreachable by a checked program**:
    `ptrFive` has a *secret* pointer aimed at a cell labelled public, which is exactly
    what `LabInv` forbids. So the leak is real in the model that admits such a state,
    and stage 1w's invariant is what rules it out. -/
theorem the_leaking_state_violates_the_label_invariant :
    ¬ LabInv Psec ["secret"] ptrFive := by
  intro h
  have := h rfl "secret" (by simp)
  revert this
  decide

/-- With secret addresses retired, freeing needs no level condition at all. -/
theorem free_needs_no_level_condition :
    jcheck Psec ["secret"] freeThenAlloc = some ["pub"]
  ∧ jcheck Psec ["pub"] (.seq (.memop .free "pub") (.memop .alloc "other"))
      = some ["other"] := by decide

/-- And the restriction is exactly what closes the witness above: the leaking program is
    refused, while the five-certificate worked program — which frees a public buffer —
    is unaffected. -/
theorem the_fix_is_targeted :
    allcheck Psec [] [] fiveProg = some (["db"], [], 6)
  ∧ jcheck Psec [] safeHeapProg = some [] := by decide

/-! ## The exchange rate

    Stage 1t recorded "the allocator never reuses" as a limitation. It was also
    load-bearing: removing it cost one new typing restriction (`P x = false` on `free`)
    and two new invariant conjuncts, and bought a model in which the ABA hazard is real
    and handled.

    Nothing that was proved became false. `SepInv` grew, `JSecTy.free` grew a
    hypothesis, and one worked program (`safeHeapProg`) had to allocate through a public
    variable instead of a secret one — because under a reusing allocator, freeing a
    secret pointer is genuinely unsafe rather than merely unmodelled. -/

/-- The invariant that carries the whole thing: a freed address is not live. Stated
    here because it is the one conjunct a reader would not predict, and the one the
    `alloc` proof splits on. -/
theorem freed_and_live_are_disjoint {V : List String} {s : UState}
    (h : SepInv V s) (hd : s.dead = false) :
    ∀ a : Int, memInt a s.freed = true → memInt a s.live = false :=
  (h.2 hd).2.2.2.1

end ConfTyping
