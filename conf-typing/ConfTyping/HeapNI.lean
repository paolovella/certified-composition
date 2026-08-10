/-
  The composable core, stage 1j: noninterference for the heap — and the first place
  where two certificates do not factor.

  Stage 1h left `memops_not_yet_NI_typed` as the standing limit, with a reason: `alloc`
  writes the fresh-address counter into the observable store. That reason was right
  only for a *Low* target, and this stage corrects it. Three findings, in increasing
  order of interest.

  **1. High allocation is free.** `fresh` and `live` are not in the observation, so
  allocating into a **High** variable is invisible: `USecTy.allocH` is sound with no
  change to `uLowEq` at all. Stage 1h's blanket statement has been narrowed
  accordingly, and `heapProg_two_certificates` is the first heap program carrying both
  the noninterference certificate and the memory certificate at once.

  **2. Low allocation is the open design question, not the closed one.**
  `allocL_would_be_unsound` exhibits two Low-equal states with different allocation
  counters: allocate into a Low variable and they are no longer Low-equal. Typing that
  needs `fresh` in the observation — the "are addresses public?" question — which is a
  decision about the adversary, not a proof obligation, and is left open deliberately.

  **3. `deref` and `free` can never have an unconditional rule — and the reason is not
  the one stage 1h gave.** They can **fault**; a fault sets `dead`; and `dead` is
  observable. `deref_leaks_through_dead` shows a Low-equal pair separated by a single
  `deref` whose target is a High variable. No refinement of a *syntactic* typing
  judgment fixes this, because whether the step faults is a property of the state.

  What it does have is `deref_NI_given_safety`: `deref` **is** noninterferent on states
  satisfying the memory invariant. The hypothesis is literally the other certificate.

  That is the finding worth the module. Stages 1c–1e established four accumulation laws
  with *no interaction term* — budgets add, authorization threads, ledgers append,
  noninterference conjoins — and `Bridge.pair_comp_cert` was read as saying carrying `n`
  properties costs `n` independent accumulations. For the heap that is false:
  noninterference of `deref` is **conditional on memory safety**, so the two cannot be
  established side by side and conjoined at the end. `ni_and_memory_do_not_factor`
  states both halves together.

  The consequence for the next stage is concrete rather than vague: a combined checker
  cannot be `ucheckNI P c && slcheck V c`. The judgment has to be *indexed by the
  tracked set*, so that the NI rule for `deref x` can require `x ∈ V` — which is a new
  inductive, not a conjunction of the two existing ones. That is a design conclusion
  reached by finding a counterexample rather than by preference.
-/
import ConfTyping.MemLinear

namespace ConfTyping

/-! ## Two states, Low-equal, differing only where it matters -/

/-- Low-equal to `noAlloc'`, but with a different allocation counter. -/
def noAlloc : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false,
    heap := fun _ => 0, live := [], fresh := 0, err := false, sstore := fun _ => [], sink := []  }

/-- The same Low state, seven allocations later. -/
def noAlloc' : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false,
    heap := fun _ => 0, live := [], fresh := 7, err := false, sstore := fun _ => [], sink := []  }

/-- A state whose *secret* holds a live pointer. -/
def ptrInSecret : UState :=
  { store := fun y => if y == "secret" then 5 else 0, auth := [], reads := [],
    dead := false, heap := fun _ => 0, live := [5], fresh := 6, err := false, sstore := fun _ => [], sink := []  }

/-- Low-indistinguishable from it, but the secret is not a pointer. -/
def ptrInSecret' : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false,
    heap := fun _ => 0, live := [5], fresh := 6, err := false, sstore := fun _ => [], sink := []  }

theorem noAlloc_lowEq : uLowEq Psec noAlloc noAlloc' :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

theorem ptrInSecret_lowEq : uLowEq Psec ptrInSecret ptrInSecret' := by
  refine ⟨?_, rfl, rfl⟩
  intro y hy
  show (if y == "secret" then (5 : Int) else 0) = 0
  have : ¬ (y == "secret") = true := by simpa [Psec] using hy
  simp [this]

/-! ## 1. High allocation is free -/

/-- **Allocation into a High variable is noninterferent**, with no change to the
    observation: the address written is the allocation counter, which the Low adversary
    cannot see, and it lands in a variable the Low adversary cannot see either. -/
theorem alloc_high_NI {P : Partition} (x : String) (hx : P x = true) :
    ∀ (n : Nat) (π : MedPolicy) (s s' : UState), uLowEq P s s' →
      uOptLowEq P (uexec n (.memop .alloc x) π s) (uexec n (.memop .alloc x) π s') :=
  fun n π s s' hle => usecTy_sound n _ (.allocH x hx) π s s' hle

/-- The stage-1c handler with a High allocation appended: the first program on this
    machine to carry the **noninterference** certificate and the **memory** certificate
    at the same time. -/
def heapProg : UCmd := .seq (.assign "x" (.num 1)) (.memop .alloc "secret")

theorem heapProg_two_certificates :
    ucheckNI Psec heapProg = true ∧ slcheck [] heapProg = some ["secret"] := by decide

/-- Spelled out: both guarantees, on the same program, from the two checkers. -/
theorem heapProg_NI_and_safe :
    (∀ (n : Nat) (π : MedPolicy) (s s' : UState), uLowEq Psec s s' →
        uOptLowEq Psec (uexec n heapProg π s) (uexec n heapProg π s'))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n heapProg π (initU σ) = some r → r.1.err = false) :=
  ⟨uNI_of_check heapProg_two_certificates.1,
   slcheck_no_fault heapProg_two_certificates.2⟩

/-! ## 2. Low allocation is the open question -/

/-- **`allocL` is not derivable, and here is why.** Two Low-equal states may sit at
    different points of the allocation sequence; allocating into a *Low* variable
    publishes that difference. Typing this needs `fresh` in the observation — which is
    a decision about what the adversary can see, not a missing lemma. -/
theorem allocL_would_be_unsound :
    ∃ r r' : UState × Nat × List Bool,
      uLowEq Psec noAlloc noAlloc'
    ∧ Psec "p" = false
    ∧ uexec 1 (.memop .alloc "p") (fun _ => true) noAlloc = some r
    ∧ uexec 1 (.memop .alloc "p") (fun _ => true) noAlloc' = some r'
    ∧ ¬ lowEq Psec r.1.store r'.1.store := by
  refine ⟨_, _, noAlloc_lowEq, rfl, rfl, rfl, ?_⟩
  intro h
  have := h "p" rfl
  revert this
  decide

/-! ## 3. Deref and free: no unconditional rule, ever -/

/-- **The leak stage 1h did not name.** `deref` on a High variable faults in one run
    and not the other; the fault sets `dead`; `dead` is observable. So no *syntactic*
    typing rule for `deref` can be sound, at any security level — whether the step
    faults is a property of the state, not of the program text. -/
theorem deref_leaks_through_dead :
    ∃ r r' : UState × Nat × List Bool,
      uLowEq Psec ptrInSecret ptrInSecret'
    ∧ uexec 1 (.memop .deref "secret") (fun _ => true) ptrInSecret = some r
    ∧ uexec 1 (.memop .deref "secret") (fun _ => true) ptrInSecret' = some r'
    ∧ r.1.dead = false ∧ r'.1.dead = true
    ∧ ¬ uLowEq Psec r.1 r'.1 := by
  refine ⟨_, _, ptrInSecret_lowEq, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  have := h.2.2
  revert this
  decide

/-- **But `deref` is noninterferent on memory-safe states.** If both runs satisfy the
    memory invariant with `x` tracked, neither faults, so the step is a no-op on the
    observation. The hypothesis is stage 1h's certificate, used as a premise. -/
theorem deref_NI_given_safety {P : Partition} {V : List String} {x : String}
    (hx : memStr x V = true) (m : Nat) (π : MedPolicy) (s s' : UState)
    (hs : MemInv V s) (hs' : MemInv V s') (hle : uLowEq P s s') :
    uOptLowEq P (uexec (m+1) (.memop .deref x) π s)
                (uexec (m+1) (.memop .deref x) π s') := by
  obtain ⟨hst, hrd, hdd⟩ := hle
  simp only [uexec]
  refine ⟨?_, rfl, rfl⟩
  by_cases hd : s.dead = true
  · have hd' : s'.dead = true := by rwa [hdd] at hd
    rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
  · have hd0 : s.dead = false := by simpa using hd
    have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
    have hd0' : s'.dead = false := by simpa using hd'
    have hl : memInt (s.store x) s.live = true := hs.2 hd0 x (memStr_mem hx)
    have hl' : memInt (s'.store x) s'.live = true := hs'.2 hd0' x (memStr_mem hx)
    rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
    exact ⟨hst, hrd, hdd⟩

/-- The same for `free`: it edits `live`, which is not observed, and leaves the store,
    the reads and the fault flag alone — *provided* it does not fault, which is again
    the memory certificate. -/
theorem free_NI_given_safety {P : Partition} {V : List String} {x : String}
    (hx : memStr x V = true) (m : Nat) (π : MedPolicy) (s s' : UState)
    (hs : MemInv V s) (hs' : MemInv V s') (hle : uLowEq P s s') :
    uOptLowEq P (uexec (m+1) (.memop .free x) π s)
                (uexec (m+1) (.memop .free x) π s') := by
  obtain ⟨hst, hrd, hdd⟩ := hle
  simp only [uexec]
  refine ⟨?_, rfl, rfl⟩
  by_cases hd : s.dead = true
  · have hd' : s'.dead = true := by rwa [hdd] at hd
    rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
  · have hd0 : s.dead = false := by simpa using hd
    have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
    have hd0' : s'.dead = false := by simpa using hd'
    have hl : memInt (s.store x) s.live = true := hs.2 hd0 x (memStr_mem hx)
    have hl' : memInt (s'.store x) s'.live = true := hs'.2 hd0' x (memStr_mem hx)
    rw [if_neg hd, if_neg hd', if_pos hl, if_pos hl']
    exact ⟨hst, hrd, hdd⟩

/-! ## The finding -/

/-- **The two certificates do not factor.** Both halves in one statement: there is no
    unconditional noninterference rule for `deref` — a Low-equal pair is separated by a
    single step — and yet `deref` is noninterferent whenever the *memory* certificate
    holds of both states.

    Stages 1c–1e built four accumulation laws with no interaction term, and that
    generalised as far as four. It does not generalise to the heap: NI for `deref` is
    conditional on memory safety, so the two properties cannot be certified
    independently and conjoined at the end. Concretely, a combined checker cannot be
    `ucheckNI P c && slcheck V c`; the judgment must be *indexed by the tracked set* so
    that the NI rule for `deref x` can demand `x ∈ V`. That is a new inductive, not a
    conjunction — a design conclusion forced by a counterexample. -/
theorem ni_and_memory_do_not_factor :
    (∃ r r' : UState × Nat × List Bool,
        uLowEq Psec ptrInSecret ptrInSecret'
      ∧ uexec 1 (.memop .deref "secret") (fun _ => true) ptrInSecret = some r
      ∧ uexec 1 (.memop .deref "secret") (fun _ => true) ptrInSecret' = some r'
      ∧ ¬ uLowEq Psec r.1 r'.1)
  ∧ (∀ (P : Partition) (V : List String) (x : String), memStr x V = true →
      ∀ (m : Nat) (π : MedPolicy) (s s' : UState), MemInv V s → MemInv V s' →
        uLowEq P s s' →
        uOptLowEq P (uexec (m+1) (.memop .deref x) π s)
                    (uexec (m+1) (.memop .deref x) π s')) := by
  refine ⟨?_, fun P V x hx m π s s' hs hs' hle => deref_NI_given_safety hx m π s s' hs hs' hle⟩
  obtain ⟨r, r', h1, h2, h3, _, _, h6⟩ := deref_leaks_through_dead
  exact ⟨r, r', h1, h2, h3, h6⟩

/-- And the counterexample is not an artefact of a badly chosen partition: the same
    `deref` is perfectly noninterferent once the pointer is tracked. `ptrInSecret'` is
    exactly the state that fails `MemInv ["secret"]`. -/
theorem the_leaking_state_is_the_unsafe_one :
    MemInv ["secret"] ptrInSecret ∧ ¬ MemInv ["secret"] ptrInSecret' := by
  constructor
  · refine ⟨rfl, fun _ y hy => ?_⟩
    rcases List.mem_cons.mp hy with h | h
    · subst h; decide
    · simp at h
  · rintro ⟨-, hv⟩
    have := hv rfl "secret" (by simp)
    revert this
    decide

end ConfTyping
