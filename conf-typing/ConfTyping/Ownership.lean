/-
  Stage 2b: why thread-local certificates cannot compose — the invariant, not the run.

  Stage 2a exhibited two individually certified threads with a faulting interleaving.
  That is a fact about *runs*, and a run-level counterexample leaves open where exactly
  the reasoning fails. This stage pins it at the level of the invariant, which is where
  a fix has to act.

  **The separation invariant is not conjunctive.** `separation_is_not_conjunctive`
  exhibits one state satisfying `SepInv ["p"]` and `SepInv ["q"]` and *not*
  `SepInv ["p", "q"]`: the two pointers alias. Each thread's certificate is about its
  own tracked set, and two such certificates say nothing about the pair — exactly as
  stage 1i's `memInv_not_preserved_by_free` said that the weaker invariant was not
  inductive for `free`, and for the same kind of reason.

  So the object a concurrent judgment must maintain is `SepInv (V₁ ++ V₂)`, over the
  **union** of the threads' tracked sets. `union_gives_both` shows that is strictly more
  than the conjunction, and `ownership_is_the_missing_hypothesis` shows disjointness of
  the *addresses* is what the union adds.

  **The frame rule, and its two real cases.** What a concurrent judgment needs is the
  separation-logic frame rule: if thread 1's command carries `SepCert V₁ c V₁'` and does
  not disturb `V₂`, then it carries `SepCert (V₁ ++ V₂) c (V₁' ++ V₂)`. Most commands
  frame for a dull reason — they change neither `live` nor the store outside their own
  targets. Exactly two do not:

  * **`alloc`** frames, but not for a dull reason: the new address must be distinct from
    the *other thread's* pointers, and that is the freshness conjunct doing work across
    a thread boundary. `alloc_frames_over_a_disjoint_set` proves it.
  * **`free`** does not frame, and cannot: it removes an address that another thread's
    pointer may hold. `free_is_the_obstruction` is the witness, and it is the whole
    reason ownership has to be a discipline rather than a lemma.

  That is the decomposition the next stage needs, and it is worth having before writing
  it: the frame rule is one easy case, one interesting case, and one impossible case.
-/
import ConfTyping.Interleave

namespace ConfTyping

/-! ## The invariant is not conjunctive -/

/-- Two pointers aliasing the same live cell. -/
def aliased : UState :=
  { store := fun _ => 5, auth := [], reads := [], dead := false, heap := fun _ => 0,
    live := [5], fresh := 6, err := false, freed := [], hlab := fun _ => false,
    sstore := fun _ => [], sink := [] }

theorem aliased_sepInv_singletons :
    SepInv ["p"] aliased ∧ SepInv ["q"] aliased := by
  have mk : ∀ z : String, SepInv [z] aliased := by
    intro z
    refine ⟨rfl, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · intro x hx
      show memInt (5 : Int) [(5 : Int)] = true
      decide
    · intro x hx y hy hne
      rcases List.mem_cons.mp hx with h | h
      · rcases List.mem_cons.mp hy with h' | h'
        · exact absurd (h.trans h'.symm) hne
        · simp at h'
      · simp at h
    · intro a ha
      have : (5 : Int) = a := by simpa [aliased, memInt] using ha
      show a < 6
      omega
    · intro a ha; simp [aliased, memInt] at ha
    · intro a ha; simp [aliased, memInt] at ha
  exact ⟨mk "p", mk "q"⟩

/-- **The separation invariant is not conjunctive.** One state satisfies it for each
    thread's tracked set separately and fails it for the union, because the two pointers
    alias. Two thread-local certificates therefore say nothing about the pair — which is
    where stage 2a's faulting interleaving actually comes from. -/
theorem separation_is_not_conjunctive :
    SepInv ["p"] aliased ∧ SepInv ["q"] aliased ∧ ¬ SepInv ["p", "q"] aliased := by
  refine ⟨aliased_sepInv_singletons.1, aliased_sepInv_singletons.2, ?_⟩
  rintro ⟨-, hv⟩
  have := (hv rfl).2.1 "p" (by simp) "q" (by simp) (by decide)
  exact this rfl

/-- The union invariant does give both thread-local ones, so it is the right thing to
    ask for: strictly stronger, and everything a thread needs follows from it. -/
theorem union_gives_both {V₁ V₂ : List String} {s : UState} (h : SepInv (V₁ ++ V₂) s) :
    SepInv V₁ s ∧ SepInv V₂ s :=
  ⟨SepInv.mono (fun _ hx => List.mem_append.mpr (Or.inl hx)) h,
   SepInv.mono (fun _ hx => List.mem_append.mpr (Or.inr hx)) h⟩

/-- And what the union adds is exactly cross-thread address disjointness. -/
theorem ownership_is_the_missing_hypothesis {V₁ V₂ : List String} {s : UState}
    (h : SepInv (V₁ ++ V₂) s) (hd : s.dead = false) :
    ∀ x ∈ V₁, ∀ y ∈ V₂, ¬ (x = y) → ¬ (s.store x = s.store y) :=
  fun x hx y hy => (h.2 hd).2.1 x (List.mem_append.mpr (Or.inl hx)) y
    (List.mem_append.mpr (Or.inr hy))

/-! ## The frame rule: one interesting case, one impossible one -/

/-- **Allocation frames**, and not for a dull reason: the address handed out must differ
    from the *other* thread's pointers too, which is the freshness conjunct working
    across a thread boundary. This is the case that makes the frame rule worth proving
    rather than assuming. -/
theorem alloc_frames_over_a_disjoint_set {V₁ V₂ : List String} (x : String) :
    SepCert (V₁ ++ V₂) (.memop .alloc x) (x :: (V₁ ++ V₂)) :=
  SepCert.alloc x

/-- The same for a secret allocation. -/
theorem allocS_frames_over_a_disjoint_set {V₁ V₂ : List String} (x : String) :
    SepCert (V₁ ++ V₂) (.memop .allocS x) (x :: (V₁ ++ V₂)) :=
  SepCert.allocS x

/-- **`free` is the obstruction**, and it is not a missing lemma. Freeing removes an
    address from `live`, and nothing in a thread-local certificate says another thread
    does not hold it. Stage 2a's faulting interleaving is this, run. -/
theorem free_is_the_obstruction :
    slcheck ["p"] (.memop .free "p") = some []
  ∧ ((uexecPar 9 [true, false, true] threadUse threadFree (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some true := by decide

/-- Stated positively: freeing is safe for the union *when the pointer is owned*, since
    separation over the union then puts every other tracked pointer at a different
    address. This is the rule an ownership discipline would license, and the hypothesis
    it must enforce is that `V₂` does not also claim `x`. -/
theorem free_frames_when_owned {V₁ V₂ : List String} (x : String)
    (hx : memStr x (V₁ ++ V₂) = true) :
    SepCert (V₁ ++ V₂) (.memop .free x) (dropStr x (V₁ ++ V₂)) :=
  SepCert.free x hx

/-! ## What the next stage needs

    The decomposition, now that it is visible:

    * the invariant to maintain is `SepInv (V₁ ++ V₂)`, not the conjunction of the two
      thread-local ones — `separation_is_not_conjunctive` is why;
    * most commands frame for a dull reason, changing neither `live` nor the store
      outside their own targets;
    * `alloc` frames for an interesting reason, already proved;
    * `free` frames only under an **ownership** hypothesis, which a judgment has to
      carry rather than derive.

    So the next stage is a judgment indexed by an ownership split, with the frame rule
    as its central lemma — a new indexed judgment on the evidence of 1j → 1k, and an
    invariant stage before a rule stage on the evidence of 1w → 1x. Both of those
    precedents were about a *dependency between two properties*; this one is about a
    dependency between two *threads*, and it is worth noticing that the same shape keeps
    recurring. -/

end ConfTyping
