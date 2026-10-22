/-
  The leak gap, closed — the one vulnerability class the map admitted it missed.

  `VULN-COVERAGE.md` row 6 has said, since the external corpus was transcribed:
  *"use-after-free, double-free and wild dereference only. **Leaks (CWE-401) are NOT
  detected**"*, with `corpus/ext/b06` as the witness — a CWE-401 demonstrative
  example that this framework **accepts**:

      alloc buf ; if fail { skip } else { store buf v ; free buf }

  Allocate, take the error path, never free. Every other certificate in the repo
  is happy with it, because none of them is about liveness of allocation.

  This module is the missing certificate. It is admitted under the scoped
  exception recorded in `PLAN-2026-08.md` — **property coverage, not
  expressiveness**: no construct is added to `UCmd`, nothing is made easier to
  write, and the exception may only be invoked by citing a map row that admits a
  gap. Row 6 is that row.

  ── The property ──
  `LeakFree` says a completed run leaves nothing allocated that was not allocated
  before: `s'.live ⊆ s.live`. The state already carries `live`, so this needs no
  new semantics — which is the reason the gap was closeable without touching the
  language.

  ── The checker ──
  `lcheck` tracks the variables currently holding an **unfreed** allocation.
  `alloc` adds, `free` removes, and the two rules that give the checker its teeth
  are the ones that refuse to lose a handle:

  * **writing over a live handle is a leak** — `assign x _` and `load x _` are
    rejected when `x` is tracked, because the address survives and the only
    pointer to it does not;
  * **branches must agree** — `ite` requires both arms to end with the same
    tracked set, which is exactly what catches `b06`: one arm still holds `buf`
    and the other does not;
  * **loops must be a fixpoint** — a body that ends holding more than it started
    with is refused, which is `while c { alloc x }`.

  ── The honest limit, and it is a real one ──
  `LeakFree` quantifies over runs that **complete without aborting**
  (`s'.dead = false`). A run that aborts on a refused `check` *can* leak, and this
  certificate does not exclude that:

      alloc p ; check r ; free p

  is accepted, and leaks whenever the policy refuses `r`. That is not an oversight
  found later — it is why the theorem is stated for completing runs. On the
  refusal path the program has already failed the mediation certificate, and what
  happens to its memory is the runtime's affair; making `lcheck` reject every
  allocation that precedes a `check` would refuse most real handlers to buy a
  guarantee about a path that has already aborted. **Stated here, in the map, and
  guarded, rather than left for a later corpus to find.**
-/
import ConfTyping.CountedLoop

namespace ConfTyping

/-! ## The property -/

/-- Set equality on tracked-variable lists. -/
def eqStr (A B : List String) : Bool := subStr A B && subStr B A

/-- **Leak freedom.** A run that completes without aborting leaves no address
    allocated that was not allocated when it started. -/
def LeakFree (π : MedPolicy) (c : UCmd) : Prop :=
  ∀ (n : Nat) (s s' : UState) (k : Nat) (t : List Bool),
    uexec n c π s = some (s', k, t) → s'.dead = false →
    ∀ a : Int, memInt a s'.live = true → memInt a s.live = true

/-! ## The checker -/

/-- Track the variables holding an allocation that has not been freed. `none` is
    a refusal. -/
def lcheck : List String → UCmd → Option (List String)
  | O, .skip           => some O
  | O, .check _        => some O
  | O, .access _       => some O
  | O, .sop _ _ _      => some O
  | O, .assign x _     => if memStr x O then none else some O
  | O, .hop .load  x _ => if memStr x O then none else some O
  | O, .hop .store _ _ => some O
  | O, .memop .alloc  x => if memStr x O then none else some (x :: O)
  | O, .memop .allocS x => if memStr x O then none else some (x :: O)
  | O, .memop .deref  _ => some O
  | O, .memop .free   x => if memStr x O then some (dropStr x O) else none
  | O, .seq c₁ c₂      => (lcheck O c₁).bind (fun O₁ => lcheck O₁ c₂)
  | O, .ite _ c₁ c₂    =>
      (lcheck O c₁).bind fun O₁ =>
        (lcheck O c₂).bind fun O₂ =>
          if eqStr O₁ O₂ then some O₁ else none
  | O, .loop _ body    =>
      (lcheck O body).bind fun O₁ => if eqStr O₁ O then some O else none

/-- The verdict: nothing outstanding at the start, nothing outstanding at the end. -/
def leakSafe (c : UCmd) : Bool :=
  match lcheck [] c with
  | some O => O.isEmpty
  | none   => false

/-! ## The invariant

Every live address is either one we started with, or is held by a tracked
variable. The `dead` disjunct makes the invariant survive an abort, after which
every command is a no-op. -/

/-- The ownership invariant. -/
def Owned (O : List String) (s₀ s : UState) : Prop :=
  s.dead = true ∨
    ∀ a : Int, memInt a s.live = true →
      memInt a s₀.live = true ∨ ∃ x, memStr x O = true ∧ s.store x = a

theorem memStr_cons {x y : String} {O : List String} (h : memStr x O = true) :
    memStr x (y :: O) = true := by
  simp only [memStr, Bool.or_eq_true]
  exact Or.inr h

/-- The converse of `memStr_mem`, which the repo did not yet have. -/
theorem mem_memStr {r : String} : ∀ {A : List String}, r ∈ A → memStr r A = true
  | [],      h => by cases h
  | x :: xs, h => by
      simp only [memStr, Bool.or_eq_true, beq_iff_eq]
      rcases List.mem_cons.mp h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (mem_memStr h)

/-- Tracked-set containment transports membership. -/
theorem memStr_of_subStr {y : String} {A B : List String}
    (hs : subStr A B = true) (h : memStr y A = true) : memStr y B = true :=
  mem_memStr (subStr_mem hs y (memStr_mem h))

/-- Dropping a *different* variable keeps membership. -/
theorem memStr_dropStr_of_ne {x y : String} : ∀ {O : List String},
    ¬ (y = x) → memStr y O = true → memStr y (dropStr x O) = true
  | [],      _,  h => by simp [memStr] at h
  | z :: zs, hn, h => by
      simp only [memStr, Bool.or_eq_true, beq_iff_eq] at h
      by_cases hz : z = x
      · rw [dropStr, if_pos (by simp [hz])]
        rcases h with h | h
        · exact absurd (hz ▸ h.symm) hn
        · exact memStr_dropStr_of_ne hn h
      · rw [dropStr, if_neg (by simpa using hz)]
        simp only [memStr, Bool.or_eq_true, beq_iff_eq]
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (memStr_dropStr_of_ne hn h)

theorem eqStr_symm {A B : List String} (h : eqStr A B = true) : eqStr B A = true := by
  simp only [eqStr, Bool.and_eq_true] at h ⊢
  exact ⟨h.2, h.1⟩

/-- Transport the invariant across a step that does not grow `live` and does not
    disturb any tracked variable. Most commands are this case. -/
theorem Owned.transport {O : List String} {s₀ s s' : UState} (h : Owned O s₀ s)
    (hd : s.dead = true → s'.dead = true)
    (hlive : ∀ a, memInt a s'.live = true → memInt a s.live = true)
    (hst : ∀ x, memStr x O = true → s'.store x = s.store x) : Owned O s₀ s' := by
  rcases h with hdd | h
  · exact Or.inl (hd hdd)
  · refine Or.inr fun a ha => ?_
    rcases h a (hlive a ha) with h₀ | ⟨y, hy, hs⟩
    · exact Or.inl h₀
    · exact Or.inr ⟨y, hy, by rw [hst y hy]; exact hs⟩

/-- Tracking more variables is always sound. -/
theorem Owned.weaken {O : List String} {x : String} {s₀ s : UState}
    (h : Owned O s₀ s) : Owned (x :: O) s₀ s := by
  rcases h with hd | h
  · exact Or.inl hd
  · refine Or.inr fun a ha => ?_
    rcases h a ha with h₀ | ⟨y, hy, hs⟩
    · exact Or.inl h₀
    · exact Or.inr ⟨y, memStr_cons hy, hs⟩

/-- A set-equal tracked list carries the same invariant. -/
theorem Owned.congr {O O' : List String} {s₀ s : UState}
    (h : Owned O s₀ s) (he : eqStr O O' = true) : Owned O' s₀ s := by
  rcases h with hd | h
  · exact Or.inl hd
  · refine Or.inr fun a ha => ?_
    rcases h a ha with h₀ | ⟨y, hy, hs⟩
    · exact Or.inl h₀
    · refine Or.inr ⟨y, ?_, hs⟩
      simp only [eqStr, Bool.and_eq_true] at he
      exact memStr_of_subStr he.1 hy

/-- Aborting is sticky: once a run is dead every command is a no-op, so the state
    that comes out is dead too. -/
theorem uexec_dead : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s s' : UState)
    (k : Nat) (t : List Bool),
    uexec n c π s = some (s', k, t) → s.dead = true → s'.dead = true := by
  intro n
  induction n with
  | zero => intro c π s s' k t h; simp [uexec] at h
  | succ n ih =>
      intro c π s s' k t h hd
      cases c with
      | seq c₁ c₂ =>
          simp only [uexec] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          rw [e₁, Option.bind_some] at h
          rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
          · rw [e₂] at h; simp at h
          rw [e₂] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, -⟩ := h
          exact hs ▸ ih c₂ π r₁.1 r₂.1 r₂.2.1 r₂.2.2 e₂ (ih c₁ π s r₁.1 r₁.2.1 r₁.2.2 e₁ hd)
      | ite e c₁ c₂ =>
          simp only [uexec] at h
          split at h
          · rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            rw [e₁] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hs, -⟩ := h
            exact hs ▸ ih c₁ π s r₁.1 r₁.2.1 r₁.2.2 e₁ hd
          · rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            rw [e₂] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hs, -⟩ := h
            exact hs ▸ ih c₂ π s r₂.1 r₂.2.1 r₂.2.2 e₂ hd
      | loop e body =>
          simp only [uexec] at h
          split at h
          · rcases e₁ : uexec n body π s with _ | r₁
            · rw [e₁] at h; simp at h
            rw [e₁, Option.bind_some] at h
            rcases e₂ : uexec n (.loop e body) π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            rw [e₂] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hs, -⟩ := h
            exact hs ▸ ih (.loop e body) π r₁.1 r₂.1 r₂.2.1 r₂.2.2 e₂
              (ih body π s r₁.1 r₁.2.1 r₁.2.2 e₁ hd)
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hs, -⟩ := h
            exact hs ▸ hd
      | _ =>
          simp only [uexec, if_pos hd, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hs, -⟩ := h
          exact hs ▸ hd

/-! ## Soundness

The tracked set really does account for every address the run has allocated and
not yet released. -/

theorem lcheck_owned : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (O O' : List String)
    (s₀ s s' : UState) (k : Nat) (t : List Bool),
    lcheck O c = some O' → uexec n c π s = some (s', k, t) →
    Owned O s₀ s → Owned O' s₀ s' := by
  intro n
  induction n with
  | zero => intro c π O O' s₀ s s' k t _ h2 _; simp [uexec] at h2
  | succ n ih =>
      intro c π O O' s₀ s s' k t h1 h2 h3
      cases c with
      | skip =>
          simp only [lcheck, Option.some.injEq] at h1
          simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨hs, -⟩ := h2
          subst h1; subst hs; exact h3
      | check r =>
          simp only [lcheck, Option.some.injEq] at h1
          simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨hs, -⟩ := h2
          subst h1; subst hs
          by_cases hd : s.dead = true
          · exact Or.inl (by simp [hd])
          · simp only [Bool.not_eq_true] at hd
            rw [if_neg (by simp [hd])]
            refine h3.transport ?_ ?_ ?_
            · intro hdd; simp_all
            · intro a ha; split at ha <;> exact ha
            · intro y _; split <;> rfl
      | access r =>
          simp only [lcheck, Option.some.injEq] at h1
          simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨hs, -⟩ := h2
          subst h1; subst hs
          by_cases hd : s.dead = true
          · exact Or.inl (by simp [hd])
          · simp only [Bool.not_eq_true] at hd
            rw [if_neg (by simp [hd])]
            exact h3.transport (fun hdd => by simp_all) (fun _ ha => ha) (fun _ _ => rfl)
      | sop op x e =>
          simp only [lcheck, Option.some.injEq] at h1
          simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨hs, -⟩ := h2
          subst h1; subst hs
          by_cases hd : s.dead = true
          · exact Or.inl (by simp [hd])
          · simp only [Bool.not_eq_true] at hd
            rw [if_neg (by simp [hd])]
            cases op <;>
              exact h3.transport (fun hdd => by simp_all) (fun _ ha => ha) (fun _ _ => rfl)
      | assign x e =>
          simp only [lcheck] at h1
          split at h1
          · simp at h1
          · rename_i hx
            simp only [Option.some.injEq] at h1
            simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
            obtain ⟨hs, -⟩ := h2
            subst h1; subst hs
            by_cases hd : s.dead = true
            · exact Or.inl (by simp [hd])
            · simp only [Bool.not_eq_true] at hd
              rw [if_neg (by simp [hd])]
              refine h3.transport (fun hdd => by simp_all) (fun _ ha => ha) ?_
              intro y hy
              have hne : ¬ (y = x) := by rintro rfl; simp_all
              simp only [upd, if_neg hne]
      | hop op x y =>
          cases op with
          | load =>
              simp only [lcheck] at h1
              split at h1
              · simp at h1
              · rename_i hx
                simp only [Option.some.injEq] at h1
                simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst h1; subst hs
                by_cases hd : s.dead = true
                · exact Or.inl (by simp [hd])
                · simp only [Bool.not_eq_true] at hd
                  rw [if_neg (by simp [hd])]
                  refine h3.transport (fun hdd => by simp_all) ?_ ?_
                  · intro a ha; split at ha <;> exact ha
                  · intro z hz
                    have hne : ¬ (z = x) := by rintro rfl; simp_all
                    split
                    · simp only [upd, if_neg hne]
                    · rfl
          | store =>
              simp only [lcheck, Option.some.injEq] at h1
              simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
              obtain ⟨hs, -⟩ := h2
              subst h1; subst hs
              by_cases hd : s.dead = true
              · exact Or.inl (by simp [hd])
              · simp only [Bool.not_eq_true] at hd
                rw [if_neg (by simp [hd])]
                refine h3.transport (fun hdd => by simp_all) ?_ ?_
                · intro a ha; split at ha <;> exact ha
                · intro z _; split <;> rfl
      | memop op x =>
          cases op with
          | deref =>
              simp only [lcheck, Option.some.injEq] at h1
              simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
              obtain ⟨hs, -⟩ := h2
              subst h1; subst hs
              by_cases hd : s.dead = true
              · exact Or.inl (by simp [hd])
              · simp only [Bool.not_eq_true] at hd
                rw [if_neg (by simp [hd])]
                refine h3.transport (fun hdd => by simp_all) ?_ ?_
                · intro a ha; split at ha <;> exact ha
                · intro z _; split <;> rfl
          | alloc =>
              simp only [lcheck] at h1
              split at h1
              · simp at h1
              · rename_i hx
                simp only [Option.some.injEq] at h1
                simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst h1; subst hs
                by_cases hd : s.dead = true
                · exact Or.inl (by simp [hd])
                · simp only [Bool.not_eq_true] at hd
                  rcases h3 with hdd | h3
                  · exact absurd hdd (by simp [hd])
                  refine Or.inr fun a ha => ?_
                  rw [if_neg (by simp [hd])] at ha
                  simp only [memInt, Bool.or_eq_true, beq_iff_eq] at ha
                  rw [if_neg (by simp [hd])]
                  rcases ha with ha | ha
                  · exact Or.inr ⟨x, by simp [memStr], by simp [upd, ha]⟩
                  · rcases h3 a ha with h₀ | ⟨y, hy, hsy⟩
                    · exact Or.inl h₀
                    · have hne : ¬ (y = x) := by rintro rfl; simp_all
                      exact Or.inr ⟨y, memStr_cons hy, by simp only [upd, if_neg hne]; exact hsy⟩
          | allocS =>
              simp only [lcheck] at h1
              split at h1
              · simp at h1
              · rename_i hx
                simp only [Option.some.injEq] at h1
                simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst h1; subst hs
                by_cases hd : s.dead = true
                · exact Or.inl (by simp [hd])
                · simp only [Bool.not_eq_true] at hd
                  rcases h3 with hdd | h3
                  · exact absurd hdd (by simp [hd])
                  refine Or.inr fun a ha => ?_
                  rw [if_neg (by simp [hd])] at ha
                  simp only [memInt, Bool.or_eq_true, beq_iff_eq] at ha
                  rw [if_neg (by simp [hd])]
                  rcases ha with ha | ha
                  · exact Or.inr ⟨x, by simp [memStr], by simp [upd, ha]⟩
                  · rcases h3 a ha with h₀ | ⟨y, hy, hsy⟩
                    · exact Or.inl h₀
                    · have hne : ¬ (y = x) := by rintro rfl; simp_all
                      exact Or.inr ⟨y, memStr_cons hy, by simp only [upd, if_neg hne]; exact hsy⟩
          | free =>
              simp only [lcheck] at h1
              split at h1
              · rename_i hx
                simp only [Option.some.injEq] at h1
                simp only [uexec, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst h1; subst hs
                by_cases hd : s.dead = true
                · exact Or.inl (by simp [hd])
                · simp only [Bool.not_eq_true] at hd
                  rcases h3 with hdd | h3
                  · exact absurd hdd (by simp [hd])
                  rw [if_neg (by simp [hd])]
                  split
                  · refine Or.inr fun a ha => ?_
                    have hmem : memInt a s.live = true := dropInt_memInt ha
                    have hne : ¬ (a = s.store x) := by
                      rintro rfl
                      rw [memInt_dropInt_self] at ha
                      exact absurd ha (by simp)
                    rcases h3 a hmem with h₀ | ⟨y, hy, hsy⟩
                    · exact Or.inl h₀
                    · have hyx : ¬ (y = x) := by rintro rfl; exact hne hsy.symm
                      exact Or.inr ⟨y, memStr_dropStr_of_ne hyx hy, hsy⟩
                  · exact Or.inl (by simp)
              · simp at h1
      | seq c₁ c₂ =>
          simp only [lcheck] at h1
          rcases l₁ : lcheck O c₁ with _ | O₁
          · rw [l₁] at h1; simp at h1
          rw [l₁, Option.bind_some] at h1
          simp only [uexec] at h2
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h2; simp at h2
          rw [e₁, Option.bind_some] at h2
          rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
          · rw [e₂] at h2; simp at h2
          rw [e₂] at h2
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
          obtain ⟨hs, -⟩ := h2
          subst hs
          exact ih c₂ π O₁ O' s₀ r₁.1 r₂.1 r₂.2.1 r₂.2.2 h1 e₂
            (ih c₁ π O O₁ s₀ s r₁.1 r₁.2.1 r₁.2.2 l₁ e₁ h3)
      | ite e c₁ c₂ =>
          simp only [lcheck] at h1
          rcases l₁ : lcheck O c₁ with _ | O₁
          · rw [l₁] at h1; simp at h1
          rcases l₂ : lcheck O c₂ with _ | O₂
          · rw [l₁, Option.bind_some, l₂] at h1; simp at h1
          rw [l₁, Option.bind_some, l₂, Option.bind_some] at h1
          split at h1
          · rename_i heq
            have hO : O₁ = O' := by injection h1
            have main : Owned O₁ s₀ s' := by
              simp only [uexec] at h2
              split at h2
              · rcases e₁ : uexec n c₁ π s with _ | r₁
                · rw [e₁] at h2; simp at h2
                rw [e₁] at h2
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst hs
                exact ih c₁ π O O₁ s₀ s r₁.1 r₁.2.1 r₁.2.2 l₁ e₁ h3
              · rcases e₂ : uexec n c₂ π s with _ | r₂
                · rw [e₂] at h2; simp at h2
                rw [e₂] at h2
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst hs
                exact (ih c₂ π O O₂ s₀ s r₂.1 r₂.2.1 r₂.2.2 l₂ e₂ h3).congr (eqStr_symm heq)
            exact hO ▸ main
          · simp at h1
      | loop e body =>
          simp only [lcheck] at h1
          rcases lb : lcheck O body with _ | O₁
          · rw [lb] at h1; simp at h1
          rw [lb, Option.bind_some] at h1
          split at h1
          · rename_i heq
            have hO : O = O' := by injection h1
            have main : Owned O s₀ s' := by
              simp only [uexec] at h2
              split at h2
              · rcases e₁ : uexec n body π s with _ | r₁
                · rw [e₁] at h2; simp at h2
                rw [e₁, Option.bind_some] at h2
                rcases e₂ : uexec n (.loop e body) π r₁.1 with _ | r₂
                · rw [e₂] at h2; simp at h2
                rw [e₂] at h2
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst hs
                have hbody : Owned O s₀ r₁.1 :=
                  (ih body π O O₁ s₀ s r₁.1 r₁.2.1 r₁.2.2 lb e₁ h3).congr heq
                have hloop : lcheck O (.loop e body) = some O := by
                  simp only [lcheck, lb, Option.bind_some]; rw [if_pos heq]
                exact ih (.loop e body) π O O s₀ r₁.1 r₂.1 r₂.2.1 r₂.2.2 hloop e₂ hbody
              · simp only [Option.some.injEq, Prod.mk.injEq] at h2
                obtain ⟨hs, -⟩ := h2
                subst hs; exact h3
            exact hO ▸ main
          · simp at h1

/-! ## The certificate -/

/-- **Leak freedom, certified.** A program the checker accepts leaks nothing on
    any run that completes without aborting. -/
theorem leakSafe_sound {c : UCmd} (h : leakSafe c = true) (π : MedPolicy) :
    LeakFree π c := by
  intro n s s' k t hex hnd a ha
  simp only [leakSafe] at h
  rcases lc : lcheck [] c with _ | O
  · rw [lc] at h; simp at h
  rw [lc] at h
  cases O with
  | cons y ys => simp [List.isEmpty] at h
  | nil =>
      have hown : Owned [] s s := Or.inr (fun b hb => Or.inl hb)
      rcases lcheck_owned n c π [] [] s s s' k t lc hex hown with hdd | hres
      · rw [hdd] at hnd; simp at hnd
      · rcases hres a ha with h₀ | ⟨y, hy, -⟩
        · exact h₀
        · simp [memStr] at hy

/-! ## The witness: `corpus/ext/b06`, the CWE-401 example that was accepted -/

/-- `alloc buf ; if fail { skip } else { store buf v ; free buf }` — CWE-401
    example 1, transcribed, and the program the map admitted was accepted. -/
def b06 : UCmd :=
  .seq (.memop .alloc "buf")
       (.ite (.var "fail") .skip
             (.seq (.hop .store "buf" "v") (.memop .free "buf")))

/-- The same program with the error path fixed. -/
def b06fixed : UCmd :=
  .seq (.memop .alloc "buf")
       (.ite (.var "fail") (.memop .free "buf")
             (.seq (.hop .store "buf" "v") (.memop .free "buf")))

/-- **The gap is closed.** The leak is now refused — one arm of the branch still
    holds `buf` and the other does not. -/
theorem b06_rejected : leakSafe b06 = false := by decide

/-- And the repair is accepted, so the rule is not merely refusing everything
    that allocates. -/
theorem b06fixed_accepted : leakSafe b06fixed = true := by decide

/-- `while c { alloc x }` — the unbounded leak — is refused by the fixpoint rule. -/
theorem loop_alloc_rejected :
    leakSafe (.loop (.var "c") (.memop .alloc "x")) = false := by decide

/-- And the balanced loop is **accepted**, so the fixpoint rule is not merely
    refusing every loop. The pair is the `b06`/`b06fixed` discipline applied to
    the rule that had only its negative witnessed: a refusal on its own is
    satisfied by a checker that rejects the whole construct. -/
theorem loop_balanced_accepted :
    leakSafe (.loop (.var "c")
      (.seq (.memop .alloc "x") (.memop .free "x"))) = true := by decide

/-- Overwriting the only handle to a live allocation is refused. -/
theorem overwrite_rejected :
    leakSafe (.seq (.memop .alloc "p") (.assign "p" (.num 0))) = false := by decide

/-! ## The limit, witnessed rather than asserted

The certificate is about runs that complete. This program is **accepted** and
**leaks** when the policy refuses `r` — which is why `LeakFree` says what it says,
and why the map records the restriction. -/

/-- `alloc p ; check r ; free p`. -/
def allocThenCheck : UCmd :=
  .seq (.memop .alloc "p") (.seq (.check "r") (.memop .free "p"))

theorem allocThenCheck_accepted : leakSafe allocThenCheck = true := by decide

end ConfTyping
