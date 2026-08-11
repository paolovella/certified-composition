/-
  Attacking the core (stage 1t): what twenty stages of building missed.

  Every finding from stage 1h onwards came from a counterexample that turned up while
  building something else. That is a poor way to look for defects, because it only finds
  the ones that happen to block the next step. This stage looks on purpose.

  **What survived.** Twelve adversarial programs — laundering a secret through
  concatenation and through sanitisation, branching and looping on a secret,
  use-after-free through an alias, double-free through two names, a path literal that
  escapes, an access without its check — are all refused, and each refusal is recorded
  below rather than asserted. No unsoundness was found in any checker.

  **What did not survive.** Three defects, one of them real:

  1. **The exported noninterference statement was vacuous in its string dimension.**
     `jcheck_gives_both` and `xcheck_gives_five` state noninterference from `initU σ` —
     and `initU` gives every string variable the empty value, so two runs from `initU`
     *cannot differ in a secret string*. Everything proved about the sink was therefore
     true and empty. `jsecTy_sound` was general all along; only the exported wrapper was
     weak, so the fix is `allcheck_NI_general` plus a witness that it does real work.
     This is the same mistake as stage 1o's unobserved sink, made one level up: the
     theorem looked like it covered strings and did not.

  2. **The heap is a fiction.** `uexec` never reads or writes the `heap` field —
     `heap_is_never_touched` proves it. So "memory safety" here means *liveness of
     addresses*, never anything about stored values. That is what `umcheck_no_fault` and
     `slcheck_no_fault` actually say, but a `heap : Int → Int` field sitting in `UState`
     implies more, and implying more is the failure mode this repo exists to avoid.

  3. **The allocator never reuses an address**, and the separation proof *depends* on
     that: `SepInv`'s freshness conjunct is what makes a new pointer provably distinct
     from every tracked one. Real allocators reuse freed addresses, which is precisely
     how use-after-free becomes exploitable rather than merely wrong. So stage 1i's
     CWE-416 result held for a non-reusing allocator, and that hypothesis was never
     written down. **(Fixed in stage 1u: the allocator now reuses. See `Reuse.lean` —
     the separation argument survived with two extra invariant conjuncts, but reuse
     turned the free list into a channel and `free` gained a typing restriction.)**

  None of the three is unsoundness. All three are the guarantee being narrower than its
  name, which is the defect this project treats as most serious.
-/
import ConfTyping.Deploy

namespace ConfTyping

/-! ## Twelve attacks, all refused

    Evidence that the checkers are not permissive in the obvious ways. Each line is an
    attack someone would actually try. -/

theorem attack_leak_string_into_public :
    jcheck Psec [] (.sop .set "pub" (.var "secret")) = none := by decide

theorem attack_emit_the_secret :
    jcheck Psec [] (.sop .emit "db" (.var "secret")) = none := by decide

theorem attack_launder_by_concatenation :
    jcheck Psec [] (.sop .set "pub" (.cat (.lit []) (.var "secret"))) = none := by decide

/-- Sanitising makes a secret *structurally* harmless and keeps it secret; the flow
    rule refuses it. This is `sanitising_does_not_declassify` from the attacker's side. -/
theorem attack_launder_by_sanitising :
    jcheck Psec [] (.sop .set "pub" (.san (.var "secret"))) = none := by decide

theorem attack_branch_on_a_secret :
    jcheck Psec [] (.ite (.var "secret") .skip .skip) = none := by decide

theorem attack_loop_on_a_secret :
    jcheck Psec [] (.loop (.var "secret") .skip) = none := by decide

/-- The classic: make an alias, free the original, use the alias. `assign` drops its
    target from the tracked set, so the alias was never usable. -/
theorem attack_use_after_free_via_alias :
    slcheck [] (.seq (.memop .alloc "p")
                (.seq (.assign "q" (.var "p"))
                 (.seq (.memop .free "p") (.memop .deref "q")))) = none := by decide

theorem attack_free_through_a_second_name :
    slcheck [] (.seq (.memop .alloc "p")
                (.seq (.assign "q" (.var "p")) (.memop .free "q"))) = none := by decide

/-- A variable known to contain *one* parent segment is refused for a path, because the
    analysis tracks a lower bound on depth and cannot rule out the pop landing first. -/
theorem attack_path_from_a_nonzero_variable :
    pcheck "fs" [("u", 1)] (.sop .emit "fs" (.cat (.lit [.ord]) (.var "u"))) = none := by
  decide

theorem attack_escaping_literal :
    pcheck "fs" [] (.sop .emit "fs" (.lit [.ord, .quote, .quote])) = none := by decide

theorem attack_access_without_check :
    allcheck Psec [] [] (.access "db") = none := by decide

theorem attack_check_the_wrong_resource :
    allcheck Psec [] [] (.seq (.check "log") (.access "db")) = none := by decide

/-- All twelve in one place, so the list cannot quietly shrink. -/
theorem twelve_attacks_refused :
    jcheck Psec [] (.sop .set "pub" (.var "secret")) = none
  ∧ jcheck Psec [] (.sop .emit "db" (.var "secret")) = none
  ∧ jcheck Psec [] (.sop .set "pub" (.cat (.lit []) (.var "secret"))) = none
  ∧ jcheck Psec [] (.sop .set "pub" (.san (.var "secret"))) = none
  ∧ jcheck Psec [] (.ite (.var "secret") .skip .skip) = none
  ∧ jcheck Psec [] (.loop (.var "secret") .skip) = none
  ∧ slcheck [] (.seq (.memop .alloc "p")
      (.seq (.assign "q" (.var "p"))
       (.seq (.memop .free "p") (.memop .deref "q")))) = none
  ∧ slcheck [] (.seq (.memop .alloc "p")
      (.seq (.assign "q" (.var "p")) (.memop .free "q"))) = none
  ∧ pcheck "fs" [("u", 1)] (.sop .emit "fs" (.cat (.lit [.ord]) (.var "u"))) = none
  ∧ pcheck "fs" [] (.sop .emit "fs" (.lit [.ord, .quote, .quote])) = none
  ∧ allcheck Psec [] [] (.access "db") = none
  ∧ allcheck Psec [] [] (.seq (.check "log") (.access "db")) = none := by decide

/-! ## Defect 1: the exported noninterference statement was vacuous for strings -/

/-- **The defect, stated.** Two runs started from `initU` agree on every string
    variable, so they cannot differ in a secret string — and every guarantee about the
    sink proved from `initU` is therefore true and empty. -/
theorem initU_hides_string_inputs (σ σ' : Store) :
    (initU σ).sstore = (initU σ').sstore ∧ (initU σ).sink = (initU σ').sink :=
  ⟨rfl, rfl⟩

/-- **The fix.** `jsecTy_sound` was general all along; this exports it. Two memory-safe,
    Low-equal states — differing however they like in *secret* string variables — stay
    Low-equal, sink included. -/
theorem allcheck_NI_general {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : allcheck P [] [] c = some (A', V', k)) :
    ∀ (n : Nat) (π : MedPolicy) (s s' : UState),
      SepInv [] s → SepInv [] s' → uLowEqA P s s' →
      uOptLowEqA P (uexec n c π s) (uexec n c π s') :=
  fun n π s s' hs hs' hle =>
    jsecTy_sound n c [] V' (allcheck_sound c [] [] A' V' k h).joint π s s' hs hs' hle

/-- Two states that differ in a secret string and agree on everything Low. -/
def secretStr : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false, heap := fun _ => 0,
    live := [], fresh := 0, err := false, freed := [],
    sstore := fun y => if y == "secret" then [UCh.quote] else [], sink := [] }

def secretStr' : UState :=
  { store := fun _ => 0, auth := [], reads := [], dead := false, heap := fun _ => 0,
    live := [], fresh := 0, err := false, freed := [], sstore := fun _ => [], sink := [] }

theorem secretStr_lowEqA : uLowEqA Psec secretStr secretStr' := by
  refine ⟨fun _ _ => rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
  intro y hy
  show (if y == "secret" then [UCh.quote] else []) = []
  have : ¬ (y == "secret") = true := by simpa [Psec] using hy
  simp [this]

theorem secretStr_sepInv : SepInv [] secretStr ∧ SepInv [] secretStr' :=
  ⟨⟨rfl, fun _ => ⟨by intro x hx; simp at hx, by intro x hx; simp at hx,
                   by intro a ha; simp [secretStr, memInt] at ha,
                   by intro a ha; simp [secretStr, memInt] at ha,
                   by intro a ha; simp [secretStr, memInt] at ha⟩⟩,
   ⟨rfl, fun _ => ⟨by intro x hx; simp at hx, by intro x hx; simp at hx,
                   by intro a ha; simp [secretStr', memInt] at ha,
                   by intro a ha; simp [secretStr', memInt] at ha,
                   by intro a ha; simp [secretStr', memInt] at ha⟩⟩⟩

/-- A program that *uses* the secret string and still emits publicly. -/
def secretTouching : UCmd :=
  .seq (.sop .set "secret" (.cat (.var "secret") (.lit [.ord])))
       (.sop .emit "db" (.lit [.ord, .quote]))

theorem secretTouching_checks :
    allcheck Psec [] [] secretTouching = some ([], [], 2) := by decide

/-- **And the general statement does real work.** The two runs genuinely differ in the
    secret — the secret string is `[quote, ord]` in one and `[ord]` in the other — and
    the sinks come out equal anyway. From `initU` this would have been vacuous. -/
theorem secretTouching_NI_is_real :
    ((uexec 5 secretTouching (fun _ => true) secretStr).map
        (fun r => (r.1.sstore "secret", r.1.sink)))
      = some ([UCh.quote, UCh.ord], [("db", [UCh.ord, UCh.quote])])
  ∧ ((uexec 5 secretTouching (fun _ => true) secretStr').map
        (fun r => (r.1.sstore "secret", r.1.sink)))
      = some ([UCh.ord], [("db", [UCh.ord, UCh.quote])])
  ∧ (∀ (n : Nat) (π : MedPolicy),
        uOptLowEqA Psec (uexec n secretTouching π secretStr)
                        (uexec n secretTouching π secretStr')) := by
  refine ⟨by decide, by decide, fun n π => ?_⟩
  exact allcheck_NI_general secretTouching_checks n π secretStr secretStr'
    secretStr_sepInv.1 secretStr_sepInv.2 secretStr_lowEqA

/-! ## Defects 2 and 3: the memory model promises less than it looks like -/

/-- **The heap is never touched, and the allocator never reuses.** One induction, two
    scope facts. -/
theorem uexec_heap_fresh : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool), uexec n c π s = some r →
    r.1.heap = s.heap ∧ s.fresh ≤ r.1.fresh
  | 0,     _, _, _, _, h => by simp [uexec] at h
  | n + 1, c, π, s, r, h => by
      cases c with
      | skip =>
          simp only [uexec, Option.some.injEq] at h; subst h; exact ⟨by simp, by simp⟩
      | assign x e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [if_pos hd]; exact ⟨by simp, by simp⟩
          · simp only [if_neg hd]; exact ⟨by simp, by simp⟩
      | check q =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [if_pos hd]; exact ⟨by simp, by simp⟩
          · simp only [if_neg hd]
            by_cases hp : π q = true
            · simp only [if_pos hp]; exact ⟨by simp, by simp⟩
            · simp only [if_neg hp]; exact ⟨by simp, by simp⟩
      | access q =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [if_pos hd]; exact ⟨by simp, by simp⟩
          · simp only [if_neg hd]; exact ⟨by simp, by simp⟩
      | sop op x e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [if_pos hd]; exact ⟨by simp, by simp⟩
          · simp only [if_neg hd]
            cases op with
            | set  => exact ⟨by simp, by simp⟩
            | emit => exact ⟨by simp, by simp⟩
      | memop op x =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp only [if_pos hd]; exact ⟨by simp, by simp⟩
          · simp only [if_neg hd]
            cases op with
            | alloc =>
                refine ⟨by simp, ?_⟩
                show s.fresh ≤ bumpFresh s.freed s.fresh
                cases s.freed with
                | nil => show s.fresh ≤ s.fresh + 1; omega
                | cons _ _ => exact Int.le_refl _
            | deref =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [if_pos hl]; exact ⟨by simp, by simp⟩
                · simp only [if_neg hl]; exact ⟨by simp, by simp⟩
            | free =>
                by_cases hl : memInt (s.store x) s.live = true
                · simp only [if_pos hl]; exact ⟨by simp, by simp⟩
                · simp only [if_neg hl]; exact ⟨by simp, by simp⟩
      | seq c₁ c₂ =>
          rw [uexec_seq_eq] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          · rw [e₁, Option.bind_some] at h
            rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              obtain ⟨h₁, f₁⟩ := uexec_heap_fresh n c₁ π s r₁ e₁
              obtain ⟨h₂, f₂⟩ := uexec_heap_fresh n c₂ π r₁.1 r₂ e₂
              exact ⟨by rw [h₂, h₁], Int.le_trans f₁ f₂⟩
      | ite e c₁ c₂ =>
          rw [uexec_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg] at h
            rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact uexec_heap_fresh n c₁ π s r₁ e₁
          · rw [if_neg hg] at h
            rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact uexec_heap_fresh n c₂ π s r₂ e₂
      | loop e c₀ =>
          rw [uexec_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg] at h
            rcases e₁ : uexec n c₀ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁, Option.bind_some] at h
              rcases e₂ : uexec n (.loop e c₀) π r₁.1 with _ | r₂
              · rw [e₂] at h; simp at h
              · rw [e₂] at h
                simp only [Option.map_some, Option.some.injEq] at h
                subst h
                obtain ⟨h₁, f₁⟩ := uexec_heap_fresh n c₀ π s r₁ e₁
                obtain ⟨h₂, f₂⟩ := uexec_heap_fresh n (.loop e c₀) π r₁.1 r₂ e₂
                exact ⟨by rw [h₂, h₁], Int.le_trans f₁ f₂⟩
          · rw [if_neg hg] at h
            simp only [Option.some.injEq] at h; subst h
            exact ⟨by simp, by simp⟩

/-- **Defect 2, as a theorem.** No command reads or writes the heap, so "memory safety"
    on this machine means the *liveness of addresses* and says nothing about stored
    values. That is exactly what `umcheck_no_fault` and `slcheck_no_fault` claim — but a
    `heap` field in `UState` implies more, and the implication was never checked. -/
theorem heap_is_never_touched (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool) (h : uexec n c π s = some r) : r.1.heap = s.heap :=
  (uexec_heap_fresh n c π s r h).1

/-- **Defect 3, and what became of it.** When this was written the allocator only
    advanced a counter, so a freed address was never handed out again — a limitation
    that stage 1i's use-after-free result silently depended on. Stage 1u removed it:
    `free` now returns the address to a free list and `alloc` reuses it
    (`Reuse.the_allocator_reuses`). The statement below survives the change — the
    counter is still monotone, it just no longer implies non-reuse — so it is renamed to
    say what it actually proves. What the removal cost is recorded in `Reuse.lean`: two
    new invariant conjuncts and one new typing restriction, because with reuse the free
    list becomes a channel. -/
theorem fresh_counter_is_monotone (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool) (h : uexec n c π s = some r) : s.fresh ≤ r.1.fresh :=
  (uexec_heap_fresh n c π s r h).2

/-! ## The verdict

    Twelve attacks, no unsoundness. Three defects, all of the same kind: a guarantee
    narrower than its name. One was fixable in a line (`allcheck_NI_general` — the
    general theorem existed and only the wrapper was weak); two are properties of the
    model that are now theorems instead of unstated assumptions.

    Looking on purpose found things that twenty stages of building did not, and all
    three were in the *statements* rather than the proofs. That is where to look next
    time. -/

end ConfTyping
