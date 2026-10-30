/-
  **`bcheck`'s budget on every partial run** (F2 step 3, the first of four ports). Not Ring 0.

  `UCert.budget` bounds the cost of runs `uexec` finishes. On `ucmdLangT` (halting abort, one
  trace) a run can also abort, or run out of fuel, and the budget must hold of those runs too:
  that is what makes `Cert.bound` non-vacuous on a lawful language. This file proves it by
  induction on `bcheckF`'s rules, the way `bcheckF_sound` does for finished runs:
  - a sequence costs at most the sum, an `ite` one plus the larger branch, an atomic step 1;
  - a counted loop from counter `v` costs at most `1 + v * (b + 2)` on every partial run
    (`countU_costT`). After a finished turn the counter went down by one or the run died,
    which `countU_turn` gives through the bridge `uexecT_done_agree`; a dead state's run then
    costs 0, because abort halts.
  The result: `bcheck_boundT`, `Cert.bound k` on `ucmdLangT` for every `bcheck`-accepted
  program.
-/
import ConfTyping.UTrace

namespace ConfTyping

/-! ## Single steps -/

set_option hygiene false in
local macro "step_tac" : tactic =>
  `(tactic| (simp only [stepT, uexec]; (repeat (split)) <;> simp_all))

/-- An atomic step costs at most 1. -/
theorem stepT_cost (c : UCmd) (hc : atomic c = true) (π : MedPolicy) (s : UState) :
    (stepT c π s).cost ≤ 1 := by
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | memop op x => cases op <;> step_tac
  | hop op x y => cases op <;> step_tac
  | sop op x e => cases op <;> step_tac
  | _ => step_tac

/-- A run that starts dead, or has no fuel, costs nothing. -/
theorem uexecT_dead_cost (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState) (hd : s.dead = true) :
    (uexecT n c π s).cost = 0 := by
  cases n <;> simp [uexecT, hd]

/-- A command that does not write `x` leaves `x` alone, on every partial run. -/
theorem uexecT_noWrite : ∀ (n : Nat) (x : String) (c : UCmd) (π : MedPolicy) (s : UState),
    noWrite x c = true → (uexecT n c π s).st.store x = s.store x := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; rfl
  | succ m ih =>
    intro x c π s hw
    cases c with
    | seq c₁ c₂ =>
      simp only [noWrite, Bool.and_eq_true] at hw
      simp only [uexecT]; split
      · rfl
      simp only [TRun.seqT]
      split
      · rw [ih x c₂ π _ hw.2, ih x c₁ π s hw.1]
      · exact ih x c₁ π s hw.1
    | ite e c₁ c₂ =>
      simp only [noWrite, Bool.and_eq_true] at hw
      simp only [uexecT]; split
      · rfl
      simp only [TRun.tick]
      split
      · exact ih x c₁ π s hw.1
      · exact ih x c₂ π s hw.2
    | loop e b =>
      simp only [noWrite] at hw
      simp only [uexecT]; split
      · rfl
      split
      · simp only [TRun.tick, TRun.seqT]
        split
        · rw [ih x _ π _ (by simpa [noWrite] using hw), ih x b π s hw]
        · exact ih x b π s hw
      · rfl
    | _ =>
      simp only [uexecT]; split
      · rfl
      simp only [stepT]
      split
      · rename_i r hr; exact noWrite_preserves 1 x _ π s r hw hr
      · rfl

/-! ## The counted loop -/

theorem TRun.seqT_cost_le (a : TRun) (k : UState → TRun) :
    (a.seqT k).cost ≤ a.cost + (k a.st).cost := by
  unfold TRun.seqT; split
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _

/-- An atomic command costs at most 1 on any partial run. -/
theorem uexecT_atomic_cost (n : Nat) (c : UCmd) (hc : atomic c = true) (π : MedPolicy)
    (s : UState) : (uexecT n c π s).cost ≤ 1 := by
  rcases n with _ | n
  · simp [uexecT]
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | _ => simp only [uexecT]; split
         · simp
         · exact stepT_cost _ hc π s

/-- One turn of a counted loop, body then decrement, costs at most `b + 1`. -/
theorem turn_costT (i : String) (body : UCmd) (π : MedPolicy) (b : Nat)
    (hb : ∀ n s, (uexecT n body π s).cost ≤ b) (n : Nat) (s : UState) :
    (uexecT n (.seq body (decOne i)) π s).cost ≤ b + 1 := by
  rcases n with _ | n
  · simp [uexecT]
  simp only [uexecT]; split
  · simp
  · have h1 := TRun.seqT_cost_le (uexecT n body π s) (fun t => uexecT n (decOne i) π t)
    have h2 := hb n s
    have h3 := uexecT_atomic_cost n (decOne i) rfl π (uexecT n body π s).st
    omega

/-- **The loop's budget on partial runs.** From a state whose counter is `v`, a counted loop
    whose body costs at most `b` on every partial run costs at most `1 + v * (b + 2)`. -/
theorem countU_costT (i : String) (body : UCmd) (π : MedPolicy) (b : Nat)
    (hw : noWrite i body = true) (hb : ∀ n s, (uexecT n body π s).cost ≤ b)
    (hbu : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
            uexec n body π s = some r → r.2.1 ≤ b) :
    ∀ (n v : Nat) (s : UState), s.store i = (v : Int) →
      (uexecT n (countU i body) π s).cost ≤ 1 + v * (b + 2) := by
  intro n
  induction n with
  | zero => intro _ _ _; simp [uexecT]
  | succ m ih =>
    intro v s hv
    by_cases hd : s.dead = true
    · rw [uexecT_dead_cost _ _ _ _ hd]; exact Nat.zero_le _
    have ht := turn_costT i body π b hb m s
    unfold countU
    simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte]
    by_cases hg : evalE (.var i) s.store ≠ 0
    · rw [ite_eq_left hg]
      have hv0 : v ≠ 0 := by intro h0; apply hg; simp [evalE, hv, h0]
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      simp only [TRun.tick]
      rw [Nat.succ_mul]
      generalize hT : w * (b + 2) = T
      by_cases hdone : (uexecT m (.seq body (decOne i)) π s).out = .done
      · have hk : (uexecT m (countU i body) π (uexecT m (.seq body (decOne i)) π s).st).cost
            ≤ 1 + T := by
          obtain ⟨hu, _⟩ := uexecT_done_agree m _ π s hdone
          rcases (countU_turn hw hbu m π s _ hu).2 with h1 | ⟨h1, _⟩
          · rw [← hT]; apply ih w
            simp only at h1; rw [h1, hv]; push_cast; omega
          · rw [uexecT_dead_cost _ _ _ _ h1]; exact Nat.zero_le _
        have hs := TRun.seqT_cost_le (uexecT m (.seq body (decOne i)) π s)
          (fun t => uexecT m (.loop (.var i) (.seq body (decOne i))) π t)
        unfold countU at hk
        omega
      · have hs : ((uexecT m (.seq body (decOne i)) π s).seqT
            (fun t => uexecT m (.loop (.var i) (.seq body (decOne i))) π t)).cost
            = (uexecT m (.seq body (decOne i)) π s).cost := by
          unfold TRun.seqT; rw [ite_eq_right hdone]
        rw [hs]; omega
    · rw [ite_eq_right hg]; simp

/-! ## The checker's budget holds on every partial run -/

/-- An atomic step is within any budget `uexec`'s step is within. -/
theorem stepT_cost_le_of {c : UCmd} {π : MedPolicy} {s : UState} {k : Nat}
    (hb : ∀ r, uexec 1 c π s = some r → r.2.1 ≤ k) : (stepT c π s).cost ≤ k := by
  unfold stepT; split
  · rename_i r hr; exact hb r hr
  · exact Nat.zero_le _

/-- **`bcheck`'s budget on partial runs.** Every run of a `bcheckF`-accepted program, at any
    fuel and with halting abort, costs at most the checker's budget: finished, aborted, or out
    of fuel. -/
theorem bcheckF_budgetT {P : Partition} : ∀ (f : Nat) (c : UCmd) (A V A' V' : List String)
    (k : Nat), bcheckF P f A V c = some (A', V', k) →
      ∀ (n : Nat) (π : MedPolicy) (s : UState), (uexecT n c π s).cost ≤ k := by
  intro f
  induction f with
  | zero => intro c A V A' V' k h; simp [bcheckF] at h
  | succ g ih =>
    intro c A V A' V' k h n π s
    rcases n with _ | n
    · simp [uexecT]
    by_cases hd : s.dead = true
    · rw [uexecT_dead_cost _ _ _ _ hd]; exact Nat.zero_le _
    cases c with
    | seq c₁ c₂ =>
      simp only [bcheckF] at h
      split at h
      · -- a counted loop
        rename_i i m body heq
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          split at h
          · rename_i A₂ V₂ b hbody
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨_, _, rfl⟩ := h
              rw [asFor_eq heq]
              have hbT := ih body _ _ _ _ _ hbody
              have hbu := (bcheckF_sound g body _ _ _ _ _ hbody).bundle.budget
              unfold forU
              simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte]
              by_cases ha : (uexecT n (.assign i (.num (m : Int))) π s).out = .done
              · have hcnt : (uexecT n (.assign i (.num (m : Int))) π s).st.store i = (m : Int) := by
                  obtain ⟨hu, _⟩ := uexecT_done_agree n _ π s ha
                  rcases n with _ | n
                  · cases ha
                  simp only [uexec, hd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
                    Prod.mk.injEq] at hu
                  rw [← hu.1]; simp [upd, evalE]
                have h1 := TRun.seqT_cost_le (uexecT n (.assign i (.num (m : Int))) π s)
                  (fun t => uexecT n (countU i body) π t)
                have h2 := uexecT_atomic_cost n (.assign i (.num (m : Int))) rfl π s
                have h3 := countU_costT i body π b hcond.2 (fun n s => hbT n π s) hbu n m _ hcnt
                generalize m * (b + 2) = T at *
                omega
              · have hs : ((uexecT n (.assign i (.num (m : Int))) π s).seqT
                    (fun t => uexecT n (countU i body) π t)).cost
                    = (uexecT n (.assign i (.num (m : Int))) π s).cost := by
                  unfold TRun.seqT; rw [ite_eq_right ha]
                have h2 := uexecT_atomic_cost n (.assign i (.num (m : Int))) rfl π s
                rw [hs]; omega
            · cases h
          · cases h
        · cases h
      · -- a sequence
        obtain ⟨⟨A₁, V₁, k₁⟩, hc₁, hm⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨A₂, V₂, k₂⟩, hc₂, hk⟩ := Option.map_eq_some_iff.mp hm
        simp only [Prod.mk.injEq] at hk
        obtain ⟨_, _, rfl⟩ := hk
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte]
        have e₁ := ih c₁ _ _ _ _ _ hc₁ n π s
        have e₂ := ih c₂ _ _ _ _ _ hc₂ n π (uexecT n c₁ π s).st
        have := TRun.seqT_cost_le (uexecT n c₁ π s) (fun t => uexecT n c₂ π t)
        omega
    | ite e c₁ c₂ =>
      simp only [bcheckF] at h
      split at h
      · split at h
        · rename_i p₁ p₂ h₁ h₂
          obtain ⟨A₁, V₁, k₁⟩ := p₁
          obtain ⟨A₂, V₂, k₂⟩ := p₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, _, rfl⟩ := h
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick]
          have e₁ := ih c₁ _ _ _ _ _ h₁ n π s
          have e₂ := ih c₂ _ _ _ _ _ h₂ n π s
          have m₁ := Nat.le_max_left k₁ k₂
          have m₂ := Nat.le_max_right k₁ k₂
          split <;> omega
        · cases h
      · cases h
    | loop e b =>
      simp only [bcheckF, allcheck] at h; cases h
    | _ =>
      simp only [bcheckF] at h
      have hb := (allcheck_sound _ _ _ _ _ _ h).bundle.budget 1 π s
      simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte]
      exact stepT_cost_le_of hb

/-- **The budget certificate on the lawful language.** A program `bcheck` accepts with budget
    `k` carries `Cert.bound k` on `ucmdLangT`: every run, finished, aborted or out of fuel,
    costs at most `k`. -/
theorem bcheck_boundT {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.bound (ucmdLangT P π) k c :=
  fun n σ _ => bcheckF_budgetT (usize c) c [] [] A' V' k h n π (initU σ)

end ConfTyping
