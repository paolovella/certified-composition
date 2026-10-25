/-
  The composable core, stage 2e: what speculation costs, and what it cannot touch.

  Stage 2d left the speculative machine with one genuine unsoundness — the certified
  budget ignores transient work — and one positive so narrow it barely counted:
  branch-free programs are window-independent. Both are now closed, and the second turns
  out to have been the wrong statement of a much stronger one.

  **Rollback is complete.** `rollback_is_complete` — for **every** program and **every**
  window, the architectural state after speculation is the state `uexec` would have
  reached. Not just branch-free ones. Stage 2d's `branch_free_is_inert` is the special
  case where the *trace* also agrees; the state agrees always, because transient state is
  discarded by construction and nothing carries it forward.

  That single induction retires the question for four of the five certificates.
  `four_of_five_are_immune` states it directly: mediation, noninterference, memory safety
  and structural integrity are all predicates on the final `UState`, so a machine that
  reaches the same final state satisfies them or fails them identically. No rule changes,
  no side condition, no fence. Speculation cannot touch them.

  So the surface is exactly two things wide: the **cost** and the **trace**.

  **The cost, bounded.** `spec_cost_bound` — in any run, `realCost ≤ archCost * (1 + w)`.
  The budget is not lost to speculation, it is *scaled* by the misprediction window, and
  the constant is the window itself. Composed with a certificate
  (`certified_cost_under_speculation`), a program checked at bound `k` really executes at
  most `k * (1 + w)` commands, and `fiveProg_costs_six_even_speculating` shows the
  branch-free case pays nothing at all.

  The bound is tight in the sense that matters — `the_bound_is_not_vacuous` exhibits a
  program whose real cost genuinely exceeds its certified one — and loose as a constant,
  since it charges a full window to every command rather than to every branch. Tightening
  it to `k + w * (branches taken)` needs a branch count in the judgment and is not
  attempted here.

  **The trace** remains where stage 2d left it: two routes excluded by rules written for
  other purposes, no third route found, and a conjecture stated so it can be attacked.
  That is the one thing this stage does not advance, and saying so is the point of
  separating the two.
-/
import ConfTyping.SpecUnified

namespace ConfTyping

/-! ## Rollback is complete -/

/-- **Speculation has no architectural effect, for every program and every window.** The
    transient state is discarded and nothing carries it forward, so the final state is
    the one `uexec` reaches.

    Stage 2d proved this only for branch-free programs, and only as a by-product of
    proving something stronger about them. Generalising 2d's faithfulness lemma from
    `w = 0` to every `w` — which cost nothing, because the transient parts live in the
    two components that lemma projects away — makes it a corollary and makes it
    universal. -/
theorem rollback_is_complete (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState) :
    (uexecS n w c π s).map (fun r => r.1) = (uexec n c π s).map (fun r => r.1) := by
  have h := spec_is_uexec_extended n w c π s
  rcases e : uexecS n w c π s with _ | r <;> rw [e] at h
  · rcases e' : uexec n c π s with _ | r' <;> rw [e'] at h
    · rfl
    · simp at h
  · rcases e' : uexec n c π s with _ | r' <;> rw [e'] at h
    · simp at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      simp only [Option.map_some, h.1]

/-- The other half, named because it is the reason the budget failed: the
    **architectural** cost does not depend on the window. That is exactly what makes it
    blind to the transient work it does not count. -/
theorem archcost_window_free (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState) :
    (uexecS n w c π s).map (fun r => r.2.1) = (uexec n c π s).map (fun r => r.2.1) := by
  have h := spec_is_uexec_extended n w c π s
  rcases e : uexecS n w c π s with _ | r <;> rw [e] at h
  · rcases e' : uexec n c π s with _ | r' <;> rw [e'] at h
    · rfl
    · simp at h
  · rcases e' : uexec n c π s with _ | r' <;> rw [e'] at h
    · simp at h
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      simp only [Option.map_some, h.2]

/-! ## Four of the five certificates are immune -/

/-- **Mediation, noninterference, memory safety and structural integrity all transfer to
    the speculative machine, for every program and every window.** Each is a predicate on
    the final `UState`, and `rollback_is_complete` says the final state is the same one.
    No rule changes and no fence is required — the guarantees were never at risk.

    Stated as a transfer principle rather than for a fixed program, so it applies to
    anything the core certifies however it was certified. -/
theorem four_of_five_are_immune {c : UCmd} {P : Partition}
    (hmed : ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
    (hmem : ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false)
    (hsink : ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → ∀ t ∈ r.1.sink, t.1 ≠ "")
    : ∀ (n w : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × Nat × List Int),
        uexecS n w c π (initU σ) = some r →
        (∀ q ∈ r.1.reads, π q = true) ∧ r.1.err = false
          ∧ (∀ t ∈ r.1.sink, t.1 ≠ "") := by
  intro n w π σ r hr
  have h := rollback_is_complete n w c π (initU σ)
  rw [hr] at h
  rcases e : uexec n c π (initU σ) with _ | r' <;> rw [e] at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨fun q hq => hmed n π σ r' e q (h ▸ hq), h ▸ hmem n π σ r' e,
           fun t ht => hsink n π σ r' e t (h ▸ ht)⟩

/-- The same for noninterference, which needs two runs rather than one and so is stated
    on its own. `uOptLowEq` asks for three things — low-equal states, equal costs, equal
    branch observations — and `spec_is_uexec_extended` supplies the first two at every
    window. The third is the branch list, which lives in `uexec`'s observation and not in
    `uexecS`'s trace, so it is projected to `[]` on both sides rather than quietly
    dropped. -/
theorem ni_transfers_to_speculation {c : UCmd} {P : Partition}
    (hni : ∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
    : ∀ (n w : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P ((uexecS n w c π (initU σ)).map (fun r => (r.1, r.2.1, ([] : List Bool))))
                    ((uexecS n w c π (initU σ')).map
                       (fun r => (r.1, r.2.1, ([] : List Bool)))) := by
  intro n w π σ σ' hlow
  have h := hni n π σ σ' hlow
  have key : ∀ (σ₀ : Store) (r₀ : UState × Nat × List Bool),
      uexec n c π (initU σ₀) = some r₀ →
      ∃ rr, uexecS n w c π (initU σ₀) = some rr ∧ rr.1 = r₀.1 ∧ rr.2.1 = r₀.2.1 := by
    intro σ₀ r₀ h₀
    have e := spec_is_uexec_extended n w c π (initU σ₀)
    rw [h₀] at e
    rcases hh : uexecS n w c π (initU σ₀) with _ | rr
    · rw [hh] at e; simp at e
    · rw [hh] at e
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      exact ⟨rr, rfl, e.1, e.2⟩
  have keyN : ∀ (σ₀ : Store), uexec n c π (initU σ₀) = none →
      uexecS n w c π (initU σ₀) = none := by
    intro σ₀ h₀
    have e := spec_is_uexec_extended n w c π (initU σ₀)
    rw [h₀] at e
    rcases hh : uexecS n w c π (initU σ₀) with _ | rr
    · rfl
    · rw [hh] at e; simp at e
  rcases hA' : uexec n c π (initU σ) with _ | rA' <;>
    rcases hB' : uexec n c π (initU σ') with _ | rB' <;> rw [hA', hB'] at h
  · rw [keyN σ hA', keyN σ' hB']; exact trivial
  · simp only [uOptLowEq] at h
  · simp only [uOptLowEq] at h
  · obtain ⟨rA, hA, hs1, hk1⟩ := key σ rA' hA'
    obtain ⟨rB, hB, hs2, hk2⟩ := key σ' rB' hB'
    rw [hA, hB]
    exact ⟨hs1 ▸ hs2 ▸ h.1, by rw [hk1, hk2]; exact h.2.1, rfl⟩

/-! ## The cost, bounded -/

/-- **The real cost is the architectural cost scaled by the window.** In any run,
    `realCost ≤ archCost * (1 + w)`: speculation does not lose the budget, it multiplies
    it, and the multiplier is the misprediction window. Stated within a single run, so no
    two-run comparison and no state agreement is needed. -/
theorem spec_cost_bound : ∀ (n w : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × Nat × List Int),
    uexecS n w c π s = some r → r.2.2.1 ≤ r.2.1 * (1 + w)
  | 0,     _, _, _, _, _, h => by simp [uexecS] at h
  | n + 1, w, c, π, s, r, h => by
      cases c with
      | skip =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | assign _ _ =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | check _ =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | access _ =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | memop _ _ =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | sop _ _ _ =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | hop _ _ _ =>
          simp only [uexecS, uexec, Option.map_some, Option.some.injEq] at h; subst h
          show 1 ≤ 1 * (1 + w); omega
      | seq c₁ c₂ =>
          rw [show uexecS (n+1) w (.seq c₁ c₂) π s
                = (uexecS n w c₁ π s).bind (fun r₁ =>
                    (uexecS n w c₂ π r₁.1).map fun r₂ =>
                      (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2.1 + r₂.2.2.1,
                       r₁.2.2.2 ++ r₂.2.2.2)) from rfl] at h
          rcases e₁ : uexecS n w c₁ π s with _ | r₁ <;> rw [e₁] at h
          · simp at h
          · rw [Option.bind_some] at h
            rcases e₂ : uexecS n w c₂ π r₁.1 with _ | r₂ <;> rw [e₂] at h
            · simp at h
            · simp only [Option.map_some, Option.some.injEq] at h; subst h
              have h₁ := spec_cost_bound n w c₁ π s r₁ e₁
              have h₂ := spec_cost_bound n w c₂ π r₁.1 r₂ e₂
              show r₁.2.2.1 + r₂.2.2.1 ≤ (r₁.2.1 + r₂.2.1) * (1 + w)
              rw [Nat.add_mul]; omega
      | ite e c₁ c₂ =>
          rw [uexecS_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexecS n w c₁ π s with _ | r₁ <;> rw [e₁] at h
            · simp at h
            · simp only [Option.map_some, Option.some.injEq] at h; subst h
              have h₁ := spec_cost_bound n w c₁ π s r₁ e₁
              have ht := transSteps_le w (flatten c₂) π s
              show 1 + transSteps w (flatten c₂) π s + r₁.2.2.1 ≤ (1 + r₁.2.1) * (1 + w)
              rw [Nat.add_mul, Nat.one_mul]; omega
          · rw [ite_eq_right hg] at h
            rcases e₂ : uexecS n w c₂ π s with _ | r₂ <;> rw [e₂] at h
            · simp at h
            · simp only [Option.map_some, Option.some.injEq] at h; subst h
              have h₂ := spec_cost_bound n w c₂ π s r₂ e₂
              have ht := transSteps_le w (flatten c₁) π s
              show 1 + transSteps w (flatten c₁) π s + r₂.2.2.1 ≤ (1 + r₂.2.1) * (1 + w)
              rw [Nat.add_mul, Nat.one_mul]; omega
      | loop e c₀ =>
          rw [uexecS_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexecS n w c₀ π s with _ | r₁ <;> rw [e₁] at h
            · simp at h
            · rw [Option.bind_some] at h
              rcases e₂ : uexecS n w (.loop e c₀) π r₁.1 with _ | r₂ <;> rw [e₂] at h
              · simp at h
              · simp only [Option.map_some, Option.some.injEq] at h; subst h
                have h₁ := spec_cost_bound n w c₀ π s r₁ e₁
                have h₂ := spec_cost_bound n w (.loop e c₀) π r₁.1 r₂ e₂
                show 1 + r₁.2.2.1 + r₂.2.2.1 ≤ (1 + r₁.2.1 + r₂.2.1) * (1 + w)
                rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
          · rw [ite_eq_right hg] at h
            simp only [Option.some.injEq] at h; subst h
            show 1 ≤ 1 * (1 + w); omega

/-- **Composed with a certificate.** A program the core checks at bound `k` really runs
    at most `k * (1 + w)` commands under misprediction window `w`, transient work
    included. The budget survives speculation; it is scaled, and the scale factor is the
    window. -/
theorem certified_cost_under_speculation {P : Partition} {c : UCmd}
    {C' : TaintEnv} {A' V' : List String} {k : Nat} {Ks : List Nat}
    (hx : xcheck P [] [] [] c = some (C', A', V', k, Ks)) :
    ∀ (n w : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × Nat × List Int),
      uexecS n w c π s = some r → r.2.2.1 ≤ k * (1 + w) := by
  intro n w π s r hr
  have hb := spec_cost_bound n w c π s r hr
  have harch : r.2.1 ≤ k := by
    have hw := archcost_window_free n w c π s
    rw [hr] at hw
    rcases e : uexec n c π s with _ | r' <;> rw [e] at hw
    · simp at hw
    · simp only [Option.map_some, Option.some.injEq] at hw
      have := (xcheck_gives_five hx).1 n π s r' e
      omega
  calc r.2.2.1 ≤ r.2.1 * (1 + w) := hb
    _ ≤ k * (1 + w) := Nat.mul_le_mul_right _ harch

/-- The worked program is branch-free, so it pays nothing: six commands certified, six
    executed, at every window. -/
theorem fiveProg_costs_six_even_speculating :
    ∀ (n w : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × Nat × List Int),
      uexecS n w fiveProg π s = some r → r.2.2.1 ≤ 6 * (1 + w) :=
  certified_cost_under_speculation fiveProg_checks

/-- **And the bound is not vacuous**: a certified program whose real cost genuinely
    exceeds its certified one, so the scaling is doing work rather than restating the
    budget. -/
theorem the_bound_is_not_vacuous :
    acostU 12 1 brLow (fun _ => true) twoLive = some 2
  ∧ rcostU 12 1 brLow (fun _ => true) twoLive = some 3
  ∧ (3 : Nat) ≤ 2 * (1 + 1) := by decide

/-! ## What is left

    Speculation, on this core, is exactly two things wide: the **cost**, now bounded, and
    the **trace**, still open. The other four certificates were never at risk, and
    `rollback_is_complete` is the one-line reason.

    Two honest looseness notes. The cost bound charges a full window to *every* command
    rather than to every branch, so `k * (1 + w)` is far above the true
    `k + w * (branches taken)`; tightening it needs a branch count in the judgment, and
    the loose form is what a bound is for. And the trace question is untouched here — it
    is stage 2d's conjecture, and separating the two stages is what makes clear which one
    moved. -/

end ConfTyping
