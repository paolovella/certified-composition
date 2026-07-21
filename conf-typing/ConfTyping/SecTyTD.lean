/-
  Declassified timing — brick 6: the Policy analogue of the timing checker.

  Brick 5 (`SecTyT`) closed the timing channel by *forbidding* secret-dependent
  branching — safe, but a program that must branch on a secret is rejected, not
  certified. This module adds the declassification stratum to the clock: a High
  guard is allowed **when its branch bit is declared released**, and the checker
  then certifies that the whole instrumented outcome (store, running time,
  trace) reveals *at most* the declared bits.

  `SecTyTD P Δ c` is the timing-sensitive discipline with declared guards
  (`iteD`) and declared writes (`assignD`) — the brick-3 policy environment `Δ`
  over the timing checker. Soundness (`secTyTD_sound`) is
  `ReleasesAtMost c (outO P) P (relOf P c)`: two runs agreeing on Low *and on
  the computed ledger* `relOf P c` produce the identical outcome, clock
  included. The ledger `relOf` (brick 3) already carries the branch bit of each
  non-Low guard, so the released quantity is exactly the declassified timing.

  The money theorem: `Ptime` (branch on the secret, unequal branch costs) —
  rejected by the store checker's timing-sensitive sibling under an empty budget
  (`ptime_rejected_TD`, matching brick 5) — type-checks under one declared guard
  permit, and its running time is then certified to reveal *at most* the secret
  bit (`ptime_timing_released`, `ptime_wall_of_bit`). Declassification turns a
  rejected timing leak into a bounded, declared one.
-/
import ConfTyping.SecTyD
import ConfTyping.SecTyT

namespace ConfTyping

/-! ## The judgment: timing-sensitive typing with declared guards -/

/-- Timing-sensitive flow typing with a policy budget `Δ`: `SecTyT` plus
    declared High writes (`assignD`) and **declared High guards** (`iteD`).
    Still no undeclared `iteH` — a secret branch must be *declared* to pass. -/
inductive SecTyTD (P : Partition) (Δ : List Permit) : Cmd → Prop where
  | skip    : SecTyTD P Δ .skip
  | assignH : ∀ x e, P x = true → SecTyTD P Δ (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → SecTyTD P Δ (.assign x e)
  | assignD : ∀ x e, Permit.expr e ∈ Δ → SecTyTD P Δ (.assign x e)
  | seq     : SecTyTD P Δ c₁ → SecTyTD P Δ c₂ → SecTyTD P Δ (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → SecTyTD P Δ c₁ → SecTyTD P Δ c₂ →
              SecTyTD P Δ (.ite e c₁ c₂)
  | iteD    : ∀ e, Permit.guard e ∈ Δ → SecTyTD P Δ c₁ → SecTyTD P Δ c₂ →
              SecTyTD P Δ (.ite e c₁ c₂)

/-! ## Soundness: the outcome releases at most the ledger -/

/-- Full-outcome release: Low store, cost, and trace all agree between runs
    that agree on Low *and* on the declared release `φ`. -/
def OutReleases (c : Cmd) (P : Partition) (φ : Release) : Prop :=
  ∀ σ σ', lowEq P σ σ' → φ σ = φ σ' →
    lowEq P (evalStore c σ) (evalStore c σ')
      ∧ (eval c σ).2.1 = (eval c σ').2.1
      ∧ (eval c σ).2.2 = (eval c σ').2.2

/-- The shared branch case for the full outcome: whether the guard is Low
    (same branch by `evalE_lowEq`) or its bit is in the ledger (same branch by
    ledger agreement), the conditional releases at most its ledger. -/
theorem iteTD_aux {P : Partition} {e : Expr} {c₁ c₂ : Cmd}
    (ih₁ : OutReleases c₁ P (relOf P c₁))
    (ih₂ : OutReleases c₂ P (relOf P c₂)) :
    OutReleases (.ite e c₁ c₂) P (relOf P (.ite e c₁ c₂)) := by
  intro σ σ' hle hφ
  by_cases hg : exprLow P e = true
  · simp only [relOf, if_pos hg] at hφ
    injection hφ with hφ₁ hφ₂
    have hgv : evalE e σ = evalE e σ' := evalE_lowEq e hg hle
    by_cases hb : evalE e σ ≠ 0
    · have hb' : evalE e σ' ≠ 0 := by rwa [hgv] at hb
      obtain ⟨hs, hc, ht⟩ := ih₁ σ σ' hle hφ₁
      refine ⟨?_, ?_, ?_⟩
      · show lowEq P (eval (.ite e c₁ c₂) σ).1 (eval (.ite e c₁ c₂) σ').1
        simp only [eval, if_pos hb, if_pos hb']; exact hs
      · show (eval (.ite e c₁ c₂) σ).2.1 = (eval (.ite e c₁ c₂) σ').2.1
        simp only [eval, if_pos hb, if_pos hb']; rw [hc]
      · show (eval (.ite e c₁ c₂) σ).2.2 = (eval (.ite e c₁ c₂) σ').2.2
        simp only [eval, if_pos hb, if_pos hb']; rw [ht]
    · have hb' : ¬ evalE e σ' ≠ 0 := by rwa [hgv] at hb
      obtain ⟨hs, hc, ht⟩ := ih₂ σ σ' hle hφ₂
      refine ⟨?_, ?_, ?_⟩
      · show lowEq P (eval (.ite e c₁ c₂) σ).1 (eval (.ite e c₁ c₂) σ').1
        simp only [eval, if_neg hb, if_neg hb']; exact hs
      · show (eval (.ite e c₁ c₂) σ).2.1 = (eval (.ite e c₁ c₂) σ').2.1
        simp only [eval, if_neg hb, if_neg hb']; rw [hc]
      · show (eval (.ite e c₁ c₂) σ).2.2 = (eval (.ite e c₁ c₂) σ').2.2
        simp only [eval, if_neg hb, if_neg hb']; rw [ht]
  · simp only [relOf, if_neg hg] at hφ
    injection hφ with hbit hφr
    injection hφr with hφ₁ hφ₂
    injection hbit with hbit
    have hbb : (evalE e σ ≠ 0) ↔ (evalE e σ' ≠ 0) := by
      by_cases h₁ : evalE e σ ≠ 0 <;> by_cases h₂ : evalE e σ' ≠ 0 <;>
        simp [h₁, h₂] at hbit ⊢
    by_cases hb : evalE e σ ≠ 0
    · have hb' : evalE e σ' ≠ 0 := hbb.mp hb
      obtain ⟨hs, hc, ht⟩ := ih₁ σ σ' hle hφ₁
      refine ⟨?_, ?_, ?_⟩
      · show lowEq P (eval (.ite e c₁ c₂) σ).1 (eval (.ite e c₁ c₂) σ').1
        simp only [eval, if_pos hb, if_pos hb']; exact hs
      · show (eval (.ite e c₁ c₂) σ).2.1 = (eval (.ite e c₁ c₂) σ').2.1
        simp only [eval, if_pos hb, if_pos hb']; rw [hc]
      · show (eval (.ite e c₁ c₂) σ).2.2 = (eval (.ite e c₁ c₂) σ').2.2
        simp only [eval, if_pos hb, if_pos hb']; rw [ht]
    · have hb' : ¬ evalE e σ' ≠ 0 := fun h => hb (hbb.mpr h)
      obtain ⟨hs, hc, ht⟩ := ih₂ σ σ' hle hφ₂
      refine ⟨?_, ?_, ?_⟩
      · show lowEq P (eval (.ite e c₁ c₂) σ).1 (eval (.ite e c₁ c₂) σ').1
        simp only [eval, if_neg hb, if_neg hb']; exact hs
      · show (eval (.ite e c₁ c₂) σ).2.1 = (eval (.ite e c₁ c₂) σ').2.1
        simp only [eval, if_neg hb, if_neg hb']; rw [hc]
      · show (eval (.ite e c₁ c₂) σ).2.2 = (eval (.ite e c₁ c₂) σ').2.2
        simp only [eval, if_neg hb, if_neg hb']; rw [ht]

theorem secTyTD_outReleases {P : Partition} {Δ : List Permit} {c : Cmd}
    (h : SecTyTD P Δ c) : OutReleases c P (relOf P c) := by
  induction h with
  | skip => intro σ σ' hle _; exact ⟨hle, rfl, rfl⟩
  | assignH x e hx =>
      intro σ σ' hle _
      refine ⟨?_, rfl, rfl⟩
      intro y hy
      have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      simp only [upd, if_neg hyx]; exact hle y hy
  | assignL x e he =>
      intro σ σ' hle _
      refine ⟨?_, rfl, rfl⟩
      intro y hy
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      simp only [upd]
      by_cases hxy : y = x
      · rw [if_pos hxy, if_pos hxy, evalE_lowEq e he hle]
      · rw [if_neg hxy, if_neg hxy]; exact hle y hy
  | assignD x e _ =>
      intro σ σ' hle hφ
      refine ⟨?_, rfl, rfl⟩
      intro y hy
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      have hev : evalE e σ = evalE e σ' := by
        by_cases hl : exprLow P e = true
        · exact evalE_lowEq e hl hle
        · simp only [relOf, if_neg hl] at hφ; injection hφ
      simp only [upd, hev]
      by_cases hxy : y = x
      · rw [if_pos hxy, if_pos hxy]
      · rw [if_neg hxy, if_neg hxy]; exact hle y hy
  | seq h₁ h₂ ih₁ ih₂ =>
      intro σ σ' hle hφ
      simp only [relOf, seqRelease] at hφ
      injection hφ with hφ₁ hφ₂
      obtain ⟨hs₁, hc₁, ht₁⟩ := ih₁ σ σ' hle hφ₁
      obtain ⟨hs₂, hc₂, ht₂⟩ := ih₂ _ _ hs₁ hφ₂
      refine ⟨hs₂, ?_, ?_⟩
      · show (eval _ σ).2.1 + (eval _ (evalStore _ σ)).2.1
             = (eval _ σ').2.1 + (eval _ (evalStore _ σ')).2.1
        rw [hc₁, hc₂]
      · show (eval _ σ).2.2 ++ (eval _ (evalStore _ σ)).2.2
             = (eval _ σ').2.2 ++ (eval _ (evalStore _ σ')).2.2
        rw [ht₁, ht₂]
  | iteL e _ _ _ ih₁ ih₂ => exact iteTD_aux ih₁ ih₂
  | iteD e _ _ _ ih₁ ih₂ => exact iteTD_aux ih₁ ih₂

/-- The full-outcome release predicate is the channel claim
    `ReleasesAtMost c (outO P) P φ`. -/
theorem outReleases_to_releasesAtMost {P : Partition} {c : Cmd} {φ : Release}
    (h : OutReleases c P φ) : ReleasesAtMost c (outO P) P φ := by
  intro σ σ' hle hφ
  obtain ⟨hs, hc, ht⟩ := h σ σ' hle hφ
  simp only [obs, outO, tup, resultO, wall, branchO]
  congr 1
  · congr 1
    funext y
    cases hPy : P y with
    | true  => simp
    | false => simp only [Bool.false_eq_true, if_false]; exact hs y hPy
  · rw [hc, ht]

/-- **Soundness.** A component typed timing-sensitively with declared guards
    reveals, on its whole instrumented outcome, at most its ledger `relOf P c`
    — the declassified timing bound. -/
theorem secTyTD_sound {P : Partition} {Δ : List Permit} {c : Cmd}
    (h : SecTyTD P Δ c) : ReleasesAtMost c (outO P) P (relOf P c) :=
  outReleases_to_releasesAtMost (secTyTD_outReleases h)

/-! ## The executable checker -/

def secCheckTD (P : Partition) (Δ : List Permit) : Cmd → Bool
  | .skip        => true
  | .assign x e  => P x || exprLow P e || decide (Permit.expr e ∈ Δ)
  | .seq c₁ c₂   => secCheckTD P Δ c₁ && secCheckTD P Δ c₂
  | .ite e c₁ c₂ =>
      (exprLow P e && secCheckTD P Δ c₁ && secCheckTD P Δ c₂)
        || (decide (Permit.guard e ∈ Δ) && secCheckTD P Δ c₁ && secCheckTD P Δ c₂)

theorem secCheckTD_sound {P : Partition} {Δ : List Permit} :
    ∀ {c : Cmd}, secCheckTD P Δ c = true → SecTyTD P Δ c
  | .skip, _ => .skip
  | .assign _ _, h => by
      simp only [secCheckTD, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with (hx | he) | hm
      · exact .assignH _ _ hx
      · exact .assignL _ _ he
      · exact .assignD _ _ hm
  | .seq _ _, h => by
      simp only [secCheckTD, Bool.and_eq_true] at h
      exact .seq (secCheckTD_sound h.1) (secCheckTD_sound h.2)
  | .ite _ _ _, h => by
      simp only [secCheckTD, Bool.or_eq_true, Bool.and_eq_true,
                 decide_eq_true_eq] at h
      rcases h with ⟨⟨hg, h₁⟩, h₂⟩ | ⟨⟨hm, h₁⟩, h₂⟩
      · exact .iteL _ hg (secCheckTD_sound h₁) (secCheckTD_sound h₂)
      · exact .iteD _ hm (secCheckTD_sound h₁) (secCheckTD_sound h₂)

/-- **Certificates by `decide`, declassified-timing form.** -/
theorem releasesAtMost_of_checkTD {P : Partition} {Δ : List Permit} {c : Cmd}
    (h : secCheckTD P Δ c = true) : ReleasesAtMost c (outO P) P (relOf P c) :=
  secTyTD_sound (secCheckTD_sound h)

/-! ## The money theorem: a rejected timing leak becomes a declared one -/

/-- Under an empty budget, the secret branch is rejected — matching brick 5's
    `ptime_rejected_T`: with nothing declared, `SecTyTD` is `SecTyT`. -/
theorem ptime_rejected_TD : secCheckTD Phigh [] Ptime = false := by decide

/-- Declared, it type-checks. -/
theorem ptime_checksTD :
    secCheckTD Phigh [Permit.guard (.var "b")] Ptime = true := by decide

/-- **The timing is released to the declared bit.** The whole outcome of
    `Ptime` — its running time included — reveals at most `relOf Phigh Ptime`,
    whose leading component is the branch bit `(b ≠ 0)`. Declassification turned
    the brick-5-rejected leak into a bounded, declared release. -/
theorem ptime_timing_released :
    ReleasesAtMost Ptime (outO Phigh) Phigh (relOf Phigh Ptime) :=
  releasesAtMost_of_checkTD ptime_checksTD

/-- The concrete consequence: `Ptime`'s running time is a function of the
    secret bit alone — two runs agreeing on `(b ≠ 0)` take the same time. The
    declassified-timing bound, made explicit. -/
theorem ptime_wall_of_bit (σ σ' : Store)
    (hbit : (σ "b" ≠ 0) ↔ (σ' "b" ≠ 0)) :
    (eval Ptime σ).2.1 = (eval Ptime σ').2.1 := by
  simp only [Ptime, eval, evalE]
  by_cases h : σ "b" ≠ 0 <;> by_cases h' : σ' "b" ≠ 0 <;> simp_all

end ConfTyping
