/-
  The checker, Policy form — brick 3, session 2: declassification typing and
  the ledger.

  `SecTyD P Δ pc c` extends the session-1 discipline with *declared* releases:
  a policy environment `Δ` of permits (released expression values, released
  guard bits). Declaring is not a free pass twice over: (1) the checker
  requires membership — an undeclared High flow is rejected (`Pfull` with an
  empty budget); (2) what a typed program actually reveals is *computed from
  the syntax* as `relOf P c` — the **ledger** — and soundness proves
  `BoundaryReleases c P (relOf P c)`.

  The ledger composes by the brick-2 certificate algebra, definitionally:

      relOf P (c₁; c₂) = seqRelease c₁ (relOf P c₁) (relOf P c₂)   (`rfl`)

  — the checker's output for a pipeline is the seam theorem's computed
  certificate, no translation layer.

  The money theorem: `P_leak` type-checks under the single declared guard
  permit, and the checker-derived certificate *rederives the hand-proved
  Paper-1 bound* — `checker_rederives_pleak_bound` has the same statement as
  `result_releases_at_most_bit`, proved from `decide` + soundness instead of
  a bespoke semantic argument.

  Honesty: `relOf` is deliberately coarse for undeclared High guards (it
  includes the branch bit even when confinement makes the release vacuous) —
  coarser φ means a weaker, still-sound claim; precision matters only where
  declassification is real. The instrumented channels (wall/branch) remain
  session-1-honest: `relOf` certifies the store boundary.
-/
import ConfTyping.SecTy
import ConfTyping.FlowBridge

namespace ConfTyping

deriving instance DecidableEq for Expr

/-- A declared release permit: the value of an expression, or the branch bit
    of a guard. -/
inductive Permit where
  | expr  : Expr → Permit
  | guard : Expr → Permit
deriving DecidableEq

/-! ## The ledger: what a program reveals, computed from syntax -/

/-- **The derived release (the ledger).** What the component reveals about
    High, read off the syntax: nothing for Low writes; the expression value
    for declared High writes; for sequencing, the first ledger paired with
    the second *evaluated at the boundary* — exactly `seqRelease`; for
    branches on a non-Low guard, the branch bit paired with both branches'
    ledgers. -/
def relOf (P : Partition) : Cmd → Release
  | .skip => fun _ => .int 0
  | .assign _ e =>
      if exprLow P e then (fun _ => .int 0) else (fun σ => .int (evalE e σ))
  | .seq c₁ c₂ => fun σ => .pair (relOf P c₁ σ) (relOf P c₂ (evalStore c₁ σ))
  | .ite e c₁ c₂ =>
      if exprLow P e then
        fun σ => .pair (relOf P c₁ σ) (relOf P c₂ σ)
      else
        fun σ => .pair (.int (if evalE e σ ≠ 0 then 1 else 0))
                       (.pair (relOf P c₁ σ) (relOf P c₂ σ))

/-- **The ledger composes by the brick-2 certificate algebra** — the
    checker's output for a pipeline is the seam theorem's computed
    certificate, definitionally. -/
theorem relOf_seq (P : Partition) (c₁ c₂ : Cmd) :
    relOf P (.seq c₁ c₂) = seqRelease c₁ (relOf P c₁) (relOf P c₂) := rfl

/-! ## The judgment -/

/-- Policy-form flow typing: the session-1 rules, plus declared High writes
    (`assignD`) and declared guards (`iteD`) — both only in the Low context
    (a declassification *inside* a secret branch would leak through its own
    occurrence). -/
inductive SecTyD (P : Partition) (Δ : List Permit) : Bool → Cmd → Prop where
  | skip    : SecTyD P Δ pc .skip
  | assignH : ∀ x e, P x = true → SecTyD P Δ pc (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → SecTyD P Δ false (.assign x e)
  | assignD : ∀ x e, Permit.expr e ∈ Δ → SecTyD P Δ false (.assign x e)
  | seq     : SecTyD P Δ pc c₁ → SecTyD P Δ pc c₂ → SecTyD P Δ pc (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → SecTyD P Δ pc c₁ → SecTyD P Δ pc c₂ →
              SecTyD P Δ pc (.ite e c₁ c₂)
  | iteH    : SecTyD P Δ true c₁ → SecTyD P Δ true c₂ →
              SecTyD P Δ pc (.ite e c₁ c₂)
  | iteD    : ∀ e, Permit.guard e ∈ Δ →
              SecTyD P Δ false c₁ → SecTyD P Δ false c₂ →
              SecTyD P Δ false (.ite e c₁ c₂)

/-- Session-1 derivations lift (with any budget). -/
theorem SecTyD.ofSecTy {P : Partition} {Δ : List Permit} :
    ∀ {pc c}, SecTy P pc c → SecTyD P Δ pc c := by
  intro pc c h
  induction h with
  | skip => exact .skip
  | assignH x e hx => exact .assignH x e hx
  | assignL x e he => exact .assignL x e he
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteL e he _ _ ih₁ ih₂ => exact .iteL e he ih₁ ih₂
  | iteH _ _ ih₁ ih₂ => exact .iteH ih₁ ih₂

/-! ## Soundness -/

/-- The shared branch case: if both branches carry their ledgers, the
    conditional carries its ledger — the guard is either Low (same branch by
    `evalE_lowEq`) or its bit is in the ledger (same branch by agreement). -/
theorem ite_aux {P : Partition} {e : Expr} {c₁ c₂ : Cmd}
    (ih₁ : BoundaryReleases c₁ P (relOf P c₁))
    (ih₂ : BoundaryReleases c₂ P (relOf P c₂)) :
    BoundaryReleases (.ite e c₁ c₂) P (relOf P (.ite e c₁ c₂)) := by
  intro σ σ' hle hφ
  by_cases hg : exprLow P e = true
  · simp only [relOf, ite_eq_left hg] at hφ
    injection hφ with hφ₁ hφ₂
    have hgv : evalE e σ = evalE e σ' := evalE_lowEq e hg hle
    show lowEq P ((eval (.ite e c₁ c₂) σ).1) ((eval (.ite e c₁ c₂) σ').1)
    simp only [eval, ← hgv]
    split
    · exact ih₁ σ σ' hle hφ₁
    · exact ih₂ σ σ' hle hφ₂
  · simp only [relOf, ite_eq_right hg] at hφ
    injection hφ with hbit hφr
    injection hφr with hφ₁ hφ₂
    injection hbit with hbit
    have hgv : (evalE e σ ≠ 0) ↔ (evalE e σ' ≠ 0) := by
      by_cases h₁ : evalE e σ ≠ 0 <;> by_cases h₂ : evalE e σ' ≠ 0 <;>
        simp [h₁, h₂] at hbit ⊢
    show lowEq P ((eval (.ite e c₁ c₂) σ).1) ((eval (.ite e c₁ c₂) σ').1)
    by_cases hb : evalE e σ ≠ 0
    · have hb' : evalE e σ' ≠ 0 := hgv.mp hb
      simp only [eval, ite_eq_left hb, ite_eq_left hb']
      exact ih₁ σ σ' hle hφ₁
    · have hb' : ¬ evalE e σ' ≠ 0 := fun h => hb (hgv.mpr h)
      simp only [eval, ite_eq_right hb, ite_eq_right hb']
      exact ih₂ σ σ' hle hφ₂

/-- **Soundness, Policy form.** A typed component reveals at most its
    ledger: the boundary-release certificate with the checker-computed φ.
    The `seq` case is definitionally the brick-2 seam theorem. -/
theorem secTyD_sound {P : Partition} {Δ : List Permit} {pc : Bool} {c : Cmd}
    (h : SecTyD P Δ pc c) : BoundaryReleases c P (relOf P c) := by
  induction h with
  | skip => intro σ σ' hle _; exact hle
  | assignH y e hyH =>
      intro σ σ' hle _ x hx
      show upd σ y (evalE e σ) x = upd σ' y (evalE e σ') x
      have hxy : x ≠ y := fun hxy => by rw [hxy, hyH] at hx; cases hx
      simp only [upd, ite_eq_right hxy]
      exact hle x hx
  | assignL y e he =>
      intro σ σ' hle _ x hx
      show upd σ y (evalE e σ) x = upd σ' y (evalE e σ') x
      simp only [upd]
      by_cases hxy : x = y
      · rw [ite_eq_left hxy, ite_eq_left hxy, evalE_lowEq e he hle]
      · rw [ite_eq_right hxy, ite_eq_right hxy]; exact hle x hx
  | assignD y e _ =>
      intro σ σ' hle hφ x hx
      show upd σ y (evalE e σ) x = upd σ' y (evalE e σ') x
      have hev : evalE e σ = evalE e σ' := by
        by_cases hl : exprLow P e = true
        · exact evalE_lowEq e hl hle
        · simp only [relOf, ite_eq_right hl] at hφ
          injection hφ
      simp only [upd, hev]
      by_cases hxy : x = y
      · rw [ite_eq_left hxy, ite_eq_left hxy]
      · rw [ite_eq_right hxy, ite_eq_right hxy]; exact hle x hx
  | seq _ _ ih₁ ih₂ => exact boundaryReleases_seq ih₁ ih₂
  | iteL e _ _ _ ih₁ ih₂ => exact ite_aux ih₁ ih₂
  | iteH _ _ ih₁ ih₂ => exact ite_aux ih₁ ih₂
  | iteD e _ _ _ ih₁ ih₂ => exact ite_aux ih₁ ih₂

/-! ## The executable checker, Policy form -/

def secCheckD (P : Partition) (Δ : List Permit) : Bool → Cmd → Bool
  | _,  .skip => true
  | pc, .assign x e =>
      P x || (!pc && exprLow P e) || (!pc && decide (Permit.expr e ∈ Δ))
  | pc, .seq c₁ c₂ => secCheckD P Δ pc c₁ && secCheckD P Δ pc c₂
  | pc, .ite e c₁ c₂ =>
      (exprLow P e && secCheckD P Δ pc c₁ && secCheckD P Δ pc c₂)
        || (secCheck P true c₁ && secCheck P true c₂)
        || (!pc && decide (Permit.guard e ∈ Δ)
              && secCheckD P Δ false c₁ && secCheckD P Δ false c₂)

theorem secCheckD_sound {P : Partition} {Δ : List Permit} :
    ∀ {c : Cmd} {pc : Bool}, secCheckD P Δ pc c = true → SecTyD P Δ pc c
  | .skip, _, _ => .skip
  | .assign _ _, pc, h => by
      simp only [secCheckD, Bool.or_eq_true, Bool.and_eq_true,
                 Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
      rcases h with (hx | ⟨hpc, he⟩) | ⟨hpc, hm⟩
      · exact .assignH _ _ hx
      · subst hpc; exact .assignL _ _ he
      · subst hpc; exact .assignD _ _ hm
  | .seq _ _, pc, h => by
      simp only [secCheckD, Bool.and_eq_true] at h
      exact .seq (secCheckD_sound h.1) (secCheckD_sound h.2)
  | .ite _ _ _, pc, h => by
      simp only [secCheckD, Bool.or_eq_true, Bool.and_eq_true,
                 Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
      rcases h with (⟨⟨hg, h₁⟩, h₂⟩ | ⟨h₁, h₂⟩) | ⟨⟨⟨hpc, hm⟩, h₁⟩, h₂⟩
      · exact .iteL _ hg (secCheckD_sound h₁) (secCheckD_sound h₂)
      · exact .iteH (SecTyD.ofSecTy (secCheck_sound h₁))
                    (SecTyD.ofSecTy (secCheck_sound h₂))
      · subst hpc
        exact .iteD _ hm (secCheckD_sound h₁) (secCheckD_sound h₂)

/-- **Certificates by `decide`, Policy form.** One decidable check yields the
    boundary-release certificate with the computed ledger. -/
theorem boundaryReleases_of_check {P : Partition} {Δ : List Permit} {c : Cmd}
    (h : secCheckD P Δ false c = true) : BoundaryReleases c P (relOf P c) :=
  secTyD_sound (secCheckD_sound h)

/-! ## The teeth: declaration is required, and visible -/

/-- With an empty budget, the full-copy program is rejected. -/
theorem pfull_rejected_undeclared :
    secCheckD Phigh [] false Pfull = false := by decide

/-- Declared, it passes — and the ledger *shows* the full release: the
    declaration is not a bypass, it is a visible line item. -/
theorem pfull_accepted_declared :
    secCheckD Phigh [Permit.expr (.var "b")] false Pfull = true := by decide

theorem pfull_ledger :
    relOf Phigh Pfull = fun σ => .int (σ "b") := rfl

/-! ## The money theorem: the checker rederives the Paper-1 bound -/

/-- `P_leak` type-checks under the single declared guard permit. -/
theorem pleak_checksD :
    secCheckD Phigh [Permit.guard (.var "b")] false Pleak = true := by decide

/-- **The hand-proved bound, rederived by the checker.** Same statement as
    `result_releases_at_most_bit` (Paper 1, §7.3): the running `P_leak`
    reveals at most the bit `(b ≠ 0)` — proved here from `decide` plus
    soundness, with a two-line massage from the computed ledger
    `⟨bit, ⟨0, 0⟩⟩` to the declared `φ_bit`. The bespoke semantic argument
    is now checker output. -/
theorem checker_rederives_pleak_bound :
    ReleasesAtMost Pleak (resultO Phigh) Phigh φ_bit := by
  have hB : BoundaryReleases Pleak Phigh (relOf Phigh Pleak) :=
    boundaryReleases_of_check pleak_checksD
  rw [← boundaryReleases_iff]
  intro σ σ' hle hφ
  apply hB σ σ' hle
  -- φ_bit agreement determines the whole computed ledger ⟨bit, ⟨0,0⟩⟩.
  simp only [φ_bit] at hφ
  injection hφ with hbit
  show Val.pair (.int (if σ "b" ≠ 0 then 1 else 0))
        (.pair (.int 0) (.int 0))
     = Val.pair (.int (if σ' "b" ≠ 0 then 1 else 0))
        (.pair (.int 0) (.int 0))
  rw [hbit]

end ConfTyping
