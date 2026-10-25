/-
  The checker — brick 3, session 1: certificates from syntax (Closure form).

  A syntax-directed flow type system for IMP whose derivations *manufacture*
  the boundary certificates of the seam module: `SecTy P pc c` is the classic
  pc-label discipline (Volpano–Smith shape), `secCheck` is its executable
  form, and soundness (`secTy_boundaryNI`, `boundaryNI_of_check`) turns a
  decidable syntactic check into the semantic certificate `BoundaryNI c P` —
  which then flows through the seam theorems and the Bridge reception
  untouched. Type-check your component; the framework proves it.

  Honesty, stated up front and as theorems:
  * **sound, not complete** — the checker rejects some secure programs
    (`P_leak` is rejected, correctly: `pleak_not_boundaryNI` proved its
    boundary claim false, but a program assigning a *constant* under a High
    guard would be rejected too);
  * **store-boundary only** — a well-typed program can still leak through
    the instrumented channels: `typed_but_wall_leaks` exhibits a checked
    program whose running time reveals the secret. The timing channel needs
    the Policy stratum (session 2) or a padding discipline (out of scope);
  * loop-free IMP, as everywhere in this instance.
-/
import ConfTyping.Compose

namespace ConfTyping

/-! ## Expression labels -/

/-- An expression is Low when every variable it reads is Low. -/
def exprLow (P : Partition) : Expr → Bool
  | .num _   => true
  | .var x   => !(P x)
  | .add a b => exprLow P a && exprLow P b

/-- Low expressions are functions of the Low store. -/
theorem evalE_lowEq {P : Partition} {σ σ' : Store} :
    ∀ e : Expr, exprLow P e = true → lowEq P σ σ' → evalE e σ = evalE e σ'
  | .num _, _, _ => rfl
  | .var x, he, h => by
      simp only [exprLow, Bool.not_eq_eq_eq_not, Bool.not_true] at he
      exact h x he
  | .add a b, he, h => by
      simp only [exprLow, Bool.and_eq_true] at he
      simp only [evalE, evalE_lowEq a he.1 h, evalE_lowEq b he.2 h]

/-! ## The judgment -/

/-- The flow typing judgment. `pc = true` is a High context (inside a branch
    on secret data). Reading: `assignH` — High targets absorb anything;
    `assignL` — writes in a Low context may flow anywhere if the expression
    is Low; `iteL` — a Low guard preserves the context; `iteH` — any guard
    is permitted if both branches type in the High context (and hence, by
    confinement, write nothing Low). -/
inductive SecTy (P : Partition) : Bool → Cmd → Prop where
  | skip    : SecTy P pc .skip
  | assignH : ∀ x e, P x = true → SecTy P pc (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → SecTy P false (.assign x e)
  | seq     : SecTy P pc c₁ → SecTy P pc c₂ → SecTy P pc (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → SecTy P pc c₁ → SecTy P pc c₂ →
              SecTy P pc (.ite e c₁ c₂)
  | iteH    : SecTy P true c₁ → SecTy P true c₂ →
              SecTy P pc (.ite e c₁ c₂)

/-! ## Confinement and soundness -/

/-- **Confinement.** A program typed in the High context writes no Low
    variable. -/
theorem confinement_aux {P : Partition} {pc : Bool} {c : Cmd}
    (h : SecTy P pc c) :
    pc = true → ∀ σ x, P x = false → evalStore c σ x = σ x := by
  induction h with
  | skip => intro _ σ x _; rfl
  | assignH y e hyH =>
      intro _ σ x hx
      show upd σ y (evalE e σ) x = σ x
      simp only [upd]
      rw [ite_eq_right (fun hxy : x = y => by rw [hxy, hyH] at hx; cases hx)]
  | assignL y e _ => intro hpc; exact absurd hpc (by decide)
  | seq h₁ h₂ ih₁ ih₂ =>
      intro hpc σ x hx
      show evalStore _ (evalStore _ σ) x = σ x
      rw [ih₂ hpc _ x hx, ih₁ hpc σ x hx]
  | iteL e _ h₁ h₂ ih₁ ih₂ =>
      intro hpc σ x hx
      show (eval (.ite _ _ _) σ).1 x = σ x
      simp only [eval]
      split
      · exact ih₁ hpc σ x hx
      · exact ih₂ hpc σ x hx
  | iteH h₁ h₂ ih₁ ih₂ =>
      intro _ σ x hx
      show (eval (.ite _ _ _) σ).1 x = σ x
      simp only [eval]
      split
      · exact ih₁ rfl σ x hx
      · exact ih₂ rfl σ x hx

theorem confinement {P : Partition} {c : Cmd} (h : SecTy P true c) :
    ∀ σ x, P x = false → evalStore c σ x = σ x :=
  confinement_aux h rfl

/-- **Soundness.** A typed component carries the boundary certificate — in
    either context (High-context programs are boundary-trivial by
    confinement). The seam cases reuse the brick-2 theorems. -/
theorem secTy_boundaryNI {P : Partition} {pc : Bool} {c : Cmd}
    (h : SecTy P pc c) : BoundaryNI c P := by
  induction h with
  | skip => exact boundaryNI_skip P
  | assignH y e hyH =>
      intro σ σ' hle x hx
      show upd σ y (evalE e σ) x = upd σ' y (evalE e σ') x
      have hxy : x ≠ y := fun hxy => by rw [hxy, hyH] at hx; cases hx
      simp only [upd, ite_eq_right hxy]
      exact hle x hx
  | assignL y e he =>
      intro σ σ' hle x hx
      show upd σ y (evalE e σ) x = upd σ' y (evalE e σ') x
      simp only [upd]
      by_cases hxy : x = y
      · rw [ite_eq_left hxy, ite_eq_left hxy, evalE_lowEq e he hle]
      · rw [ite_eq_right hxy, ite_eq_right hxy]; exact hle x hx
  | seq _ _ ih₁ ih₂ => exact boundaryNI_seq ih₁ ih₂
  | iteL e hg _ _ ih₁ ih₂ =>
      intro σ σ' hle
      have hgv : evalE e σ = evalE e σ' := evalE_lowEq e hg hle
      show lowEq P ((eval (.ite e _ _) σ).1) ((eval (.ite e _ _) σ').1)
      simp only [eval, ← hgv]
      split
      · exact ih₁ σ σ' hle
      · exact ih₂ σ σ' hle
  | iteH h₁ h₂ _ _ =>
      rename_i c₁ c₂ pc' e _ih₁ _ih₂
      intro σ σ' hle x hx
      have e₁ : (eval (.ite e c₁ c₂) σ).1 x = σ x := by
        simp only [eval]; split
        · exact confinement h₁ σ x hx
        · exact confinement h₂ σ x hx
      have e₂ : (eval (.ite e c₁ c₂) σ').1 x = σ' x := by
        simp only [eval]; split
        · exact confinement h₁ σ' x hx
        · exact confinement h₂ σ' x hx
      show (eval (.ite e c₁ c₂) σ).1 x = (eval (.ite e c₁ c₂) σ').1 x
      rw [e₁, e₂]
      exact hle x hx

/-! ## The executable checker -/

/-- The checker: a computable shadow of `SecTy`. -/
def secCheck (P : Partition) : Bool → Cmd → Bool
  | _,  .skip        => true
  | pc, .assign x e  => P x || (!pc && exprLow P e)
  | pc, .seq c₁ c₂   => secCheck P pc c₁ && secCheck P pc c₂
  | pc, .ite e c₁ c₂ =>
      (exprLow P e && secCheck P pc c₁ && secCheck P pc c₂)
        || (secCheck P true c₁ && secCheck P true c₂)

/-- The checker is sound for the judgment. (Completeness is not claimed —
    the judgment itself is already incomplete for semantic security, which
    is the usual and correct price of decidability.) -/
theorem secCheck_sound {P : Partition} :
    ∀ {c : Cmd} {pc : Bool}, secCheck P pc c = true → SecTy P pc c
  | .skip, _, _ => .skip
  | .assign _ _, pc, h => by
      simp only [secCheck, Bool.or_eq_true, Bool.and_eq_true,
                 Bool.not_eq_eq_eq_not, Bool.not_true] at h
      rcases h with hx | ⟨hpc, he⟩
      · exact .assignH _ _ hx
      · subst hpc; exact .assignL _ _ he
  | .seq _ _, pc, h => by
      simp only [secCheck, Bool.and_eq_true] at h
      exact .seq (secCheck_sound h.1) (secCheck_sound h.2)
  | .ite _ _ _, pc, h => by
      simp only [secCheck, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨⟨hg, h₁⟩, h₂⟩ | ⟨h₁, h₂⟩
      · exact .iteL _ hg (secCheck_sound h₁) (secCheck_sound h₂)
      · exact .iteH (secCheck_sound h₁) (secCheck_sound h₂)

/-- **The checker manufactures certificates.** One decidable check yields
    the semantic boundary certificate — the input to every seam theorem and
    the Bridge reception. -/
theorem boundaryNI_of_check {P : Partition} {c : Cmd}
    (h : secCheck P false c = true) : BoundaryNI c P :=
  secTy_boundaryNI (secCheck_sound h)

/-- And the sink-channel claim, through the brick-2 equivalence. -/
theorem resultNI_of_check {P : Partition} {c : Cmd}
    (h : secCheck P false c = true) : J_NI c (resultO P) P :=
  (boundaryNI_iff_resultNI c P).mp (boundaryNI_of_check h)

/-! ## Non-vacuity, both ways -/

/-- A two-instruction component: publish a constant, shuffle the secret. -/
def Pok : Cmd := .seq (.assign "l" (.num 7)) (.assign "b" (.var "b"))

theorem pok_checks : secCheck Phigh false Pok = true := by decide

/-- Checked, hence certified — no manual proof about `P_ok` anywhere. -/
theorem pok_certified : BoundaryNI Pok Phigh :=
  boundaryNI_of_check pok_checks

/-- Checker output composes through the seam: certified pipeline, zero
    per-composite reasoning. -/
theorem pok_seq_certified : BoundaryNI (.seq Pok Pok) Phigh :=
  boundaryNI_seq pok_certified pok_certified

/-- **The checker rejects `P_leak`** — and brick 2 proved that rejection
    semantically correct (`pleak_not_boundaryNI`): checker and semantics
    point at the same culprit. -/
theorem pleak_rejected : secCheck Phigh false Pleak = false := by decide

/-! ## The honesty theorem: store-soundness is not timing-soundness -/

/-- A High guard with unequal branch *costs*: types fine, leaks time. -/
def Ptime : Cmd := .ite (.var "b") (.seq .skip .skip) .skip

theorem wall_Ptime_σ0 : (eval Ptime σ0).2.1 = 3 := by
  simp [Ptime, eval, evalE, σ0, upd]

theorem wall_Ptime_σ1 : (eval Ptime σ1).2.1 = 2 := by
  simp [Ptime, eval, evalE, σ1]

/-- **Typed, but the clock leaks.** `P_time` passes the checker and its
    running time reveals the secret bit: session-1 soundness certifies the
    *store* boundary only. The wall channel needs the Policy stratum
    (declared releases cover the guard — session 2) or a padding discipline
    (a different brick). Stated as a theorem so the claim cannot quietly
    inflate. -/
theorem typed_but_wall_leaks :
    secCheck Phigh false Ptime = true ∧ ¬ J_NI Ptime wall Phigh := by
  refine ⟨by decide, ?_⟩
  intro h
  have key := h σ0 σ1 lowEq_σ
  simp only [obs, wall] at key
  rw [wall_Ptime_σ0, wall_Ptime_σ1] at key
  injection key with h'
  exact absurd h' (by decide)

end ConfTyping
