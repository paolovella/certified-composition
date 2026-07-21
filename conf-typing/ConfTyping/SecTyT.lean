/-
  Timing-sensitive certification — brick 5: the checker certifies the clock.

  Brick 3's `typed_but_wall_leaks` was an honesty theorem: the store-only
  checker `secCheck` accepts programs that leak through the instrumented
  channels (a High-guarded branch with unequal branch costs leaks its running
  time). This module closes that gap with a *timing-sensitive* checker.

  `SecTyT` is the flow discipline with High-guarded branches **forbidden**
  (only `iteL` — Low guards — survive; there is no `iteH`), so two Low-equal
  runs always take the same branch, hence agree on cost and trace as well as
  the store. Soundness (`secTyT_sound`) is `J_NI c (outO P) P` — the *whole*
  instrumented outcome (`outO = tup resultO (tup wall branchO)`: Low store,
  cost, trace) is Low-determined. The executable `secCheckT` certifies by
  `decide`, it refines the store checker (`secCheckT_imp_secCheck`), and it
  rejects the brick-3 leak witness `Ptime` (`ptime_rejected_T`) — correctly,
  since `typed_but_wall_leaks` proved that program does leak the clock.

  Honest scope: this certifies timing-*insensitivity* (no secret-dependent
  branching). A program that must branch on a secret is rejected, not repaired
  — closing the channel by construction, the price being expressiveness. The
  declassified case (a High branch whose timing is *declared* released) is the
  Policy-stratum analogue, left to a later brick.
-/
import ConfTyping.SecTy

namespace ConfTyping

/-! ## The timing-sensitive judgment: no High-guarded branches -/

/-- Timing-sensitive flow typing. Identical to `SecTy` at `pc = false` **minus
    the `iteH` rule**: a branch on a non-Low guard is rejected, because the two
    runs could take different branches and diverge in cost/trace. No `pc` is
    needed — without `iteH` the context never goes High. -/
inductive SecTyT (P : Partition) : Cmd → Prop where
  | skip    : SecTyT P .skip
  | assignH : ∀ x e, P x = true → SecTyT P (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → SecTyT P (.assign x e)
  | seq     : SecTyT P c₁ → SecTyT P c₂ → SecTyT P (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → SecTyT P c₁ → SecTyT P c₂ →
              SecTyT P (.ite e c₁ c₂)

/-- Timing-sensitive typing refines store typing: it is `SecTy` at `pc = false`
    (drop the timing obligation and you have the brick-3 discipline). -/
theorem SecTyT.toSecTy {P : Partition} {c : Cmd} (h : SecTyT P c) :
    SecTy P false c := by
  induction h with
  | skip => exact .skip
  | assignH x e hx => exact .assignH x e hx
  | assignL x e he => exact .assignL x e he
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | iteL e he _ _ ih₁ ih₂ => exact .iteL e he ih₁ ih₂

/-! ## Soundness: the whole instrumented outcome is Low-determined -/

/-- The full-outcome noninterference predicate: Low store, cost, and trace all
    agree between Low-equal runs. -/
def OutNI (c : Cmd) (P : Partition) : Prop :=
  ∀ σ σ', lowEq P σ σ' →
    lowEq P (evalStore c σ) (evalStore c σ')
      ∧ (eval c σ).2.1 = (eval c σ').2.1
      ∧ (eval c σ).2.2 = (eval c σ').2.2

theorem secTyT_outNI {P : Partition} {c : Cmd} (h : SecTyT P c) : OutNI c P := by
  induction h with
  | skip => intro σ σ' hle; exact ⟨hle, rfl, rfl⟩
  | assignH x e hx =>
      intro σ σ' hle
      refine ⟨?_, rfl, rfl⟩
      intro y hy
      have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      simp only [upd, if_neg hyx]
      exact hle y hy
  | assignL x e he =>
      intro σ σ' hle
      refine ⟨?_, rfl, rfl⟩
      intro y hy
      show upd σ x (evalE e σ) y = upd σ' x (evalE e σ') y
      simp only [upd]
      by_cases hyx : y = x
      · rw [if_pos hyx, if_pos hyx, evalE_lowEq e he hle]
      · rw [if_neg hyx, if_neg hyx]; exact hle y hy
  | seq h₁ h₂ ih₁ ih₂ =>
      intro σ σ' hle
      obtain ⟨hs₁, hc₁, ht₁⟩ := ih₁ σ σ' hle
      obtain ⟨hs₂, hc₂, ht₂⟩ := ih₂ _ _ hs₁
      refine ⟨hs₂, ?_, ?_⟩
      · show (eval _ σ).2.1 + (eval _ (evalStore _ σ)).2.1
             = (eval _ σ').2.1 + (eval _ (evalStore _ σ')).2.1
        rw [hc₁, hc₂]
      · show (eval _ σ).2.2 ++ (eval _ (evalStore _ σ)).2.2
             = (eval _ σ').2.2 ++ (eval _ (evalStore _ σ')).2.2
        rw [ht₁, ht₂]
  | iteL e he _ _ ih₁ ih₂ =>
      intro σ σ' hle
      have hgv : evalE e σ = evalE e σ' := evalE_lowEq e he hle
      by_cases hb : evalE e σ ≠ 0
      · have hb' : evalE e σ' ≠ 0 := by rwa [hgv] at hb
        obtain ⟨hs, hc, ht⟩ := ih₁ σ σ' hle
        refine ⟨?_, ?_, ?_⟩
        · show lowEq P (eval (.ite e _ _) σ).1 (eval (.ite e _ _) σ').1
          simp only [eval, if_pos hb, if_pos hb']; exact hs
        · show (eval (.ite e _ _) σ).2.1 = (eval (.ite e _ _) σ').2.1
          simp only [eval, if_pos hb, if_pos hb']; rw [hc]
        · show (eval (.ite e _ _) σ).2.2 = (eval (.ite e _ _) σ').2.2
          simp only [eval, if_pos hb, if_pos hb']; rw [ht]
      · have hb' : ¬ evalE e σ' ≠ 0 := by rwa [hgv] at hb
        obtain ⟨hs, hc, ht⟩ := ih₂ σ σ' hle
        refine ⟨?_, ?_, ?_⟩
        · show lowEq P (eval (.ite e _ _) σ).1 (eval (.ite e _ _) σ').1
          simp only [eval, if_neg hb, if_neg hb']; exact hs
        · show (eval (.ite e _ _) σ).2.1 = (eval (.ite e _ _) σ').2.1
          simp only [eval, if_neg hb, if_neg hb']; rw [hc]
        · show (eval (.ite e _ _) σ).2.2 = (eval (.ite e _ _) σ').2.2
          simp only [eval, if_neg hb, if_neg hb']; rw [ht]

/-- The full-outcome predicate is the channel claim `J_NI c (outO P) P`. -/
theorem outNI_to_JNI {P : Partition} {c : Cmd} (h : OutNI c P) :
    J_NI c (outO P) P := by
  intro σ σ' hle
  obtain ⟨hs, hc, ht⟩ := h σ σ' hle
  simp only [obs, outO, tup, resultO, wall, branchO]
  congr 1
  · congr 1
    funext y
    cases hPy : P y with
    | true  => simp
    | false => simp only [Bool.false_eq_true, if_false]; exact hs y hPy
  · rw [hc, ht]

/-- **Soundness.** A timing-sensitively typed component's whole instrumented
    outcome — Low store, running time, and branch trace — is Low-determined.
    The clock is certified, not just the store. -/
theorem secTyT_sound {P : Partition} {c : Cmd} (h : SecTyT P c) :
    J_NI c (outO P) P :=
  outNI_to_JNI (secTyT_outNI h)

/-! ## The executable timing-sensitive checker -/

def secCheckT (P : Partition) : Cmd → Bool
  | .skip        => true
  | .assign x e  => P x || exprLow P e
  | .seq c₁ c₂   => secCheckT P c₁ && secCheckT P c₂
  | .ite e c₁ c₂ => exprLow P e && secCheckT P c₁ && secCheckT P c₂

theorem secCheckT_sound {P : Partition} :
    ∀ {c : Cmd}, secCheckT P c = true → SecTyT P c
  | .skip, _ => .skip
  | .assign _ _, h => by
      simp only [secCheckT, Bool.or_eq_true] at h
      rcases h with hx | he
      · exact .assignH _ _ hx
      · exact .assignL _ _ he
  | .seq _ _, h => by
      simp only [secCheckT, Bool.and_eq_true] at h
      exact .seq (secCheckT_sound h.1) (secCheckT_sound h.2)
  | .ite _ _ _, h => by
      simp only [secCheckT, Bool.and_eq_true] at h
      exact .iteL _ h.1.1 (secCheckT_sound h.1.2) (secCheckT_sound h.2)

/-- **Certificates by `decide`.** One timing-sensitive check yields
    full-outcome noninterference. -/
theorem outNI_of_checkT {P : Partition} {c : Cmd}
    (h : secCheckT P c = true) : J_NI c (outO P) P :=
  secTyT_sound (secCheckT_sound h)

/-- The timing-sensitive checker refines the store checker: certifying the
    clock implies certifying the store. -/
theorem secCheckT_imp_secCheck {P : Partition} :
    ∀ {c : Cmd}, secCheckT P c = true → secCheck P false c = true
  | .skip, _ => rfl
  | .assign _ _, h => h
  | .seq _ _, h => by
      simp only [secCheckT, secCheck, Bool.and_eq_true] at h ⊢
      exact ⟨secCheckT_imp_secCheck h.1, secCheckT_imp_secCheck h.2⟩
  | .ite _ _ _, h => by
      simp only [secCheckT, Bool.and_eq_true] at h
      simp only [secCheck, Bool.or_eq_true, Bool.and_eq_true]
      exact Or.inl ⟨⟨h.1.1, secCheckT_imp_secCheck h.1.2⟩,
                    secCheckT_imp_secCheck h.2⟩

/-! ## Non-vacuity and teeth -/

/-- A timing-insensitive program is certified for the whole outcome by a
    `decide`. -/
theorem pok_outNI : J_NI Pok (outO Phigh) Phigh :=
  outNI_of_checkT (by decide)

/-- **The timing-sensitive checker rejects the brick-3 leak witness.** `Ptime`
    branches on the secret `b` with unequal branch costs; `secCheck` accepted
    it (`typed_but_wall_leaks`), but `secCheckT` rejects it — correctly, since
    that program provably leaks the clock. The two checkers bracket the timing
    channel: `secCheck` = store-safe, `secCheckT` = store- and clock-safe. -/
theorem ptime_rejected_T : secCheckT Phigh Ptime = false := by decide

end ConfTyping
