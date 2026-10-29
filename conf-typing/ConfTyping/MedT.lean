/-
  **`bcheck`'s mediation on every partial run** (F2 step 3, port 2 of 4). Not Ring 0.

  `UCert.auth` carries the mediation invariant across runs `uexec` finishes. On `ucmdLangT` a
  run can also abort or run out of fuel, and every read it performed before stopping must
  still be one the policy allows. Reads are now events in program order, so the certificate is
  `Cert.trace (mediated π)`: every `read r` in the trace has `π r`. Proved by induction on
  `bcheckF`'s rules. Only the partial-run half is new: each time a sub-run finishes, the bridge
  (`uexecT_done_agree`) and the existing `UCert.auth` give the invariant at its end
  (`medInv_done`). The counted loop is `countU_medT`.
-/
import ConfTyping.BudgetT

namespace ConfTyping

/-! ## Events of the combinators -/

theorem TRun.seqT_ev_mem {a : TRun} {k : UState → TRun} {x : LCore.Ev}
    (h : x ∈ (a.seqT k).ev) : x ∈ a.ev ∨ (a.out = .done ∧ x ∈ (k a.st).ev) := by
  unfold TRun.seqT at h
  by_cases ha : a.out = .done
  · simp only [ha, ↓reduceIte, List.mem_append] at h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨ha, h⟩
  · simp only [ha, ↓reduceIte] at h; exact Or.inl h

theorem uexecT_dead_ev (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState) (hd : s.dead = true) :
    (uexecT n c π s).ev = [] := by
  cases n <;> simp [uexecT, hd]

/-- Only `access r` produces a read event. -/
theorem stepT_read {c : UCmd} {π : MedPolicy} {s : UState} {r : String}
    (h : LCore.Ev.read r ∈ (stepT c π s).ev) : c = .access r := by
  unfold stepT at h
  split at h
  · cases c with
    | access q => simp [stepEv] at h; rw [h]
    | sop op x e => cases op <;> simp [stepEv] at h
    | _ => simp [stepEv] at h
  · simp at h

/-- A finished run carries the invariant to its end, by the bridge and `UCert.auth`. -/
theorem medInv_done {A A' : List String} {c : UCmd} {k : Nat} (hc : UCert A c A' k)
    {n : Nat} {π : MedPolicy} {s : UState} (hs : UMedInv π A s)
    (hdone : (uexecT n c π s).out = .done) : UMedInv π A' (uexecT n c π s).st :=
  hc.auth n π s _ hs (uexecT_done_agree n c π s hdone).1

/-- On any partial run, only an `access r` reads `r` among the atomic commands. -/
theorem atomic_read {c : UCmd} (hc : atomic c = true) {n : Nat} {π : MedPolicy} {s : UState}
    {r : String} (h : LCore.Ev.read r ∈ (uexecT n c π s).ev) : c = .access r := by
  rcases n with _ | n
  · simp [uexecT] at h
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | _ =>
    simp only [uexecT] at h
    split at h
    · simp at h
    · exact stepT_read h

/-! ## The counted loop -/

/-- **Mediation through a counted loop, on partial runs.** If the body's reads are mediated
    from any state with the invariant for `A`, and a finished turn takes the invariant for `A`
    to one for `A₂ ⊇ A`, every read of the loop is mediated. -/
theorem countU_medT (i : String) (body : UCmd) (π : MedPolicy) (A A₂ : List String) (kk : Nat)
    (hbT : ∀ n s, UMedInv π A s → ∀ r, LCore.Ev.read r ∈ (uexecT n body π s).ev → π r = true)
    (hcert : UCert A (.seq body (decOne i)) A₂ kk) (hsub : ∀ r ∈ A, r ∈ A₂) :
    ∀ (n : Nat) (s : UState), UMedInv π A s →
      ∀ r, LCore.Ev.read r ∈ (uexecT n (countU i body) π s).ev → π r = true := by
  intro n
  induction n with
  | zero => intro s _ r hr; simp [uexecT] at hr
  | succ m ih =>
    intro s hs r hr
    by_cases hd : s.dead = true
    · rw [uexecT_dead_ev _ _ _ _ hd] at hr; cases hr
    unfold countU at hr
    simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases hg : evalE (.var i) s.store ≠ 0
    · rw [ite_eq_left hg] at hr
      simp only [TRun.tick] at hr
      rcases TRun.seqT_ev_mem hr with h1 | ⟨hdone, h2⟩
      · -- a read inside the turn is the body's
        rcases m with _ | m
        · simp [uexecT] at h1
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at h1
        rcases TRun.seqT_ev_mem h1 with h3 | ⟨_, h4⟩
        · exact hbT m s hs r h3
        · exact absurd (atomic_read rfl h4) (by simp [decOne])
      · exact ih _ (UMedInv.mono hsub (medInv_done hcert hs hdone)) r (by unfold countU; exact h2)
    · rw [ite_eq_right hg] at hr; simp at hr

/-! ## The checker's mediation holds on every partial run -/

/-- **`bcheck`'s mediation on partial runs.** From a state with the invariant for the
    checker's input set, every read a run performs, finished, aborted or out of fuel, is one
    the policy allows. -/
theorem bcheckF_medT {P : Partition} : ∀ (f : Nat) (c : UCmd) (A V A' V' : List String)
    (k : Nat), bcheckF P f A V c = some (A', V', k) →
      ∀ (n : Nat) (π : MedPolicy) (s : UState), UMedInv π A s →
        ∀ r, LCore.Ev.read r ∈ (uexecT n c π s).ev → π r = true := by
  intro f
  induction f with
  | zero => intro c A V A' V' k h; simp [bcheckF] at h
  | succ g ih =>
    intro c A V A' V' k h n π s hs r hr
    rcases n with _ | n
    · simp [uexecT] at hr
    by_cases hd : s.dead = true
    · rw [uexecT_dead_ev _ _ _ _ hd] at hr; cases hr
    cases c with
    | seq c₁ c₂ =>
      simp only [bcheckF] at h
      split at h
      · rename_i i m body heq
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          split at h
          · rename_i A₂ V₂ b hbody
            split at h
            · rename_i hsub
              simp only [Bool.and_eq_true] at hsub
              rw [asFor_eq heq] at hr
              unfold forU at hr
              simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at hr
              rcases TRun.seqT_ev_mem hr with h1 | ⟨hdone, h2⟩
              · exact absurd (atomic_read rfl h1) (by simp)
              · have hA : UCert A (.assign i (.num (m : Int))) A 1 :=
                  (allcheck_sound (P := P) _ A V A (dropStr i V) 1
                    (by simp [allcheck, exprLow])).bundle
                have hbc := (bcheckF_sound g body _ _ _ _ _ hbody).bundle
                have hdc : UCert A₂ (decOne i) A₂ 1 :=
                  (allcheck_sound (P := P) _ A₂ V₂ A₂ (dropStr i V₂) 1
                    (by simp [allcheck, decOne, exprLow, hcond.1])).bundle
                exact countU_medT i body π A A₂ _
                  (fun n s hs r hr => ih body _ _ _ _ _ hbody n π s hs r hr)
                  (UCert.seq hbc hdc) (subStr_mem hsub.1) n _ (medInv_done hA hs hdone) r h2
            · cases h
          · cases h
        · cases h
      · obtain ⟨⟨A₁, V₁, k₁⟩, hc₁, hm⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨A₂, V₂, k₂⟩, hc₂, _⟩ := Option.map_eq_some_iff.mp hm
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at hr
        rcases TRun.seqT_ev_mem hr with h1 | ⟨hdone, h2⟩
        · exact ih c₁ _ _ _ _ _ hc₁ n π s hs r h1
        · exact ih c₂ _ _ _ _ _ hc₂ n π _
            (medInv_done (bcheckF_sound g c₁ _ _ _ _ _ hc₁).bundle hs hdone) r h2
    | ite e c₁ c₂ =>
      simp only [bcheckF] at h
      split at h
      · split at h
        · rename_i p₁ p₂ h₁ h₂
          obtain ⟨A₁, V₁, k₁⟩ := p₁
          obtain ⟨A₂, V₂, k₂⟩ := p₂
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at hr
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at hr; exact ih c₁ _ _ _ _ _ h₁ n π s hs r hr
          · rw [ite_eq_right hg] at hr; exact ih c₂ _ _ _ _ _ h₂ n π s hs r hr
        · cases h
      · cases h
    | loop e b => simp only [bcheckF, allcheck] at h; cases h
    | access q =>
      have hq := atomic_read rfl hr
      simp only [UCmd.access.injEq] at hq; subst hq
      simp only [bcheckF, allcheck] at h
      split at h
      · rename_i hm
        exact hs.1 q (hs.2.2 (by simpa using hd) q (memStr_mem hm))
      · cases h
    | _ => exact absurd (atomic_read rfl hr) (by simp)

/-- **The mediation certificate on the lawful language.** Every read any run of a
    `bcheck`-accepted program performs is one the policy allows. -/
theorem bcheck_mediatedT {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangT P π) (mediated π) c := by
  intro n σ r hr
  have hinv : UMedInv π [] (initU σ) := ⟨by simp [initU], by simp [initU], by simp⟩
  exact bcheckF_medT (usize c) c [] [] A' V' k h n π (initU σ) hinv r hr

end ConfTyping
