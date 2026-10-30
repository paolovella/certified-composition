/-
  **`bcheck`'s memory safety on every partial run** (F2 step 3, port 3 of 4). Not Ring 0.

  `SepCert.safe` gives `err = false` at the end of runs `uexec` finishes. A fault inside a loop
  kills the run, and on `uexec` the dead loop never returns, so that theorem is silent exactly
  where a fault would be. On `ucmdLangT` a step that faults shows `faultEv` (a trap), so memory
  safety is a statement about the observation: `Cert.trace (fun evs => faultEv ∉ evs)`. Proved by
  induction on `bcheckF`'s rules, as for mediation: at each finished sub-run the bridge and the
  existing `SepCert` give the memory invariant at its end (`sepInv_done`), and an atomic step
  `allcheck` accepts cannot fault from a state with the invariant (`allcheck_no_fault`).
-/
import ConfTyping.MedT

namespace ConfTyping

theorem mem_dropStr {x y : String} : ∀ {V : List String}, y ∈ V → y ≠ x → y ∈ dropStr x V
  | [], h, _ => by simp at h
  | z :: zs, h, hne => by
    simp only [dropStr]
    rcases List.mem_cons.mp h with h | h
    · subst h; simp [hne]
    · split
      · exact mem_dropStr h hne
      · exact List.mem_cons_of_mem _ (mem_dropStr h hne)

/-- No step of a fault-free atomic command shows a fault. -/
theorem stepT_no_fault {c : UCmd} {π : MedPolicy} {s : UState}
    (hok : ∀ r, uexec 1 c π s = some r → r.1.err = false) : faultEv ∉ (stepT c π s).ev := by
  unfold stepT
  split
  · rename_i r hr
    simp only [hok r hr, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil]
    intro h
    cases c with
    | sop op x e => cases op <;> simp [stepEv, faultEv] at h
    | _ => simp [stepEv, faultEv] at h
  · simp

theorem uexecT_atomic_no_fault {c : UCmd} (hc : atomic c = true) {n : Nat} {π : MedPolicy}
    {s : UState} (hok : ∀ r, uexec 1 c π s = some r → r.1.err = false) :
    faultEv ∉ (uexecT n c π s).ev := by
  rcases n with _ | n
  · simp [uexecT]
  cases c with
  | seq | ite | loop => simp [atomic] at hc
  | _ =>
    simp only [uexecT]
    split
    · simp
    · exact stepT_no_fault hok

/-- A finished run carries the memory invariant to its end, by the bridge and `SepCert`. -/
theorem sepInv_done {V V' : List String} {c : UCmd} (hc : SepCert V c V')
    {n : Nat} {π : MedPolicy} {s : UState} (hs : SepInv V s)
    (hdone : (uexecT n c π s).out = .done) : SepInv V' (uexecT n c π s).st :=
  hc.safe n π s _ hs (uexecT_done_agree n c π s hdone).1

/-- An atomic command `allcheck` accepts does not fault from a state with the invariant. -/
theorem allcheck_no_fault {P : Partition} {c : UCmd} {A V A' V' : List String} {k : Nat}
    (h : allcheck P A V c = some (A', V', k)) {π : MedPolicy} {s : UState} (hs : SepInv V s) :
    ∀ r, uexec 1 c π s = some r → r.1.err = false :=
  fun r hr => ((allcheck_sound c A V A' V' k h).joint.toSepCert.safe 1 π s r hs hr).1

/-! ## The counted loop -/

theorem countU_memT (i : String) (body : UCmd) (π : MedPolicy) (W W₂ : List String)
    (hbT : ∀ n s, SepInv W s → faultEv ∉ (uexecT n body π s).ev)
    (hcert : SepCert W (.seq body (decOne i)) W₂) (hsub : ∀ x ∈ W, x ∈ W₂)
    (hdec : ∀ s, SepInv W s → ∀ r, uexec 1 (decOne i) π s = some r → r.1.err = false)
    (hbody : SepCert W body W) :
    ∀ (n : Nat) (s : UState), SepInv W s → faultEv ∉ (uexecT n (countU i body) π s).ev := by
  intro n
  induction n with
  | zero => intro s _ hf; simp [uexecT] at hf
  | succ m ih =>
    intro s hs hf
    by_cases hd : s.dead = true
    · rw [uexecT_dead_ev _ _ _ _ hd] at hf; cases hf
    unfold countU at hf
    simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at hf
    by_cases hg : evalE (.var i) s.store ≠ 0
    · rw [ite_eq_left hg] at hf
      simp only [TRun.tick] at hf
      rcases TRun.seqT_ev_mem hf with h1 | ⟨hdone, h2⟩
      · rcases m with _ | m
        · simp [uexecT] at h1
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at h1
        rcases TRun.seqT_ev_mem h1 with h3 | ⟨hbd, h4⟩
        · exact hbT m s hs h3
        · exact uexecT_atomic_no_fault rfl (hdec _ (sepInv_done hbody hs hbd)) h4
      · exact ih _ (SepInv.mono hsub (sepInv_done hcert hs hdone)) (by unfold countU; exact h2)
    · rw [ite_eq_right hg] at hf; simp at hf

/-! ## The checker's memory safety holds on every partial run -/

/-- **`bcheck`'s memory safety on partial runs.** From a state with the memory invariant for
    the checker's input set, no run, finished, aborted or out of fuel, shows a fault. -/
theorem bcheckF_memT {P : Partition} : ∀ (f : Nat) (c : UCmd) (A V A' V' : List String)
    (k : Nat), bcheckF P f A V c = some (A', V', k) →
      ∀ (n : Nat) (π : MedPolicy) (s : UState), SepInv V s →
        faultEv ∉ (uexecT n c π s).ev := by
  intro f
  induction f with
  | zero => intro c A V A' V' k h; simp [bcheckF] at h
  | succ g ih =>
    intro c A V A' V' k h n π s hs hf
    rcases n with _ | n
    · simp [uexecT] at hf
    by_cases hd : s.dead = true
    · rw [uexecT_dead_ev _ _ _ _ hd] at hf; cases hf
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
              simp only [Bool.and_eq_true, beq_iff_eq] at hsub
              obtain ⟨_, rfl⟩ := hsub
              rw [asFor_eq heq] at hf
              unfold forU at hf
              simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at hf
              rcases TRun.seqT_ev_mem hf with h1 | ⟨hdone, h2⟩
              · have hok := allcheck_no_fault (P := P) (A := A) (A' := A) (V' := dropStr i V)
                  (k := 1) (c := .assign i (.num (m : Int))) (π := π) (by simp [allcheck, exprLow]) hs
                exact uexecT_atomic_no_fault rfl hok h1
              · have hA : SepCert V (.assign i (.num (m : Int))) (dropStr i V) :=
                  (allcheck_sound (P := P) _ A V A (dropStr i V) 1
                    (by simp [allcheck, exprLow])).joint.toSepCert
                have hbc := (bcheckF_sound g body _ _ _ _ _ hbody).joint.toSepCert
                have hdc : SepCert (dropStr i V) (decOne i) (dropStr i (dropStr i V)) :=
                  (allcheck_sound (P := P) _ A₂ (dropStr i V) A₂ (dropStr i (dropStr i V)) 1
                    (by simp [allcheck, decOne, exprLow, hcond.1])).joint.toSepCert
                refine countU_memT i body π (dropStr i V) (dropStr i (dropStr i V))
                  (fun n s hs hf => ih body _ _ _ _ _ hbody n π s hs hf)
                  (SepCert.seq hbc hdc)
                  (fun x hx => mem_dropStr hx (dropStr_ne hx))
                  (fun s hs r hr => allcheck_no_fault (P := P) (A := A₂) (A' := A₂)
                    (V' := dropStr i (dropStr i V)) (k := 1)
                    (by simp [allcheck, decOne, exprLow, hcond.1]) hs r hr)
                  hbc n _ (sepInv_done hA hs hdone) h2
            · cases h
          · cases h
        · cases h
      · obtain ⟨⟨A₁, V₁, k₁⟩, hc₁, hm⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨A₂, V₂, k₂⟩, hc₂, _⟩ := Option.map_eq_some_iff.mp hm
        simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte] at hf
        rcases TRun.seqT_ev_mem hf with h1 | ⟨hdone, h2⟩
        · exact ih c₁ _ _ _ _ _ hc₁ n π s hs h1
        · exact ih c₂ _ _ _ _ _ hc₂ n π _
            (sepInv_done (bcheckF_sound g c₁ _ _ _ _ _ hc₁).joint.toSepCert hs hdone) h2
    | ite e c₁ c₂ =>
      simp only [bcheckF] at h
      split at h
      · split at h
        · rename_i p₁ p₂ h₁ h₂
          obtain ⟨A₁, V₁, k₁⟩ := p₁
          obtain ⟨A₂, V₂, k₂⟩ := p₂
          simp only [uexecT, hd, Bool.false_eq_true, ↓reduceIte, TRun.tick] at hf
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at hf; exact ih c₁ _ _ _ _ _ h₁ n π s hs hf
          · rw [ite_eq_right hg] at hf; exact ih c₂ _ _ _ _ _ h₂ n π s hs hf
        · cases h
      · cases h
    | loop e b => simp only [bcheckF, allcheck] at h; cases h
    | _ =>
      simp only [bcheckF] at h
      exact uexecT_atomic_no_fault rfl (allcheck_no_fault h hs) hf

/-- **The memory-safety certificate on the lawful language.** No run of a `bcheck`-accepted
    program shows a fault: finished, aborted or out of fuel. -/
theorem bcheck_memsafeT {P : Partition} {c : UCmd} {A' V' : List String} {k : Nat}
    (h : bcheck P [] [] c = some (A', V', k)) (π : MedPolicy) :
    LCore.Cert.trace (ucmdLangT P π) (fun evs => faultEv ∉ evs) c :=
  fun n σ _ => bcheckF_memT (usize c) c [] [] A' V' k h n π (initU σ) SepInv.initU

end ConfTyping
