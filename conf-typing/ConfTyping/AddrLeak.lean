/-
  S-OBS: addresses in the leakage.

  PLAN-2026-10 §5 moves every certificate from *state* to *observation*: `Beh` observes events,
  leakage (branches and the **addresses** memory operations touch), cost and outcome, not the
  internal state. `uLowEqA` (`HeapJoint.lean`) equates `fresh`, `freed` and `hlab` across two
  runs, and the plan flagged `JSecTy` as the riskiest certificate to re-state: does
  noninterference survive when the attacker also sees every address?

  It does, for one reason: a variable enters the tracked set `V` only by allocation, and the
  allocator is synchronised across two Low-equal runs. So two runs agree on every tracked
  pointer's value (`AddrEq`), and every memory operation `JSecTy` admits names a tracked pointer.
  This module is additive: nothing existing changes.
-/
import ConfTyping.HeapJoint

namespace ConfTyping

/-- Two live runs agree on the value of every tracked pointer. Once a run has aborted
    (`dead`), every step is a no-op and no address is touched, so nothing is required. -/
def AddrEq (V : List String) (s s' : UState) : Prop :=
  s.dead = false → ∀ x ∈ V, s.store x = s'.store x

/-- The relation on results; mismatched results are excluded by `jsecTy_sound` already. -/
def uOptAddr (V : List String) :
    Option (UState × Nat × List Bool) → Option (UState × Nat × List Bool) → Prop
  | some r, some r' => AddrEq V r.1 r'.1
  | _,      _       => True

theorem AddrEq.mono {V W : List String} {s s' : UState} (hsub : ∀ x ∈ W, x ∈ V)
    (h : AddrEq V s s') : AddrEq W s s' :=
  fun hd x hx => h hd x (hsub x hx)

theorem uOptAddr_map {V : List String} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptAddr V a a')
    {f f' : UState × Nat × List Bool → UState × Nat × List Bool}
    (hf : ∀ r, (f r).1 = r.1) (hf' : ∀ r, (f' r).1 = r.1) :
    uOptAddr V (a.map f) (a'.map f') := by
  cases a with
  | none => cases a' <;> trivial
  | some r => cases a' with
    | none => trivial
    | some r' => show AddrEq V (f r).1 (f' r').1; rw [hf, hf']; exact h

theorem uOptAddr_mono_left {V W : List String} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptAddr V a a') (hsub : ∀ x ∈ W, x ∈ V) : uOptAddr W a a' := by
  cases a with
  | none => cases a' <;> trivial
  | some r => cases a' with
    | none => trivial
    | some r' => exact AddrEq.mono hsub h

/-- **Tracked pointers agree across two Low-equal runs.** If `JSecTy P V c V'` and the usual
    invariants hold, two runs that start agreeing on `V`'s pointers end agreeing on `V'`'s. The
    only case with content is allocation, where both runs take the same address because the
    allocator is synchronised (`uLowEqA`'s `fresh` and `freed`). -/
theorem jsecTy_addrEq {P : Partition} :
    ∀ (n : Nat) (c : UCmd) (V V' : List String), JSecTy P V c V' →
      ∀ (π : MedPolicy) (s s' : UState), SepInv V s → SepInv V s' →
        LabInv P V s → LabInv P V s' → uLowEqA P s s' → AddrEq V s s' →
        uOptAddr V' (uexec n c π s) (uexec n c π s') := by
  intro n
  induction n with
  | zero => intro c V V' _ π s s' _ _ _ _ _ _; simp [uexec, uOptAddr]
  | succ m ih =>
    intro c V V' hc π s s' hI hI' hL hL' hle hA
    obtain ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ := hle
    cases hc with
    | skip _ => simp only [uexec, uOptAddr]; exact hA
    | check _ _ | access _ _ =>
        simp only [uexec, uOptAddr]; intro hd y hy
        by_cases h0 : s.dead = true
        · simp [h0] at hd
        · have h0f : s.dead = false := by simpa using h0
          have h0f' : s'.dead = false := by rw [← hdd]; exact h0f
          simp only [h0f, h0f', Bool.false_eq_true, ite_false] at hd ⊢
          repeat' split
          all_goals first | exact hA h0f y hy | simp_all
    | assignH _ x e _ | assignL _ x e _ =>
        simp only [uexec, uOptAddr]; intro hd y hy
        have hyx : y ≠ x := dropStr_ne hy
        by_cases h0 : s.dead = true
        · simp [h0] at hd
        · have h0f : s.dead = false := by simpa using h0
          have h0f' : s'.dead = false := by rw [← hdd]; exact h0f
          simp only [h0f, h0f', Bool.false_eq_true, ite_false, upd, if_neg hyx]
          exact hA h0f y (dropStr_mem hy)
    | alloc _ x _ | allocS _ x _ =>
        simp only [uexec, uOptAddr]; intro hd y hy
        by_cases h0 : s.dead = true
        · simp [h0] at hd
        · have h0f : s.dead = false := by simpa using h0
          have h0f' : s'.dead = false := by rw [← hdd]; exact h0f
          simp only [h0f, h0f', Bool.false_eq_true, ite_false, upd]
          by_cases hyx : y = x
          · rw [if_pos hyx, if_pos hyx, hfr, hfd]
          · rw [if_neg hyx, if_neg hyx]
            exact hA h0f y (memCons_ne hy hyx)
    | deref _ _ _ | free _ _ _ | setH _ _ _ _ | setL _ _ _ _ | emit _ _ _ _
    | storeL _ _ _ _ _ _ | storeH _ _ _ _ _ =>
        simp only [uexec, uOptAddr]; intro hd y hy
        have hy' : y ∈ V := by first | exact hy | exact dropStr_mem hy
        by_cases h0 : s.dead = true
        · simp [h0] at hd
        · have h0f : s.dead = false := by simpa using h0
          have h0f' : s'.dead = false := by rw [← hdd]; exact h0f
          simp only [h0f, h0f', Bool.false_eq_true, ite_false] at hd ⊢
          repeat' split
          all_goals first | exact hA h0f y hy' | simp_all
    | loadL _ d p _ _ | loadH _ d p _ _ =>
        simp only [uexec, uOptAddr]; intro hd y hy
        have hyd : y ≠ d := dropStr_ne hy
        have hy' : y ∈ V := dropStr_mem hy
        by_cases h0 : s.dead = true
        · simp [h0] at hd
        · have h0f : s.dead = false := by simpa using h0
          have h0f' : s'.dead = false := by rw [← hdd]; exact h0f
          simp only [h0f, h0f', Bool.false_eq_true, ite_false] at hd ⊢
          repeat' split
          all_goals first | exact hA h0f y hy' | simp only [upd, if_neg hyd]; exact hA h0f y hy' | simp_all
    | @seq _ V₁ _ c₁ c₂ h₁ h₂ =>
        have hlow := jsecTy_sound m c₁ _ V₁ h₁ π s s' hI hI' hL hL'
          ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
        have hadr := ih c₁ _ V₁ h₁ π s s' hI hI' hL hL'
          ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ hA
        rw [uexec_seq_eq, uexec_seq_eq]
        rcases e₁ : uexec m c₁ π s with _ | r₁ <;> rcases e₁' : uexec m c₁ π s' with _ | r₁'
        · trivial
        · trivial
        · rw [e₁, e₁'] at hlow; exact hlow.elim
        rw [e₁, e₁'] at hlow hadr
        simp only [Option.bind_some]
        have hJ : SepInv V₁ r₁.1 := h₁.toSepCert.safe m π s r₁ hI e₁
        have hJ' : SepInv V₁ r₁'.1 := h₁.toSepCert.safe m π s' r₁' hI' e₁'
        have hLJ : LabInv P V₁ r₁.1 := h₁.toLabInv m π s r₁ hI hL e₁
        have hLJ' : LabInv P V₁ r₁'.1 := h₁.toLabInv m π s' r₁' hI' hL' e₁'
        exact uOptAddr_map (ih c₂ V₁ _ h₂ π r₁.1 r₁'.1 hJ hJ' hLJ hLJ' hlow.1 hadr)
          (fun _ => rfl) (fun _ => rfl)
    | @iteL _ _ _ c₁ c₂ e hg h₁ h₂ =>
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        rw [uexec_ite_eq, uexec_ite_eq]
        by_cases hb : evalE e s.store ≠ 0
        · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_pos hb, if_pos hb']
          exact uOptAddr_map (uOptAddr_mono_left (ih c₁ _ _ h₁ π s s' hI hI' hL hL'
            ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ hA) (fun _ hx => interStr_left hx))
            (fun _ => rfl) (fun _ => rfl)
        · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_neg hb, if_neg hb']
          exact uOptAddr_map (uOptAddr_mono_left (ih c₂ _ _ h₂ π s s' hI hI' hL hL'
            ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ hA) (fun _ hx => interStr_right hx))
            (fun _ => rfl) (fun _ => rfl)
    | @whileW _ _ W₁ c₀ e hg hWV h₀ hWW₁ =>
        have hIV' : SepInv V' s := SepInv.mono hWV hI
        have hIV'' : SepInv V' s' := SepInv.mono hWV hI'
        have hLV' : LabInv P V' s := LabInv.mono hWV hL
        have hLV'' : LabInv P V' s' := LabInv.mono hWV hL'
        have hAV : AddrEq V' s s' := AddrEq.mono hWV hA
        have hbody : SepCert V' c₀ V' := SepCert.weakenPost h₀.toSepCert hWW₁
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        rw [uexec_loop_eq, uexec_loop_eq]
        by_cases hb : evalE e s.store ≠ 0
        · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_pos hb, if_pos hb']
          have hlow := jsecTy_sound m c₀ V' W₁ h₀ π s s' hIV' hIV'' hLV' hLV''
            ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩
          have hadr := ih c₀ V' W₁ h₀ π s s' hIV' hIV'' hLV' hLV''
            ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ hAV
          rcases e₁ : uexec m c₀ π s with _ | r₁ <;> rcases e₁' : uexec m c₀ π s' with _ | r₁'
          · trivial
          · trivial
          · rw [e₁, e₁'] at hlow; exact hlow.elim
          rw [e₁, e₁'] at hlow hadr
          simp only [Option.bind_some]
          have hJ : SepInv V' r₁.1 := hbody.safe m π s r₁ hIV' e₁
          have hJ' : SepInv V' r₁'.1 := hbody.safe m π s' r₁' hIV'' e₁'
          have hLJ : LabInv P V' r₁.1 := LabInv.mono hWW₁ (h₀.toLabInv m π s r₁ hIV' hLV' e₁)
          have hLJ' : LabInv P V' r₁'.1 :=
            LabInv.mono hWW₁ (h₀.toLabInv m π s' r₁' hIV'' hLV'' e₁')
          exact uOptAddr_map
            (ih (.loop e c₀) V' V' (.whileW e hg (fun _ hx => hx) h₀ hWW₁) π r₁.1 r₁'.1
              hJ hJ' hLJ hLJ' hlow.1 (AddrEq.mono hWW₁ hadr))
            (fun _ => rfl) (fun _ => rfl)
        · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_neg hb, if_neg hb']; exact hAV


/-! ## The address trace -/

/-- The addresses a run exposes, in order: every allocation's address and every pointer a
    `deref`, `free`, `load` or `store` goes through. It mirrors `uexec`; an aborted state
    touches nothing. This is the address part of PLAN-2026-10's leakage `Lk`. -/
def uaddrs : Nat → UCmd → MedPolicy → UState → Option (List Int)
  | 0,     _,            _, _ => none
  | _ + 1, .memop op x,  _, s =>
      some (if s.dead then [] else
              match op with
              | .alloc | .allocS => [pickAddr s.freed s.fresh]
              | .deref | .free   => [s.store x])
  | _ + 1, .hop op x y,  _, s =>
      some (if s.dead then [] else
              match op with
              | .load  => [s.store y]
              | .store => [s.store x])
  | n + 1, .seq c₁ c₂,   π, s =>
      (uexec n c₁ π s).bind fun r₁ =>
        (uaddrs n c₁ π s).bind fun a₁ =>
          (uaddrs n c₂ π r₁.1).map fun a₂ => a₁ ++ a₂
  | n + 1, .ite e c₁ c₂, π, s =>
      if evalE e s.store ≠ 0 then uaddrs n c₁ π s else uaddrs n c₂ π s
  | n + 1, .loop e c,    π, s =>
      if evalE e s.store ≠ 0 then
        (uexec n c π s).bind fun r₁ =>
          (uaddrs n c π s).bind fun a₁ =>
            (uaddrs n (.loop e c) π r₁.1).map fun a₂ => a₁ ++ a₂
      else some []
  | _ + 1, _,            _, _ => some []

/-- **Noninterference with addresses in the leakage** (S-OBS). Two Low-equal runs of a
    `JSecTy`-typed program expose the same address trace, secret cells included. -/
theorem jsecTy_addrs {P : Partition} :
    ∀ (n : Nat) (c : UCmd) (V V' : List String), JSecTy P V c V' →
      ∀ (π : MedPolicy) (s s' : UState), SepInv V s → SepInv V s' →
        LabInv P V s → LabInv P V s' → uLowEqA P s s' → AddrEq V s s' →
        uaddrs n c π s = uaddrs n c π s' := by
  intro n
  induction n with
  | zero => intro c V V' _ π s s' _ _ _ _ _ _; rfl
  | succ m ih =>
    intro c V V' hc π s s' hI hI' hL hL' hle hA
    have hle₀ := hle
    obtain ⟨hst, hrd, hdd, hfr, hss, hsk, hfd, hhl, hho⟩ := hle
    cases hc with
    | skip _ | assignH _ _ _ _ | assignL _ _ _ _ | check _ _ | access _ _
    | setH _ _ _ _ | setL _ _ _ _ | emit _ _ _ _ => rfl
    | alloc _ x _ | allocS _ x _ => simp only [uaddrs, hdd, hfr, hfd]
    | deref _ x hx | free _ x hx | loadL _ _ x hx _ | loadH _ _ x hx _
    | storeL _ x _ hx _ _ | storeH _ x _ hx _ =>
        simp only [uaddrs]
        by_cases h0 : s.dead = true
        · have h0' : s'.dead = true := by rwa [hdd] at h0
          simp [h0, h0']
        · have h0f : s.dead = false := by simpa using h0
          have h0f' : s'.dead = false := by rw [← hdd]; exact h0f
          simp only [h0f, h0f', Bool.false_eq_true, ite_false, hA h0f x (memStr_mem hx)]
    | @seq _ V₁ _ c₁ c₂ h₁ h₂ =>
        have hlow := jsecTy_sound m c₁ _ V₁ h₁ π s s' hI hI' hL hL' hle₀
        have hadr := jsecTy_addrEq m c₁ _ V₁ h₁ π s s' hI hI' hL hL' hle₀ hA
        have ha₁ := ih c₁ _ V₁ h₁ π s s' hI hI' hL hL' hle₀ hA
        simp only [uaddrs]
        rw [ha₁]
        rcases e₁ : uexec m c₁ π s with _ | r₁ <;> rcases e₁' : uexec m c₁ π s' with _ | r₁'
        · rfl
        · rw [e₁, e₁'] at hlow; exact hlow.elim
        · rw [e₁, e₁'] at hlow; exact hlow.elim
        rw [e₁, e₁'] at hlow hadr
        simp only [Option.bind_some]
        have hJ : SepInv V₁ r₁.1 := h₁.toSepCert.safe m π s r₁ hI e₁
        have hJ' : SepInv V₁ r₁'.1 := h₁.toSepCert.safe m π s' r₁' hI' e₁'
        have hLJ : LabInv P V₁ r₁.1 := h₁.toLabInv m π s r₁ hI hL e₁
        have hLJ' : LabInv P V₁ r₁'.1 := h₁.toLabInv m π s' r₁' hI' hL' e₁'
        rw [ih c₂ V₁ _ h₂ π r₁.1 r₁'.1 hJ hJ' hLJ hLJ' hlow.1 hadr]
    | @iteL _ _ _ c₁ c₂ e hg h₁ h₂ =>
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        simp only [uaddrs, hgv]
        split
        · exact ih c₁ _ _ h₁ π s s' hI hI' hL hL' hle₀ hA
        · exact ih c₂ _ _ h₂ π s s' hI hI' hL hL' hle₀ hA
    | @whileW _ _ W₁ c₀ e hg hWV h₀ hWW₁ =>
        have hIV' : SepInv V' s := SepInv.mono hWV hI
        have hIV'' : SepInv V' s' := SepInv.mono hWV hI'
        have hLV' : LabInv P V' s := LabInv.mono hWV hL
        have hLV'' : LabInv P V' s' := LabInv.mono hWV hL'
        have hAV : AddrEq V' s s' := AddrEq.mono hWV hA
        have hbody : SepCert V' c₀ V' := SepCert.weakenPost h₀.toSepCert hWW₁
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        simp only [uaddrs, hgv]
        split
        · have hlow := jsecTy_sound m c₀ V' W₁ h₀ π s s' hIV' hIV'' hLV' hLV'' hle₀
          have hadr := jsecTy_addrEq m c₀ V' W₁ h₀ π s s' hIV' hIV'' hLV' hLV'' hle₀ hAV
          rw [ih c₀ V' W₁ h₀ π s s' hIV' hIV'' hLV' hLV'' hle₀ hAV]
          rcases e₁ : uexec m c₀ π s with _ | r₁ <;> rcases e₁' : uexec m c₀ π s' with _ | r₁'
          · rfl
          · rw [e₁, e₁'] at hlow; exact hlow.elim
          · rw [e₁, e₁'] at hlow; exact hlow.elim
          rw [e₁, e₁'] at hlow hadr
          simp only [Option.bind_some]
          have hJ : SepInv V' r₁.1 := hbody.safe m π s r₁ hIV' e₁
          have hJ' : SepInv V' r₁'.1 := hbody.safe m π s' r₁' hIV'' e₁'
          have hLJ : LabInv P V' r₁.1 := LabInv.mono hWW₁ (h₀.toLabInv m π s r₁ hIV' hLV' e₁)
          have hLJ' : LabInv P V' r₁'.1 :=
            LabInv.mono hWW₁ (h₀.toLabInv m π s' r₁' hIV'' hLV'' e₁')
          rw [ih (.loop e c₀) V' V' (.whileW e hg (fun _ hx => hx) h₀ hWW₁) π r₁.1 r₁'.1
              hJ hJ' hLJ hLJ' hlow.1 (AddrEq.mono hWW₁ hadr)]
        · rfl

/-- **The program-level statement.** For a `JSecTy`-typed program run from two Low-equal
    initial stores, the address traces are equal: addresses can join the observation, and
    the `JSecTy` certificate survives the move to `Beh` (PLAN-2026-10 §5) with no fallback. -/
theorem jsecTy_addrs_initU {P : Partition} {c : UCmd} {V' : List String}
    (hc : JSecTy P [] c V') (n : Nat) (π : MedPolicy) (σ σ' : Store)
    (hσ : lowEq P σ σ') : uaddrs n c π (initU σ) = uaddrs n c π (initU σ') :=
  jsecTy_addrs n c [] V' hc π (initU σ) (initU σ') SepInv.initU SepInv.initU
    LabInv.initU LabInv.initU
    ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ (fun _ x hx => by cases hx)


/-! ## Witnesses: the trace is not vacuous -/

/-- Two stores that differ only in the secret. -/
def σSecret5 : Store := fun x => if x == "secret" then 5 else 0
def σSecret7 : Store := fun x => if x == "secret" then 7 else 0

/-- Accepted, and touching a **secret cell**: allocate it, store into it, free it. The trace is
    three real addresses, and it is the same whatever the secret is. -/
def secretCellProg : UCmd :=
  .seq (.memop .allocS "secret") (.seq (.hop .store "secret" "secret") (.memop .free "secret"))

theorem secretCellProg_checks : jcheck Psec [] secretCellProg = some [] := by decide

theorem secretCellProg_trace :
    uaddrs 4 secretCellProg (fun _ => true) (initU σSecret5) = some [0, 0, 0]
  ∧ uaddrs 4 secretCellProg (fun _ => true) (initU σSecret7) = some [0, 0, 0] := by decide

/-- Refused, and the trace **sees the secret**: a pointer taken from the secret and
    dereferenced exposes the secret as an address. So the trace can tell secrets apart; what
    keeps it equal is the type system. -/
def secretAddrProg : UCmd := .seq (.assign "p" (.var "secret")) (.memop .deref "p")

theorem secretAddrProg_refused : jcheck Psec [] secretAddrProg = none := by decide

theorem secretAddrProg_trace_differs :
    uaddrs 3 secretAddrProg (fun _ => true) (initU σSecret5) = some [5]
  ∧ uaddrs 3 secretAddrProg (fun _ => true) (initU σSecret7) = some [7] := by decide

end ConfTyping
