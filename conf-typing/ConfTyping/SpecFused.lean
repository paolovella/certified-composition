/-
  The composable core, stage 2i: the fused induction, and the trace theorem.

  Stage 2g ended by naming a place rather than a result: the trace conclusion does not
  factor out of the noninterference proof, so it has to be carried by an induction that
  already threads `SepInv`, `LabInv` and `uLowEqA`. This stage writes that induction and
  cashes it.
-/
import ConfTyping.BigHandler

namespace ConfTyping

/-! ## Atomic commands do not consume fuel -/

/-- The commands `uexec` decides without recursion. Everything except the three
    control-flow formers. -/
def isAtomic : UCmd → Bool
  | .seq _ _   => false
  | .ite _ _ _ => false
  | .loop _ _  => false
  | _          => true

/-- On an atomic command every nonzero fuel gives the same answer, which is what lets
    stage 2f's one-step lemmas be applied inside an induction over fuel. -/
theorem uexec_atomic {c : UCmd} (h : isAtomic c = true) (m : Nat) (π : MedPolicy)
    (s : UState) : uexec (m + 1) c π s = uexec 1 c π s := by
  cases c <;> first | rfl | simp [isAtomic] at h

/-- The pointer invariant is downward closed in the tracked set, which is what a branch
    join needs. -/
theorem PtrLow.mono {V W : List String} {s s' : UState} (hsub : ∀ x ∈ W, x ∈ V)
    (h : PtrLow V s s') : PtrLow W s s' := fun hd x hx => h hd x (hsub x hx)

/-! ## The fused induction -/

/-- **`PtrLow` is inductive over whole certified programs.** The hypothesis list is the
    point: `SepInv`, `LabInv` and `uLowEqA` are all present, because stage 2g proved no
    lighter relation is preserved by a single certified command. -/
theorem jcheck_ptrLow {P : Partition} :
    ∀ (n : Nat) (c : UCmd) (V V' : List String), jcheck P V c = some V' →
      ∀ (π : MedPolicy) (s s' : UState) (r r' : UState × Nat × List Bool),
        SepInv V s → SepInv V s' → LabInv P V s → LabInv P V s' →
        uLowEqA P s s' → PtrLow V s s' →
        uexec n c π s = some r → uexec n c π s' = some r' → PtrLow V' r.1 r'.1 := by
  intro n
  induction n with
  | zero => intro c V V' _ π s s' r r' _ _ _ _ _ _ hr _; simp [uexec] at hr
  | succ m ih =>
    intro c V V' hc π s s' r r' hI hI' hL hL' hlow hp hr hr'
    by_cases hatom : isAtomic c = true
    · rw [uexec_atomic hatom] at hr hr'
      exact ptrLow_step hc hlow hp hr hr'
    · cases c
      case seq c₁ c₂ =>
          simp only [jcheck] at hc
          rcases e₁ : jcheck P V c₁ with _ | V₁
          · rw [e₁] at hc; simp at hc
          rw [e₁, Option.bind_some] at hc
          rw [uexec_seq_eq] at hr hr'
          rcases f₁ : uexec m c₁ π s with _ | r₁
          · rw [f₁] at hr; simp at hr
          rcases f₁' : uexec m c₁ π s' with _ | r₁'
          · rw [f₁'] at hr'; simp at hr'
          rw [f₁, Option.bind_some] at hr
          rw [f₁', Option.bind_some] at hr'
          rcases f₂ : uexec m c₂ π r₁.1 with _ | r₂
          · rw [f₂] at hr; simp at hr
          rcases f₂' : uexec m c₂ π r₁'.1 with _ | r₂'
          · rw [f₂'] at hr'; simp at hr'
          rw [f₂] at hr; rw [f₂'] at hr'
          simp only [Option.map_some, Option.some.injEq] at hr hr'
          have hty₁ := jcheck_sound c₁ V V₁ e₁
          have hS₁ : SepInv V₁ r₁.1 := hty₁.toSepCert.safe m π s r₁ hI f₁
          have hS₁' : SepInv V₁ r₁'.1 := hty₁.toSepCert.safe m π s' r₁' hI' f₁'
          have hL₁ : LabInv P V₁ r₁.1 := hty₁.toLabInv m π s r₁ hI hL f₁
          have hL₁' : LabInv P V₁ r₁'.1 := hty₁.toLabInv m π s' r₁' hI' hL' f₁'
          have hlow₁ : uLowEqA P r₁.1 r₁'.1 := by
            have h := jsecTy_sound m c₁ V V₁ hty₁ π s s' hI hI' hL hL' hlow
            rw [f₁, f₁'] at h; exact h.1
          have hp₁ := ih c₁ V V₁ e₁ π s s' r₁ r₁' hI hI' hL hL' hlow hp f₁ f₁'
          have := ih c₂ V₁ V' hc π r₁.1 r₁'.1 r₂ r₂' hS₁ hS₁' hL₁ hL₁' hlow₁ hp₁ f₂ f₂'
          rw [← hr, ← hr']; exact this
      case ite e c₁ c₂ =>
          simp only [jcheck] at hc
          by_cases he : exprLow P e = true
          · rw [ite_eq_left he] at hc
            rcases e₁ : jcheck P V c₁ with _ | V₁
            · rw [e₁] at hc; simp at hc
            rcases e₂ : jcheck P V c₂ with _ | V₂
            · rw [e₁, e₂] at hc; simp at hc
            rw [e₁, e₂] at hc
            simp only [Option.some.injEq] at hc
            rw [uexec_ite_eq] at hr hr'
            have hguard : evalE e s.store = evalE e s'.store := evalE_lowEq e he hlow.1
            by_cases hg : evalE e s.store ≠ 0
            · have hg' : evalE e s'.store ≠ 0 := by rw [← hguard]; exact hg
              rw [ite_eq_left hg] at hr; rw [ite_eq_left hg'] at hr'
              rcases f₁ : uexec m c₁ π s with _ | r₁
              · rw [f₁] at hr; simp at hr
              rcases f₁' : uexec m c₁ π s' with _ | r₁'
              · rw [f₁'] at hr'; simp at hr'
              rw [f₁] at hr; rw [f₁'] at hr'
              simp only [Option.map_some, Option.some.injEq] at hr hr'
              have hp₁ := ih c₁ V V₁ e₁ π s s' r₁ r₁' hI hI' hL hL' hlow hp f₁ f₁'
              rw [← hc, ← hr, ← hr']
              exact PtrLow.mono (fun _ hx => interStr_left hx) hp₁
            · have hg' : ¬ (evalE e s'.store ≠ 0) := by rw [← hguard]; exact hg
              rw [ite_eq_right hg] at hr; rw [ite_eq_right hg'] at hr'
              rcases f₂ : uexec m c₂ π s with _ | r₂
              · rw [f₂] at hr; simp at hr
              rcases f₂' : uexec m c₂ π s' with _ | r₂'
              · rw [f₂'] at hr'; simp at hr'
              rw [f₂] at hr; rw [f₂'] at hr'
              simp only [Option.map_some, Option.some.injEq] at hr hr'
              have hp₂ := ih c₂ V V₂ e₂ π s s' r₂ r₂' hI hI' hL hL' hlow hp f₂ f₂'
              rw [← hc, ← hr, ← hr']
              exact PtrLow.mono (fun _ hx => interStr_right hx) hp₂
          · rw [ite_eq_right he] at hc; cases hc
      case loop e c₀ =>
          by_cases hcond : (exprLow P e && (jcheck P V c₀ == some V)) = true
          · have hloopc : jcheck P V (.loop e c₀) = some V := by
              simp only [jcheck, ite_eq_left hcond]
            rw [hloopc] at hc
            simp only [Option.some.injEq] at hc
            subst hc
            obtain ⟨he, hbody0⟩ := Bool.and_eq_true .. |>.mp hcond
            have hbody : jcheck P V c₀ = some V := by simpa using hbody0
            rw [uexec_loop_eq] at hr hr'
            have hguard : evalE e s.store = evalE e s'.store := evalE_lowEq e he hlow.1
            by_cases hg : evalE e s.store ≠ 0
            · have hg' : evalE e s'.store ≠ 0 := by rw [← hguard]; exact hg
              rw [ite_eq_left hg] at hr; rw [ite_eq_left hg'] at hr'
              rcases f₁ : uexec m c₀ π s with _ | r₁
              · rw [f₁] at hr; simp at hr
              rcases f₁' : uexec m c₀ π s' with _ | r₁'
              · rw [f₁'] at hr'; simp at hr'
              rw [f₁, Option.bind_some] at hr
              rw [f₁', Option.bind_some] at hr'
              rcases f₂ : uexec m (.loop e c₀) π r₁.1 with _ | r₂
              · rw [f₂] at hr; simp at hr
              rcases f₂' : uexec m (.loop e c₀) π r₁'.1 with _ | r₂'
              · rw [f₂'] at hr'; simp at hr'
              rw [f₂] at hr; rw [f₂'] at hr'
              simp only [Option.map_some, Option.some.injEq] at hr hr'
              have hty₀ := jcheck_sound c₀ V V hbody
              have hS₁ : SepInv V r₁.1 := hty₀.toSepCert.safe m π s r₁ hI f₁
              have hS₁' : SepInv V r₁'.1 := hty₀.toSepCert.safe m π s' r₁' hI' f₁'
              have hL₁ : LabInv P V r₁.1 := hty₀.toLabInv m π s r₁ hI hL f₁
              have hL₁' : LabInv P V r₁'.1 := hty₀.toLabInv m π s' r₁' hI' hL' f₁'
              have hlow₁ : uLowEqA P r₁.1 r₁'.1 := by
                have h := jsecTy_sound m c₀ V V hty₀ π s s' hI hI' hL hL' hlow
                rw [f₁, f₁'] at h; exact h.1
              have hp₁ := ih c₀ V V hbody π s s' r₁ r₁' hI hI' hL hL' hlow hp f₁ f₁'
              have := ih (.loop e c₀) V V hloopc π r₁.1 r₁'.1 r₂ r₂'
                hS₁ hS₁' hL₁ hL₁' hlow₁ hp₁ f₂ f₂'
              rw [← hr, ← hr']; exact this
            · have hg' : ¬ (evalE e s'.store ≠ 0) := by rw [← hguard]; exact hg
              rw [ite_eq_right hg] at hr; rw [ite_eq_right hg'] at hr'
              simp only [Option.some.injEq] at hr hr'
              rw [← hr, ← hr']; exact hp
          · simp only [jcheck, ite_eq_right hcond] at hc; cases hc
      all_goals exact absurd rfl hatom

/-! ## The frame, bundled

    Stage 2g's finding, as a definition: these six are what a trace argument has to carry,
    and `traceEq_is_not_inductive` is the proof that dropping `sep`/`lab` breaks it. -/

/-- The fused invariant: memory safety, heap labels, low-equivalence and the pointer
    invariant, on both runs at once. -/
structure FusedInv (P : Partition) (V : List String) (s s' : UState) : Prop where
  sep  : SepInv V s
  sep' : SepInv V s'
  lab  : LabInv P V s
  lab' : LabInv P V s'
  low  : uLowEqA P s s'
  ptr  : PtrLow V s s'

/-- It holds at the start of any two runs on low-equivalent stores. -/
theorem FusedInv.initU {P : Partition} {σ σ' : Store} (h : lowEq P σ σ') :
    FusedInv P [] (initU σ) (initU σ') :=
  ⟨SepInv.initU, SepInv.initU, LabInv.initU, LabInv.initU,
   ⟨h, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩, ptrLow_initial σ σ'⟩

/-- Two runs of a certified command from the fused invariant either both diverge or both
    converge — the shape every case below case-splits on. -/
theorem FusedInv.run {P : Partition} {V V' : List String} {c : UCmd} {n : Nat}
    {π : MedPolicy} {s s' : UState} (hc : jcheck P V c = some V') (h : FusedInv P V s s') :
    uOptLowEqA P (uexec n c π s) (uexec n c π s') :=
  jsecTy_sound n c V V' (jcheck_sound c V V' hc) π s s' h.sep h.sep' h.lab h.lab' h.low

/-- **And it is inductive.** Four preservation theorems from four different stages —
    1i's `toSepCert`, 1w's `toLabInv`, 1x's `jsecTy_sound`, and `jcheck_ptrLow` above —
    move as one. -/
theorem FusedInv.step {P : Partition} {V V' : List String} {c : UCmd} {n : Nat}
    {π : MedPolicy} {s s' : UState} {r r' : UState × Nat × List Bool}
    (hc : jcheck P V c = some V') (h : FusedInv P V s s')
    (hr : uexec n c π s = some r) (hr' : uexec n c π s' = some r') :
    FusedInv P V' r.1 r'.1 := by
  have hty := jcheck_sound c V V' hc
  refine ⟨hty.toSepCert.safe n π s r h.sep hr, hty.toSepCert.safe n π s' r' h.sep' hr',
          hty.toLabInv n π s r h.sep h.lab hr, hty.toLabInv n π s' r' h.sep' h.lab' hr',
          ?_, jcheck_ptrLow n c V V' hc π s s' r r' h.sep h.sep' h.lab h.lab' h.low h.ptr
                hr hr'⟩
  have h' := FusedInv.run (n := n) (π := π) hc h
  rw [hr, hr'] at h'; exact h'.1

/-- Two synchronised runs either both diverge or both converge, in the form a case split
    can consume. -/
theorem uOptLowEqA_split {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEqA P a a') :
    (a = none ∧ a' = none)
      ∨ ∃ r r', a = some r ∧ a' = some r' ∧ uLowEqA P r.1 r'.1 := by
  cases a with
  | none => cases a' with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some _ => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact Or.inr ⟨r, r', rfl, rfl, h.1⟩

/-- The same split for the statement the trace induction carries. -/
theorem trace_split {a a' : Option (UState × Nat × Nat × List Int)}
    (h : a.map (fun r => r.2.2.2) = a'.map (fun r => r.2.2.2)) :
    (a = none ∧ a' = none)
      ∨ ∃ r r', a = some r ∧ a' = some r' ∧ r.2.2.2 = r'.2.2.2 := by
  cases a with
  | none => cases a' with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some _ => simp at h
  | some r => cases a' with
    | none => simp at h
    | some r' => exact Or.inr ⟨r, r', rfl, rfl, by simpa using h⟩

/-! ## The transient window -/

/-- The checker, threaded along a flattened command list. -/
def jcheckList (P : Partition) : List String → List UCmd → Option (List String)
  | V, []      => some V
  | V, c :: cs => (jcheck P V c).bind fun V₁ => jcheckList P V₁ cs

theorem jcheckList_append {P : Partition} : ∀ (cs ds : List UCmd) (V V₁ : List String),
    jcheckList P V cs = some V₁ → jcheckList P V (cs ++ ds) = jcheckList P V₁ ds
  | [],      _,  V, V₁, h => by
      simp only [jcheckList, Option.some.injEq] at h; subst h; rfl
  | c :: cs, ds, V, V₁, h => by
      simp only [jcheckList] at h
      rcases e : jcheck P V c with _ | W
      · rw [e] at h; simp at h
      · rw [e, Option.bind_some] at h
        show (jcheck P V c).bind (fun W => jcheckList P W (cs ++ ds)) = _
        rw [e, Option.bind_some, jcheckList_append cs ds W V₁ h]

/-- **A certified command flattens to a certified list.** `flatten` only opens `seq`, and
    `jcheck` threads the tracked set through `seq` in exactly the same order. -/
theorem jcheck_flatten {P : Partition} : ∀ (c : UCmd) (V V' : List String),
    jcheck P V c = some V' → jcheckList P V (flatten c) = some V'
  | .seq c₁ c₂, V, V', h => by
      simp only [jcheck] at h
      rcases e : jcheck P V c₁ with _ | V₁
      · rw [e] at h; simp at h
      · rw [e, Option.bind_some] at h
        show jcheckList P V (flatten c₁ ++ flatten c₂) = some V'
        rw [jcheckList_append _ _ V V₁ (jcheck_flatten c₁ V V₁ e)]
        exact jcheck_flatten c₂ V₁ V' h
  | .skip, _, _, h | .assign _ _, _, _, h | .check _, _, _, h | .access _, _, _, h
  | .memop _ _, _, _, h | .sop _ _ _, _, _, h | .hop _ _ _, _, _, h
  | .ite _ _ _, _, _, h | .loop _ _, _, _, h => by
      show (jcheck P _ _).bind (fun W => some W) = _
      rw [h]; rfl

/-- **The transient window is a function of the Low part of the state it starts from.**
    Every command in it is certified, so `touched_agrees` fixes what each one touches and
    the fused invariant carries to the next — the window is a certified run whose *state*
    is thrown away, which is exactly why the trace survives it. -/
theorem transRun_agrees {P : Partition} :
    ∀ (w : Nat) (cs : List UCmd) (V V' : List String), jcheckList P V cs = some V' →
      ∀ (π : MedPolicy) (s s' : UState), FusedInv P V s s' →
        transRun w cs π s = transRun w cs π s' := by
  intro w
  induction w with
  | zero => intro cs V V' _ π s s' _; rfl
  | succ w ihw =>
    intro cs V V' hc π s s' h
    cases cs with
    | nil => rfl
    | cons c cs =>
      simp only [jcheckList] at hc
      rcases e₁ : jcheck P V c with _ | V₁
      · rw [e₁] at hc; simp at hc
      rw [e₁, Option.bind_some] at hc
      show touched c s ++ _ = touched c s' ++ _
      rw [touched_agrees e₁ h.low.2.2.1 h.ptr]
      rcases uOptLowEqA_split (FusedInv.run (n := 30) (π := π) e₁ h) with
        ⟨hn, hn'⟩ | ⟨r, r', f, f', _⟩
      · rw [hn, hn']
      · rw [f, f']
        exact congrArg _ (ihw cs V₁ V' hc π r.1 r'.1 (FusedInv.step e₁ h f f'))

/-! ## The trace theorem -/

/-- The speculative machine's state is `uexec`'s, so the fused invariant transports to it
    unchanged. This is `spec_is_uexec_extended` in the form the induction needs. -/
theorem uexecS_uexec {n w : Nat} {c : UCmd} {π : MedPolicy} {s : UState}
    {r : UState × Nat × Nat × List Int} (h : uexecS n w c π s = some r) :
    ∃ k tr, uexec n c π s = some (r.1, k, tr) := by
  have hx := spec_is_uexec_extended n w c π s
  rw [h] at hx
  rcases f : uexec n c π s with _ | r₂
  · rw [f] at hx; simp at hx
  · rw [f] at hx
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hx
    have hst : r.1 = r₂.1 := hx.1
    exact ⟨r₂.2.1, r₂.2.2, by rw [hst]⟩

/-- **The trace theorem.** Two runs of a certified program from states satisfying the
    fused invariant produce the **same speculative trace, at every window** — transient
    execution included. Stage 2d stated this as a conjecture; stage 2f found it false in
    the model as it then stood and repaired the model; stage 2g found the frame it needs.
    This is the induction those three stages were clearing the way for. -/
theorem jcheck_strace {P : Partition} :
    ∀ (n w : Nat) (c : UCmd) (V V' : List String), jcheck P V c = some V' →
      ∀ (π : MedPolicy) (s s' : UState), FusedInv P V s s' →
        (uexecS n w c π s).map (fun r => r.2.2.2)
          = (uexecS n w c π s').map (fun r => r.2.2.2) := by
  intro n
  induction n with
  | zero => intro w c V V' _ π s s' _; rfl
  | succ m ih =>
    intro w c V V' hc π s s' h
    by_cases hatom : isAtomic c = true
    · have hkey : ∀ t : UState, uexecS (m + 1) w c π t
          = (uexec 1 c π t).map (fun r => (r.1, r.2.1, r.2.1, touched c t)) := by
        intro t; cases c <;> first | rfl | simp [isAtomic] at hatom
      rw [hkey s, hkey s']
      rcases uOptLowEqA_split (FusedInv.run (n := 1) (π := π) hc h) with
        ⟨hn, hn'⟩ | ⟨r, r', f, f', _⟩
      · rw [hn, hn']; rfl
      · rw [f, f']
        simp only [Option.map_some]
        exact congrArg some (touched_agrees hc h.low.2.2.1 h.ptr)
    · cases c
      case seq c₁ c₂ =>
          simp only [jcheck] at hc
          rcases e₁ : jcheck P V c₁ with _ | V₁
          · rw [e₁] at hc; simp at hc
          rw [e₁, Option.bind_some] at hc
          show (Option.map _ ((uexecS m w c₁ π s).bind _))
             = (Option.map _ ((uexecS m w c₁ π s').bind _))
          rcases trace_split (ih w c₁ V V₁ e₁ π s s' h) with
            ⟨hn, hn'⟩ | ⟨r₁, r₁', q₁, q₁', ht₁⟩
          · rw [hn, hn']
          · rw [q₁, q₁']
            simp only [Option.bind_some]
            obtain ⟨k, tr, g₁⟩ := uexecS_uexec q₁
            obtain ⟨k', tr', g₁'⟩ := uexecS_uexec q₁'
            have h₁ : FusedInv P V₁ r₁.1 r₁'.1 := FusedInv.step e₁ h g₁ g₁'
            rcases trace_split (ih w c₂ V₁ V' hc π r₁.1 r₁'.1 h₁) with
              ⟨hn, hn'⟩ | ⟨r₂, r₂', q₂, q₂', ht₂⟩
            · rw [hn, hn']; rfl
            · rw [q₂, q₂']
              simp only [Option.map_some, Option.some.injEq]
              rw [ht₁, ht₂]
      case ite e c₁ c₂ =>
          simp only [jcheck] at hc
          by_cases he : exprLow P e = true
          · rw [ite_eq_left he] at hc
            rcases e₁ : jcheck P V c₁ with _ | V₁
            · rw [e₁] at hc; simp at hc
            rcases e₂ : jcheck P V c₂ with _ | V₂
            · rw [e₁, e₂] at hc; simp at hc
            rw [e₁, e₂] at hc
            rw [uexecS_ite_eq, uexecS_ite_eq]
            have hguard : evalE e s.store = evalE e s'.store := evalE_lowEq e he h.low.1
            by_cases hg : evalE e s.store ≠ 0
            · have hg' : evalE e s'.store ≠ 0 := by rw [← hguard]; exact hg
              rw [ite_eq_left hg, ite_eq_left hg']
              have htr : transRun w (flatten c₂) π s = transRun w (flatten c₂) π s' :=
                transRun_agrees w (flatten c₂) V V₂ (jcheck_flatten c₂ V V₂ e₂) π s s' h
              rcases trace_split (ih w c₁ V V₁ e₁ π s s' h) with
                ⟨hn, hn'⟩ | ⟨r₁, r₁', q₁, q₁', ht₁⟩
              · rw [hn, hn']; rfl
              · rw [q₁, q₁']
                simp only [Option.map_some, Option.some.injEq]
                rw [htr, ht₁]
            · have hg' : ¬ (evalE e s'.store ≠ 0) := by rw [← hguard]; exact hg
              rw [ite_eq_right hg, ite_eq_right hg']
              have htr : transRun w (flatten c₁) π s = transRun w (flatten c₁) π s' :=
                transRun_agrees w (flatten c₁) V V₁ (jcheck_flatten c₁ V V₁ e₁) π s s' h
              rcases trace_split (ih w c₂ V V₂ e₂ π s s' h) with
                ⟨hn, hn'⟩ | ⟨r₂, r₂', q₂, q₂', ht₂⟩
              · rw [hn, hn']; rfl
              · rw [q₂, q₂']
                simp only [Option.map_some, Option.some.injEq]
                rw [htr, ht₂]
          · rw [ite_eq_right he] at hc; cases hc
      case loop e c₀ =>
          by_cases hcond : (exprLow P e && (jcheck P V c₀ == some V)) = true
          · have hloopc : jcheck P V (.loop e c₀) = some V := by
              simp only [jcheck, ite_eq_left hcond]
            rw [hloopc] at hc
            simp only [Option.some.injEq] at hc
            subst hc
            obtain ⟨he, hbody0⟩ := Bool.and_eq_true .. |>.mp hcond
            have hbody : jcheck P V c₀ = some V := by simpa using hbody0
            rw [uexecS_loop_eq, uexecS_loop_eq]
            have hguard : evalE e s.store = evalE e s'.store := evalE_lowEq e he h.low.1
            by_cases hg : evalE e s.store ≠ 0
            · have hg' : evalE e s'.store ≠ 0 := by rw [← hguard]; exact hg
              rw [ite_eq_left hg, ite_eq_left hg']
              rcases trace_split (ih w c₀ V V hbody π s s' h) with
                ⟨hn, hn'⟩ | ⟨r₁, r₁', q₁, q₁', ht₁⟩
              · rw [hn, hn']
              · rw [q₁, q₁']
                simp only [Option.bind_some]
                obtain ⟨k, tr, g₁⟩ := uexecS_uexec q₁
                obtain ⟨k', tr', g₁'⟩ := uexecS_uexec q₁'
                have h₁ : FusedInv P V r₁.1 r₁'.1 := FusedInv.step hbody h g₁ g₁'
                rcases trace_split (ih w (.loop e c₀) V V hloopc π r₁.1 r₁'.1 h₁) with
                  ⟨hn, hn'⟩ | ⟨r₂, r₂', q₂, q₂', ht₂⟩
                · rw [hn, hn']; rfl
                · rw [q₂, q₂']
                  simp only [Option.map_some, Option.some.injEq]
                  rw [ht₁, ht₂]
            · have hg' : ¬ (evalE e s'.store ≠ 0) := by rw [← hguard]; exact hg
              rw [ite_eq_right hg, ite_eq_right hg']; rfl
          · simp only [jcheck, ite_eq_right hcond] at hc; cases hc
      all_goals exact absurd rfl hatom

/-! ## The bridge to the five-certificate checker -/

/-- **The tracked set the five-certificate checker computes is the joint checker's.**
    `allcheck` carries the mediation set and the budget alongside, and refuses loops, but
    on the pointer component it is `jcheck` rule for rule — so everything proved above
    applies to every program `allcheck`, and hence `xcheck`, accepts. -/
theorem allcheck_jcheck {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    allcheck P A V c = some (A', V', k) → jcheck P V c = some V' := by
  intro c
  induction c
  case seq c₁ c₂ ih₁ ih₂ =>
      intro A V A' V' k h
      simp only [allcheck] at h
      rcases e₁ : allcheck P A V c₁ with _ | p₁
      · rw [e₁] at h; simp at h
      rw [e₁, Option.bind_some] at h
      rcases e₂ : allcheck P p₁.1 p₁.2.1 c₂ with _ | p₂
      · rw [e₂] at h; simp at h
      rw [e₂] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      show (jcheck P V c₁).bind (fun W => jcheck P W c₂) = some V'
      rw [ih₁ A V p₁.1 p₁.2.1 p₁.2.2 (by rw [e₁]), Option.bind_some,
          ih₂ p₁.1 p₁.2.1 p₂.1 p₂.2.1 p₂.2.2 (by rw [e₂]), h.2.1]
  case ite e c₁ c₂ ih₁ ih₂ =>
      intro A V A' V' k h
      simp only [allcheck] at h
      split at h
      · rename_i he
        rcases e₁ : allcheck P A V c₁ with _ | p₁
        · rw [e₁] at h; simp at h
        rcases e₂ : allcheck P A V c₂ with _ | p₂
        · rw [e₁, e₂] at h; simp at h
        rw [e₁, e₂] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        simp only [jcheck, ite_eq_left he, ih₁ A V p₁.1 p₁.2.1 p₁.2.2 (by rw [e₁]),
          ih₂ A V p₂.1 p₂.2.1 p₂.2.2 (by rw [e₂]), Option.some.injEq]
        exact h.2.1
      · cases h
  case loop e c₀ _ => intro A V A' V' k h; simp [allcheck] at h
  case memop op x =>
      intro A V A' V' k h
      cases op <;>
        (simp only [allcheck] at h
         first | (split at h <;> simp_all [jcheck]) | simp_all [jcheck])
  case sop op x e =>
      intro A V A' V' k h
      cases op <;>
        (simp only [allcheck] at h
         first | (split at h <;> simp_all [jcheck]) | simp_all [jcheck])
  case hop op x y =>
      intro A V A' V' k h
      cases op <;>
        (simp only [allcheck] at h
         first | (split at h <;> simp_all [jcheck]) | simp_all [jcheck])
  all_goals
    intro A V A' V' k h
    simp only [allcheck] at h
    first
      | (split at h <;> simp_all [jcheck])
      | simp_all [jcheck]

/-! ## What it closes

    Stage 2d, in the module that stated the conjecture: *for every program `xcheck`
    accepts, the speculative trace is a function of the Low part of the initial state,
    under every window*. -/

/-- **The conjecture, proved.** Row 9 is now closed on `UCmd` — the language that carries
    the five certificates — rather than on brick 33's separate language with none. -/
theorem certified_trace_is_low {P : Partition} {c : UCmd} {C' : TaintEnv}
    {A' V' : List String} {k : Nat} {Ks : List Nat}
    (h : xcheck P [] [] [] c = some (C', A', V', k, Ks))
    (n w : Nat) (π : MedPolicy) (σ σ' : Store) (hσ : lowEq P σ σ') :
    straceU n w c π (initU σ) = straceU n w c π (initU σ') := by
  simp only [xcheck] at h
  rcases ea : allcheck P [] [] c with _ | p
  · rw [ea] at h; simp at h
  · rcases et : tcheck [] c with _ | q
    · rw [ea, et] at h; simp at h
    · exact jcheck_strace n w c [] p.2.1
        (allcheck_jcheck c [] [] p.1 p.2.1 p.2.2 (by rw [ea])) π (initU σ) (initU σ')
        (FusedInv.initU hσ)

/-! ## On a program worth the name -/

theorem bigHandler_allcheck :
    allcheck Psec [] [] bigHandler = some (["fs", "db"], [], 24) := by decide

/-- **Stage 2h's twenty-one-operation handler leaks nothing through its trace**, at every
    window and every fuel. It branches, it allocates a secret cell, it dereferences three
    pointers and frees them — and which addresses it touches is a function of the public
    part of its input. -/
theorem bigHandler_trace_is_low (n w : Nat) (π : MedPolicy) (σ σ' : Store)
    (h : lowEq Psec σ σ') :
    straceU n w bigHandler π (initU σ) = straceU n w bigHandler π (initU σ') :=
  jcheck_strace n w bigHandler [] []
    (allcheck_jcheck bigHandler [] [] ["fs", "db"] [] 24 bigHandler_allcheck)
    π (initU σ) (initU σ') (FusedInv.initU h)

/-- The guarantee is not vacuous on it: six memory operations are traced. -/
theorem bigHandler_trace_is_not_empty :
    straceU 60 0 bigHandler (fun _ => true) (initU σlo) = some [0, 0, 1, 1, 0, 1] := by
  decide

/-! ## The transient window really adds to the trace -/

/-- A certified branching program that dereferences a **public** pointer in one branch and
    a **secret-named** one in the other. Both branches touch memory, so misprediction
    genuinely lengthens the trace — which `bigHandler` does not do, and which is why stage
    2h's measurement could not supply this witness. -/
def brWitness : UCmd :=
  .seq (.memop .alloc "p")
    (.seq (.memop .allocS "secret")
      (.ite (.var "l") (.memop .deref "p") (.memop .deref "secret")))

theorem brWitness_checks :
    xcheck Psec [] [] [] brWitness = some ([], [], ["secret", "p"], 4, []) := by decide

/-- **The window is doing work.** At window 0 the trace is the one address the taken
    branch dereferences; at window 1 the mispredicted branch adds the other. Nothing here
    is speculation-inert, so the theorem below is not covering an empty window. -/
theorem brWitness_window_grows :
    straceU 20 0 brWitness (fun _ => true) (initU σlo) = some [1]
  ∧ straceU 20 1 brWitness (fun _ => true) (initU σlo) = some [0, 1] := by decide

/-- **And it agrees anyway.** Two initial stores differing only in `secret` — the variable
    `allocS` then overwrites with an allocator-chosen address — give the same trace at
    every window and every fuel. The transient window is covered by the theorem, not
    excluded from it. -/
theorem brWitness_trace_is_low (n w : Nat) (π : MedPolicy) (σ σ' : Store)
    (h : lowEq Psec σ σ') :
    straceU n w brWitness π (initU σ) = straceU n w brWitness π (initU σ') :=
  certified_trace_is_low brWitness_checks n w π σ σ' h

/-- The instance at the window where the transient access happens, and the same equality
    by kernel computation — the theorem and the machine agree about a concrete run. -/
theorem brWitness_agrees_measured :
    straceU 20 1 brWitness (fun _ => true) (initU σlo)
      = straceU 20 1 brWitness (fun _ => true) (initU σhi)
  ∧ straceU 20 1 brWitness (fun _ => true) (initU σhi) = some [0, 1] :=
  ⟨brWitness_trace_is_low 20 1 (fun _ => true) σlo σhi σlo_lowEq_σhi, by decide⟩

/-! ## The certificate is what does it

    `victimU` is the same shape and leaks its secret through the trace under misprediction
    (stage 2d's `victimU_leaks`). The theorem does not apply to it, and the reason is not
    a technicality: `xcheck` refuses it, because stage 1i's linearity rule drops a loaded
    value from the tracked set and so forbids the value-to-address flow the gadget needs.
    The hypothesis is the whole content. -/
theorem the_hypothesis_is_load_bearing :
    xcheck Psec [] ["p"] ["p"] victimU = none
  ∧ ¬ (straceU 12 2 victimU (fun _ => true) (specState 42)
        = straceU 12 2 victimU (fun _ => true) (specState 99)) :=
  ⟨gadget_rejected_by_memory_safety.2.2.2, victimU_leaks.2.2⟩

/-! ## What this stage claims, and what it does not

    **Claims.** For every program `xcheck` accepts, the speculative address trace is a
    function of the Low part of the initial store, at every misprediction window and every
    fuel. That is stage 2d's conjecture, and closing it takes the fused induction stage 2g
    said it would: `jcheck_ptrLow` carries `SepInv`, `LabInv`, `uLowEqA` and `PtrLow`
    together, because stage 2g's `traceEq_is_not_inductive` proved that dropping the first
    two breaks the argument at its first step.

    **Does not claim.** The trace is addresses only — no cache lines, no eviction, no
    timing, no contention — so this closes the channel the model has, not the channel a
    processor has. One global window, correctly-predicted loop guards, and no nested
    speculation (excluded by `flatten`'s treatment of a nested `ite` as one step) are all
    stage 2d's scoping, unchanged. And `allcheck` still has no loop rule, so "every
    program `xcheck` accepts" is every *loop-free* program; `jcheck_strace` itself does
    handle `loop`, and `jcheck_ptrLow` proves the pointer invariant inductive through it,
    so the restriction is the budget's, not the trace's.

    **The cost stays broken.** `transient_work_is_off_the_budget` is untouched by any of
    this: the trace is now proved secret-independent, and the *count* of transient
    commands is still off the certificate. Stage 2e bounded it; nothing here improves that
    bound. -/


end ConfTyping
