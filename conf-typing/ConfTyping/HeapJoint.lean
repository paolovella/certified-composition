/-
  The composable core, stage 1k: the joint judgment stage 1j's counterexample forced.

  Stage 1j proved that noninterference and memory safety do not factor on the heap: a
  `deref` leaks through the fault flag unless the pointer is known live, so the two
  properties cannot be certified separately and conjoined at the end. It also said
  exactly what to build instead — a judgment *indexed by the tracked set*, so the NI
  rule for `deref x` can demand `x ∈ V`. This is that judgment.

  `JSecTy P V c V'` is a four-place relation: from tracked set `V`, command `c` is both
  noninterferent at `P` and memory-safe, ending with tracked set `V'`. It has the union
  of the two rule sets, with the heap rules carrying the membership side-condition that
  neither system could state alone. `jcheck` decides it, and `jcheck_gives_both`
  extracts the two guarantees from one run of one checker.

  Two things are worth more than the construction.

  **`indexed_beats_the_conjunction`.** On `safeHeapProg` — allocate, dereference,
  mediate an access, free — the old checkers give nothing: `ucheckNI` rejects it
  outright, so the NI certificate is unavailable, while `slcheck` accepts it but says
  nothing about leaks. `jcheck` certifies both. So the indexed judgment is not a
  repackaging: it proves things the conjunction of its parts cannot, which is precisely
  the prediction stage 1j made from a counterexample.

  **`SepCert.loop`.** Getting here needed a loop rule for the memory certificate, which
  stages 1h and 1i both ducked (`umcheck` and `slcheck` return `none` at a loop). It is
  a fuel induction and the tracked set is simply the loop invariant. Adding it here
  rather than back-patching `MemLinear` keeps stage 1i's claims exactly as they were
  audited.

  Honest scope. The judgment covers everything `UCmd` has, but two of its rules stay
  conservative and both were argued for earlier: `allocL` is still absent (stage 1j's
  open question — it needs `fresh` in the observation), and a loop must preserve the
  tracked set exactly, so a loop that allocates without freeing is rejected. Neither is
  a soundness gap; both are places the analysis says "no" to a safe program.
-/
import ConfTyping.HeapNI

namespace ConfTyping

/-! ## The loop rule the memory certificate was missing -/

/-- **Loops preserve the memory invariant** when the body does, with the tracked set as
    the loop invariant. Stages 1h and 1i both stopped at `none` for loops; the joint
    judgment needs this, and it is a plain fuel induction. -/
theorem SepCert.loop {V : List String} {e : Expr} {c : UCmd} (h : SepCert V c V) :
    SepCert V (.loop e c) V := by
  constructor
  intro n
  induction n with
  | zero => intro π s r _ hr; simp [uexec] at hr
  | succ m ihm =>
      intro π s r hinv hr
      rw [uexec_loop_eq] at hr
      by_cases hg : evalE e s.store ≠ 0
      · rw [if_pos hg] at hr
        rcases e₁ : uexec m c π s with _ | r₁
        · rw [e₁] at hr; simp at hr
        · rw [e₁, Option.bind_some] at hr
          rcases e₂ : uexec m (.loop e c) π r₁.1 with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr
            simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            exact ihm π r₁.1 r₂ (h.safe m π s r₁ hinv e₁) e₂
      · rw [if_neg hg] at hr
        simp only [Option.some.injEq] at hr
        subst hr
        exact hinv

/-- Shrinking the tracked set weakens the postcondition, so it is always allowed. -/
theorem SepCert.weakenPost {V V₁ V' : List String} {c : UCmd} (h : SepCert V c V₁)
    (hsub : ∀ x ∈ V', x ∈ V₁) : SepCert V c V' :=
  ⟨fun n π s r hinv hr => SepInv.mono hsub (h.safe n π s r hinv hr)⟩

/-- And a *smaller* precondition is a weaker assumption on the input state, so it may
    be strengthened to any superset. -/
theorem SepCert.strengthenPre {V W V' : List String} {c : UCmd} (h : SepCert W c V')
    (hsub : ∀ x ∈ W, x ∈ V) : SepCert V c V' :=
  ⟨fun n π s r hinv hr => h.safe n π s r (SepInv.mono hsub hinv) hr⟩

/-! ## The indexed judgment -/

/-- **Noninterference and memory safety, in one judgment indexed by the tracked set.**
    The heap rules carry a membership side-condition that neither of the two separate
    systems could express: `USecTy` has no `V`, and `SepCert` has no `P`. -/
inductive JSecTy (P : Partition) : List String → UCmd → List String → Prop where
  | skip    : ∀ V, JSecTy P V .skip V
  | assignH : ∀ V x e, P x = true → JSecTy P V (.assign x e) (dropStr x V)
  | assignL : ∀ V x e, exprLow P e = true → JSecTy P V (.assign x e) (dropStr x V)
  | seq     : ∀ {V V₁ V₂ c₁ c₂}, JSecTy P V c₁ V₁ → JSecTy P V₁ c₂ V₂ →
              JSecTy P V (.seq c₁ c₂) V₂
  | iteL    : ∀ {V V₁ V₂ c₁ c₂} (e), exprLow P e = true →
              JSecTy P V c₁ V₁ → JSecTy P V c₂ V₂ →
              JSecTy P V (.ite e c₁ c₂) (interStr V₁ V₂)
  /-- **The widened loop rule** (stage 1l). The loop is analysed at an invariant `W`
      contained in the entry set, and the body need only *preserve* it — end with some
      `W₁ ⊇ W` rather than with `W` on the nose. Stage 1k's exact rule is the case
      `W = V`, `W₁ = V`. -/
  | whileW  : ∀ {V W W₁ c} (e), exprLow P e = true → (∀ x ∈ W, x ∈ V) →
              JSecTy P W c W₁ → (∀ x ∈ W, x ∈ W₁) →
              JSecTy P V (.loop e c) W
  | check   : ∀ V r, JSecTy P V (.check r) V
  | access  : ∀ V r, JSecTy P V (.access r) V
  /-- Allocation into a High variable: stage 1j showed the address is invisible. -/
  | allocH  : ∀ V x, P x = true → JSecTy P V (.memop .alloc x) (x :: V)
  /-- **The rule that needed the index.** `deref` is noninterferent exactly when the
      pointer is known live, so the fault branch is unreachable. -/
  | deref   : ∀ V x, memStr x V = true → JSecTy P V (.memop .deref x) V
  | free    : ∀ V x, memStr x V = true → JSecTy P V (.memop .free x) (dropStr x V)

/-- Every joint derivation contains a memory-safety derivation. -/
theorem JSecTy.toSepCert {P : Partition} {V : List String} {c : UCmd} {V' : List String}
    (h : JSecTy P V c V') : SepCert V c V' := by
  induction h with
  | skip _ => exact SepCert.skip
  | assignH _ x e _ => exact SepCert.assign x e
  | assignL _ x e _ => exact SepCert.assign x e
  | seq _ _ ih₁ ih₂ => exact SepCert.seq ih₁ ih₂
  | iteL _ _ _ _ ih₁ ih₂ => exact SepCert.ite ih₁ ih₂
  | whileW _ _ hWV _ hWW₁ ih =>
      exact SepCert.strengthenPre (SepCert.loop (SepCert.weakenPost ih hWW₁)) hWV
  | check _ r => exact SepCert.check r
  | access _ r => exact SepCert.access r
  | allocH _ x _ => exact SepCert.alloc x
  | deref _ x hx => exact SepCert.deref x hx
  | free _ x hx => exact SepCert.free x hx

/-! ## Two combinators that keep the equations

    The stage-1d versions discard the fact that the sub-run produced a particular
    outcome, which is fine when the only thing threaded is Low-equality. Here the
    invariant has to be re-established at the intermediate state, and that needs the
    equation. -/

theorem uOptLowEq_bindE {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEq P a a')
    {f f' : UState × Nat × List Bool → Option (UState × Nat × List Bool)}
    (hf : ∀ r r', a = some r → a' = some r' → uLowEq P r.1 r'.1 → r.2.1 = r'.2.1 →
          r.2.2 = r'.2.2 → uOptLowEq P (f r) (f' r')) :
    uOptLowEq P (a.bind f) (a'.bind f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' rfl rfl h.1 h.2.1 h.2.2

theorem uOptLowEq_mapE {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEq P a a')
    {f f' : UState × Nat × List Bool → UState × Nat × List Bool}
    (hf : ∀ r r', a = some r → a' = some r' → uLowEq P r.1 r'.1 → r.2.1 = r'.2.1 →
          r.2.2 = r'.2.2 → uLowEq P (f r).1 (f' r').1 ∧ (f r).2.1 = (f' r').2.1 ∧
          (f r).2.2 = (f' r').2.2) :
    uOptLowEq P (a.map f) (a'.map f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' rfl rfl h.1 h.2.1 h.2.2

/-! ## Soundness: one induction, both guarantees -/

/-- **The joint soundness theorem.** Two runs from memory-safe, Low-equal states are
    Low-equal throughout — including the heap operations, which no earlier theorem
    covered. The memory invariant is a *hypothesis of the noninterference proof*, which
    is the formal content of stage 1j's "these do not factor". -/
theorem jsecTy_sound {P : Partition} :
    ∀ (n : Nat) (c : UCmd) (V V' : List String), JSecTy P V c V' →
      ∀ (π : MedPolicy) (s s' : UState), SepInv V s → SepInv V s' → uLowEq P s s' →
        uOptLowEq P (uexec n c π s) (uexec n c π s') := by
  intro n
  induction n with
  | zero => intro c V V' _ π s s' _ _ _; exact True.intro
  | succ m ih =>
    intro c V V' hc π s s' hI hI' hle
    obtain ⟨hst, hrd, hdd⟩ := hle
    cases hc with
    | skip _ => exact ⟨⟨hst, hrd, hdd⟩, rfl, rfl⟩
    | check _ r =>
        show uOptLowEq P (uexec (m+1) (.check r) π s) (uexec (m+1) (.check r) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          by_cases hp : π r = true
          · rw [if_pos hp, if_pos hp]; exact ⟨hst, hrd, hdd⟩
          · rw [if_neg hp, if_neg hp]; exact ⟨hst, hrd, rfl⟩
    | access _ r =>
        show uOptLowEq P (uexec (m+1) (.access r) π s) (uexec (m+1) (.access r) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          exact ⟨hst, by simp [hrd], hdd⟩
    | assignH _ x e hx =>
        show uOptLowEq P (uexec (m+1) (.assign x e) π s) (uexec (m+1) (.assign x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd⟩
          intro y hy
          have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
          show upd s.store x (evalE e s.store) y = upd s'.store x (evalE e s'.store) y
          simp only [upd, if_neg hyx]; exact hst y hy
    | assignL _ x e he =>
        show uOptLowEq P (uexec (m+1) (.assign x e) π s) (uexec (m+1) (.assign x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd⟩
          intro y hy
          show upd s.store x (evalE e s.store) y = upd s'.store x (evalE e s'.store) y
          simp only [upd]
          by_cases hxy : y = x
          · rw [if_pos hxy, if_pos hxy, evalE_lowEq e he hst]
          · rw [if_neg hxy, if_neg hxy]; exact hst y hy
    | allocH _ x hx =>
        show uOptLowEq P (uexec (m+1) (.memop .alloc x) π s)
                        (uexec (m+1) (.memop .alloc x) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd⟩
          intro z hz
          have hzx : z ≠ x := fun h => by rw [h, hx] at hz; cases hz
          show upd s.store x s.fresh z = upd s'.store x s'.fresh z
          simp only [upd, if_neg hzx]; exact hst z hz
    | deref _ x hx =>
        exact deref_NI_given_safety hx m π s s' hI.toMemInv hI'.toMemInv ⟨hst, hrd, hdd⟩
    | free _ x hx =>
        exact free_NI_given_safety hx m π s s' hI.toMemInv hI'.toMemInv ⟨hst, hrd, hdd⟩
    | @seq _ V₁ _ c₁ c₂ h₁ h₂ =>
        show uOptLowEq P (uexec (m+1) (.seq c₁ c₂) π s) (uexec (m+1) (.seq c₁ c₂) π s')
        rw [uexec_seq_eq, uexec_seq_eq]
        refine uOptLowEq_bindE (ih c₁ _ V₁ h₁ π s s' hI hI' ⟨hst, hrd, hdd⟩) ?_
        intro r₁ r₁' e₁ e₁' hs₁ hc1 ht1
        have hJ : SepInv V₁ r₁.1 := h₁.toSepCert.safe m π s r₁ hI e₁
        have hJ' : SepInv V₁ r₁'.1 := h₁.toSepCert.safe m π s' r₁' hI' e₁'
        refine uOptLowEq_mapE (ih c₂ V₁ _ h₂ π r₁.1 r₁'.1 hJ hJ' hs₁) ?_
        intro r₂ r₂' _ _ hs₂ hc2 ht2
        exact ⟨hs₂, by simp [hc1, hc2], by simp [ht1, ht2]⟩
    | @iteL _ _ _ c₁ c₂ e hg h₁ h₂ =>
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        show uOptLowEq P (uexec (m+1) (.ite e c₁ c₂) π s) (uexec (m+1) (.ite e c₁ c₂) π s')
        rw [uexec_ite_eq, uexec_ite_eq]
        by_cases hb : evalE e s.store ≠ 0
        · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_pos hb, if_pos hb']
          refine uOptLowEq_mapE (ih c₁ _ _ h₁ π s s' hI hI' ⟨hst, hrd, hdd⟩) ?_
          intro r r' _ _ hs hcs htr; exact ⟨hs, by simp [hcs], by simp [htr]⟩
        · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_neg hb, if_neg hb']
          refine uOptLowEq_mapE (ih c₂ _ _ h₂ π s s' hI hI' ⟨hst, hrd, hdd⟩) ?_
          intro r r' _ _ hs hcs htr; exact ⟨hs, by simp [hcs], by simp [htr]⟩
    | @whileW _ _ W₁ c₀ e hg hWV h₀ hWW₁ =>
        have hIV' : SepInv V' s := SepInv.mono hWV hI
        have hIV'' : SepInv V' s' := SepInv.mono hWV hI'
        have hbody : SepCert V' c₀ V' := SepCert.weakenPost h₀.toSepCert hWW₁
        have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
        show uOptLowEq P (uexec (m+1) (.loop e c₀) π s) (uexec (m+1) (.loop e c₀) π s')
        rw [uexec_loop_eq, uexec_loop_eq]
        by_cases hb : evalE e s.store ≠ 0
        · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_pos hb, if_pos hb']
          refine uOptLowEq_bindE (ih c₀ V' W₁ h₀ π s s' hIV' hIV'' ⟨hst, hrd, hdd⟩) ?_
          intro r₁ r₁' e₁ e₁' hs₁ hc1 ht1
          have hJ : SepInv V' r₁.1 := hbody.safe m π s r₁ hIV' e₁
          have hJ' : SepInv V' r₁'.1 := hbody.safe m π s' r₁' hIV'' e₁'
          refine uOptLowEq_mapE
            (ih (.loop e c₀) V' V' (.whileW e hg (fun _ hx => hx) h₀ hWW₁)
              π r₁.1 r₁'.1 hJ hJ' hs₁) ?_
          intro r₂ r₂' _ _ hs₂ hc2 ht2
          exact ⟨hs₂, by simp [hc1, hc2], by simp [ht1, ht2]⟩
        · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
          rw [if_neg hb, if_neg hb']
          exact ⟨⟨hst, hrd, hdd⟩, rfl, rfl⟩

/-! ## The checker -/

/-- One decidable analysis producing both certificates. -/
def jcheck (P : Partition) : List String → UCmd → Option (List String)
  | V, .skip           => some V
  | V, .assign x e     => if P x || exprLow P e then some (dropStr x V) else none
  | V, .check _        => some V
  | V, .access _       => some V
  | V, .memop .alloc x => if P x then some (x :: V) else none
  | V, .memop .deref x => if memStr x V then some V else none
  | V, .memop .free x  => if memStr x V then some (dropStr x V) else none
  | V, .seq c₁ c₂      => (jcheck P V c₁).bind fun V₁ => jcheck P V₁ c₂
  | V, .ite e c₁ c₂    => if exprLow P e then
                            match jcheck P V c₁, jcheck P V c₂ with
                            | some V₁, some V₂ => some (interStr V₁ V₂)
                            | _, _ => none
                          else none
  | V, .loop e c       => if exprLow P e && (jcheck P V c == some V) then some V else none

theorem jcheck_sound {P : Partition} : ∀ (c : UCmd) (V V' : List String),
    jcheck P V c = some V' → JSecTy P V c V'
  | .skip, V, V', h => by
      simp only [jcheck, Option.some.injEq] at h; subst h; exact .skip V
  | .check r, V, V', h => by
      simp only [jcheck, Option.some.injEq] at h; subst h; exact .check V r
  | .access r, V, V', h => by
      simp only [jcheck, Option.some.injEq] at h; subst h; exact .access V r
  | .assign x e, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : (P x || exprLow P e) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        rcases Bool.or_eq_true _ _ |>.mp hx with h' | h'
        · exact .assignH V x e h'
        · exact .assignL V x e h'
      · rw [if_neg hx] at h; simp at h
  | .memop .alloc x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : P x = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h; exact .allocH V x hx
      · rw [if_neg hx] at h; simp at h
  | .memop .deref x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h; exact .deref V x hx
      · rw [if_neg hx] at h; simp at h
  | .memop .free x, V, V', h => by
      simp only [jcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h; exact .free V x hx
      · rw [if_neg hx] at h; simp at h
  | .seq c₁ c₂, V, V', h => by
      simp only [jcheck] at h
      rcases e₁ : jcheck P V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        exact .seq (jcheck_sound c₁ V V₁ e₁) (jcheck_sound c₂ V₁ V' h)
  | .ite e c₁ c₂, V, V', h => by
      simp only [jcheck] at h
      by_cases hg : exprLow P e = true
      · rw [if_pos hg] at h
        rcases e₁ : jcheck P V c₁ with _ | V₁
        · rw [e₁] at h; simp at h
        · rcases e₂ : jcheck P V c₂ with _ | V₂
          · rw [e₁, e₂] at h; simp at h
          · rw [e₁, e₂] at h
            simp only [Option.some.injEq] at h; subst h
            exact .iteL e hg (jcheck_sound c₁ V V₁ e₁) (jcheck_sound c₂ V V₂ e₂)
      · rw [if_neg hg] at h; simp at h
  | .loop e c₀, V, V', h => by
      simp only [jcheck] at h
      by_cases hg : (exprLow P e && (jcheck P V c₀ == some V)) = true
      · rw [if_pos hg] at h
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hg1, hg2⟩ := Bool.and_eq_true _ _ |>.mp hg
        exact .whileW e hg1 (fun _ hx => hx)
          (jcheck_sound c₀ V V (by simpa using hg2)) (fun _ hx => hx)
      · rw [if_neg hg] at h; simp at h

/-- **Both guarantees, from one run of one checker.** Noninterference *including* the
    heap operations, and no memory fault — for a program the two separate checkers
    could not certify together. -/
theorem jcheck_gives_both {P : Partition} {c : UCmd} {V' : List String}
    (h : jcheck P [] c = some V') :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false) := by
  have hty := jcheck_sound c [] V' h
  refine ⟨fun n π σ σ' hσ => ?_, fun n π σ r hr => ?_⟩
  · exact jsecTy_sound n c [] V' hty π (initU σ) (initU σ')
      SepInv.initU SepInv.initU ⟨hσ, rfl, rfl⟩
  · exact (hty.toSepCert.safe n π (initU σ) r SepInv.initU hr).1

/-! ## What the index buys -/

/-- Allocate a pointer in a secret, use it, mediate an access, release it. Every
    ingredient the two separate checkers choke on. -/
def safeHeapProg : UCmd :=
  .seq (.memop .alloc "secret")
   (.seq (.memop .deref "secret")
    (.seq (.check "db")
     (.seq (.access "db") (.memop .free "secret"))))

/-- **The indexed judgment proves what the conjunction of its parts cannot.** The
    stage-1d checker rejects this program outright — it dereferences — so no NI
    certificate is available from it at any partition; the stage-1i checker accepts it
    but is silent about leaks. `jcheck` certifies both properties at once. This is the
    concrete payoff of stage 1j's counterexample. -/
theorem indexed_beats_the_conjunction :
    ucheckNI Psec safeHeapProg = false
  ∧ slcheck [] safeHeapProg = some []
  ∧ jcheck Psec [] safeHeapProg = some [] := by decide

/-- Spelled out on that program: noninterference through a dereference, and no fault. -/
theorem safeHeapProg_both :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n safeHeapProg π (initU σ))
                       (uexec n safeHeapProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n safeHeapProg π (initU σ) = some r → r.1.err = false) :=
  jcheck_gives_both indexed_beats_the_conjunction.2.2

/-- And it runs: the access is mediated, nothing faults, the pointer is released. -/
theorem safeHeapProg_runs :
    ((uexec 9 safeHeapProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.dead, r.1.reads, r.1.live))) = some (false, false, ["db"], []) := by
  decide

/-! ## What is still conservative, and why

    Two rules say "no" to programs that are in fact safe, and both refusals were
    argued for before they were implemented rather than after.

    `allocL` is absent: allocation into a *Low* variable needs `fresh` in the
    observation, which is stage 1j's open question about whether addresses are public.
    `allocL_would_be_unsound` is the witness that it cannot simply be added.

    A loop must preserve the tracked set **exactly** (`jcheck` requires
    `jcheck P V c == some V`), so a loop body that allocates without freeing is
    rejected even when the allocation is harmless. The fix is a widening step — start
    from `V` and iterate the body's effect to a fixed point, exactly as brick 30's
    `loopFix` does for the interval domain — and it is a real piece of work rather than
    a missing line, so it is named here instead of hidden. -/

/-- The conservatism is real and worth being able to point at: a loop that allocates is
    rejected, though nothing about it is unsafe. -/
theorem allocating_loop_rejected :
    jcheck Psec [] (.loop (.num 1) (.memop .alloc "secret")) = none := by decide

end ConfTyping
