/-
  The composable core, stage 1d: noninterference on the unified machine — the third
  certificate.

  Stage 1c bundled a cost budget with an authorization triple and stopped there,
  because lifting noninterference needed a *design decision* rather than a
  transcription: which parts of a `UState` can a Low adversary see?

  The answer taken here, and it is the load-bearing choice of this module:

  * `store` — Low part observable, as in every earlier brick;
  * `reads` — **observable**. Which resources a request touches is visible in
    practice; that is the same premise brick 33 used for cache lines and brick 29 for
    log records, so denying it here would be inconsistent with the rest of the map;
  * `dead` — **observable**. A refused request is visible to whoever made it (the
    403 is the observation);
  * `auth` — **not** observable. It is internal bookkeeping with no outward effect;
    what is outwardly visible is what was *read*, which `reads` already carries.

  With that fixed, the result is pleasant and slightly surprising: **`check` and
  `access` add no flow channel at all**. Their resource names are *syntactic
  constants*, so the reads a run performs and whether it dies are determined by the
  control flow and the policy — and both are already Low-determined for a well-typed
  program. The two new constructors are therefore unconditionally well-typed
  (`USecTy.check`, `USecTy.access`), and the whole of `WSecTy`'s discipline carries
  over unchanged.

  That is a claim with a sharp edge, and the edge is the honest limit: it holds
  *because* the language has no `access (e)` — no store-dependent resource
  selection. A dynamic resource name would make `reads` a genuine flow channel and
  the two constructors would need typing rules. `access_is_static_by_design` records
  this as the price of the result rather than a hidden assumption; dynamic selection
  is IDOR-shaped and was already a named follow-on in brick 35.

  With `usecTy_sound` the bundle reaches three certificates, composing by three
  different laws: budgets add, authorization sets thread, and noninterference is
  conjunctive.
-/
import ConfTyping.Bundle

namespace ConfTyping

/-! ## What a Low adversary sees -/

/-- Low-equivalence of unified states: the Low store, the resources touched, and
    whether the run was refused. `auth` is deliberately absent — see the header. -/
def uLowEq (P : Partition) (s s' : UState) : Prop :=
  lowEq P s.store s'.store ∧ s.reads = s'.reads ∧ s.dead = s'.dead

/-- Low-equivalence of fuelled unified outcomes: halting together, and agreeing on
    the Low state, the cost, and the branch trace. -/
def uOptLowEq (P : Partition) :
    Option (UState × Nat × List Bool) → Option (UState × Nat × List Bool) → Prop
  | none,   none    => True
  | some r, some r' => uLowEq P r.1 r'.1 ∧ r.2.1 = r'.2.1 ∧ r.2.2 = r'.2.2
  | _,      _       => False

theorem uOptLowEq_bind {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEq P a a')
    {f f' : UState × Nat × List Bool → Option (UState × Nat × List Bool)}
    (hf : ∀ r r', uLowEq P r.1 r'.1 → r.2.1 = r'.2.1 → r.2.2 = r'.2.2 →
          uOptLowEq P (f r) (f' r')) :
    uOptLowEq P (a.bind f) (a'.bind f') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hf r r' h.1 h.2.1 h.2.2

theorem uOptLowEq_map {P : Partition} {a a' : Option (UState × Nat × List Bool)}
    (h : uOptLowEq P a a')
    {g g' : UState × Nat × List Bool → UState × Nat × List Bool}
    (hg : ∀ r r', uLowEq P r.1 r'.1 → r.2.1 = r'.2.1 → r.2.2 = r'.2.2 →
          uLowEq P (g r).1 (g' r').1 ∧ (g r).2.1 = (g' r').2.1
            ∧ (g r).2.2 = (g' r').2.2) :
    uOptLowEq P (a.map g) (a'.map g') := by
  cases a with
  | none => cases a' with
    | none => exact True.intro
    | some r' => exact h.elim
  | some r => cases a' with
    | none => exact h.elim
    | some r' => exact hg r r' h.1 h.2.1 h.2.2

/-! ## Typing -/

/-- Termination-sensitive flow typing on the unified language. `WSecTy`'s rules
    verbatim, plus `check` and `access` — which need no side condition because their
    resource names are syntactic constants. -/
inductive USecTy (P : Partition) : UCmd → Prop where
  | skip    : USecTy P .skip
  | assignH : ∀ x e, P x = true → USecTy P (.assign x e)
  | assignL : ∀ x e, exprLow P e = true → USecTy P (.assign x e)
  | seq     : USecTy P c₁ → USecTy P c₂ → USecTy P (.seq c₁ c₂)
  | iteL    : ∀ e, exprLow P e = true → USecTy P c₁ → USecTy P c₂ →
              USecTy P (.ite e c₁ c₂)
  | whileL  : ∀ e, exprLow P e = true → USecTy P c → USecTy P (.loop e c)
  | check   : ∀ r, USecTy P (.check r)
  | access  : ∀ r, USecTy P (.access r)
  /-- **Allocation into a High variable** (stage 1j). The address written is the
      allocation counter, which is *not* in the observation, so the only channel is
      the store — and writing a High variable is invisible. `deref` and `free` get no
      rule here at any level: they can fault, and the fault flag *is* observable. See
      `HeapNI.lean`. -/
  | allocH  : ∀ x, P x = true → USecTy P (.memop .alloc x)

/-- **Soundness — termination-sensitive noninterference on the unified machine.**
    At every fuel and under every policy, two Low-equal runs of a well-typed command
    halt together and agree on the Low store, the cost, the branch trace, the
    resources read, and whether they were refused. -/
theorem usecTy_sound {P : Partition} :
    ∀ (n : Nat) (c : UCmd), USecTy P c → ∀ (π : MedPolicy) (s s' : UState),
      uLowEq P s s' → uOptLowEq P (uexec n c π s) (uexec n c π s') := by
  intro n
  induction n with
  | zero => intro c _ π s s' _; exact True.intro
  | succ m ih =>
    intro c hc π s s' hle
    obtain ⟨hst, hrd, hdd⟩ := hle
    cases c with
    | sop _ _ _ => cases hc   -- `USecTy` has no rule for strings; see TaintCert
    | hop _ _ _ => cases hc   -- nor for heap values; see HeapValue
    | memop op x =>
        cases hc with
        | allocH _ hy =>
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
              have hzy : z ≠ x := fun h => by rw [h, hy] at hz; cases hz
              show upd s.store x (pickAddr s.freed s.fresh) z
                 = upd s'.store x (pickAddr s'.freed s'.fresh) z
              simp only [upd, if_neg hzy]; exact hst z hz
    | skip => exact ⟨⟨hst, hrd, hdd⟩, rfl, rfl⟩
    | check r =>
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
    | access r =>
        show uOptLowEq P (uexec (m+1) (.access r) π s) (uexec (m+1) (.access r) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          exact ⟨hst, by simp [hrd], hdd⟩
    | assign x e =>
        show uOptLowEq P (uexec (m+1) (.assign x e) π s) (uexec (m+1) (.assign x e) π s')
        simp only [uexec]
        refine ⟨?_, rfl, rfl⟩
        by_cases hd : s.dead = true
        · have hd' : s'.dead = true := by rwa [hdd] at hd
          rw [if_pos hd, if_pos hd']; exact ⟨hst, hrd, hdd⟩
        · have hd' : ¬ s'.dead = true := by rwa [hdd] at hd
          rw [if_neg hd, if_neg hd']
          refine ⟨?_, hrd, hdd⟩
          cases hc with
          | assignH _ _ hx =>
              intro y hy
              have hyx : y ≠ x := fun h => by rw [h, hx] at hy; cases hy
              show upd s.store x (evalE e s.store) y = upd s'.store x (evalE e s'.store) y
              simp only [upd, if_neg hyx]; exact hst y hy
          | assignL _ _ he =>
              intro y hy
              show upd s.store x (evalE e s.store) y = upd s'.store x (evalE e s'.store) y
              simp only [upd]
              by_cases hxy : y = x
              · rw [if_pos hxy, if_pos hxy, evalE_lowEq e he hst]
              · rw [if_neg hxy, if_neg hxy]; exact hst y hy
    | seq c₁ c₂ =>
        cases hc with
        | seq hc₁ hc₂ =>
            show uOptLowEq P (uexec (m+1) (.seq c₁ c₂) π s) (uexec (m+1) (.seq c₁ c₂) π s')
            simp only [uexec]
            refine uOptLowEq_bind (ih c₁ hc₁ π s s' ⟨hst, hrd, hdd⟩) ?_
            intro r₁ r₁' hs₁ hc1 ht1
            refine uOptLowEq_map (ih c₂ hc₂ π r₁.1 r₁'.1 hs₁) ?_
            intro r₂ r₂' hs₂ hc2 ht2
            exact ⟨hs₂, by rw [hc1, hc2], by rw [ht1, ht2]⟩
    | ite e c₁ c₂ =>
        cases hc with
        | iteL _ hg h₁ h₂ =>
            have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
            show uOptLowEq P (uexec (m+1) (.ite e c₁ c₂) π s) (uexec (m+1) (.ite e c₁ c₂) π s')
            simp only [uexec]
            by_cases hb : evalE e s.store ≠ 0
            · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
              rw [if_pos hb, if_pos hb']
              refine uOptLowEq_map (ih c₁ h₁ π s s' ⟨hst, hrd, hdd⟩) ?_
              intro r r' hs hcs htr; exact ⟨hs, by rw [hcs], by rw [htr]⟩
            · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
              rw [if_neg hb, if_neg hb']
              refine uOptLowEq_map (ih c₂ h₂ π s s' ⟨hst, hrd, hdd⟩) ?_
              intro r r' hs hcs htr; exact ⟨hs, by rw [hcs], by rw [htr]⟩
    | loop e c₀ =>
        cases hc with
        | whileL _ hg hc₀ =>
            have hgv : evalE e s.store = evalE e s'.store := evalE_lowEq e hg hst
            show uOptLowEq P (uexec (m+1) (.loop e c₀) π s) (uexec (m+1) (.loop e c₀) π s')
            simp only [uexec]
            by_cases hb : evalE e s.store ≠ 0
            · have hb' : evalE e s'.store ≠ 0 := by rwa [hgv] at hb
              rw [if_pos hb, if_pos hb']
              refine uOptLowEq_bind (ih c₀ hc₀ π s s' ⟨hst, hrd, hdd⟩) ?_
              intro r₁ r₁' hs₁ hc1 ht1
              refine uOptLowEq_map
                (ih (.loop e c₀) (.whileL e hg hc₀) π r₁.1 r₁'.1 hs₁) ?_
              intro r₂ r₂' hs₂ hc2 ht2
              exact ⟨hs₂, by rw [hc1, hc2], by rw [ht1, ht2]⟩
            · have hb' : ¬ evalE e s'.store ≠ 0 := by rwa [hgv] at hb
              rw [if_neg hb, if_neg hb']
              exact ⟨⟨hst, hrd, hdd⟩, rfl, rfl⟩

/-! ## The executable checker -/

def ucheckNI (P : Partition) : UCmd → Bool
  | .skip        => true
  | .assign x e  => P x || exprLow P e
  | .seq c₁ c₂   => ucheckNI P c₁ && ucheckNI P c₂
  | .ite e c₁ c₂ => exprLow P e && ucheckNI P c₁ && ucheckNI P c₂
  | .loop e c    => exprLow P e && ucheckNI P c
  | .check _     => true
  | .access _    => true
  | .memop .alloc x => P x       -- stage 1j: High allocation is invisible
  | .memop _ _   => false        -- deref/free can fault: see `memops_not_yet_NI_typed`
  | .sop _ _ _   => false        -- stage 1o: the sink is not in the observation yet
  | .hop _ _ _   => false        -- stage 1v: heap values; see HeapValue

theorem ucheckNI_sound {P : Partition} :
    ∀ {c : UCmd}, ucheckNI P c = true → USecTy P c
  | .skip, _ => .skip
  | .check r, _ => .check r
  | .access r, _ => .access r
  | .assign _ _, h => by
      simp only [ucheckNI, Bool.or_eq_true] at h
      rcases h with hx | he
      · exact .assignH _ _ hx
      · exact .assignL _ _ he
  | .seq _ _, h => by
      simp only [ucheckNI, Bool.and_eq_true] at h
      exact .seq (ucheckNI_sound h.1) (ucheckNI_sound h.2)
  | .ite _ _ _, h => by
      simp only [ucheckNI, Bool.and_eq_true] at h
      exact .iteL _ h.1.1 (ucheckNI_sound h.1.2) (ucheckNI_sound h.2)
  | .loop _ _, h => by
      simp only [ucheckNI, Bool.and_eq_true] at h
      exact .whileL _ h.1 (ucheckNI_sound h.2)
  | .memop .alloc x, h => .allocH x h
  | .memop .deref _, h => by simp [ucheckNI] at h
  | .memop .free _, h => by simp [ucheckNI] at h
  | .sop _ _ _, h => by simp [ucheckNI] at h
  | .hop _ _ _, h => by simp [ucheckNI] at h

/-- Noninterference from a Boolean. -/
theorem uNI_of_check {P : Partition} {c : UCmd} (h : ucheckNI P c = true) :
    ∀ n π s s', uLowEq P s s' → uOptLowEq P (uexec n c π s) (uexec n c π s') :=
  fun n π s s' hle => usecTy_sound n c (ucheckNI_sound h) π s s' hle

/-- **Deref and free are not NI-typed, and stage 1j narrows the reason — a
    correction of record.** Stage 1h said flatly that heap operations are not NI-typed
    because `alloc` writes the fresh-address counter into the observable store. That is
    right only for a *Low* target. Writing the counter into a **High** variable is
    invisible, and `fresh` and `live` are not in the observation at all, so
    `USecTy.allocH` is sound with no change to `uLowEq` — stage 1j adds it, and this
    theorem accordingly shrinks to `deref` and `free`.

    Those two genuinely cannot have an unconditional rule *at any level*, and not for
    the reason stage 1h gave: they can **fault**, the fault sets `dead`, and `dead` is
    observable. `HeapNI.deref_leaks_through_dead` exhibits the leak. What they can have
    is a rule *conditional on the memory certificate* — which is the first place in the
    bundle where two certificates fail to be independent. See `HeapNI.lean`.

    What remains genuinely open is `allocL`: allocation into a Low variable needs
    `fresh` in the observation, which is the "are addresses public?" question, and
    `HeapNI.allocL_would_be_unsound` shows it is not derivable as things stand. -/
theorem memops_not_yet_NI_typed (x : String) (P : Partition) :
    ucheckNI P (.memop .deref x) = false ∧ ucheckNI P (.memop .free x) = false :=
  ⟨rfl, rfl⟩

/-- And the stage-1j addition, stated where the old limit was: allocation into a High
    variable *is* NI-typed. -/
theorem high_alloc_is_NI_typed (x : String) (P : Partition) (h : P x = true) :
    ucheckNI P (.memop .alloc x) = true := h

/-! ## The third certificate, and the price of it -/

/-- The handler of stage 1c is noninterferent at the partition making `n` secret —
    so it now carries **three** certificates: a budget, mediation, and NI. -/
theorem handler_NI (P : Partition) (h : ucheckNI P handler = true) :
    ∀ n π s s', uLowEq P s s' → uOptLowEq P (uexec n handler π s) (uexec n handler π s') :=
  uNI_of_check h

/-- A partition with something genuinely secret in it — otherwise noninterference
    says nothing. The handler never mentions `secret`, so it passes. -/
def Psec : Partition := fun x => x == "secret"

theorem handler_checks_NI : ucheckNI Psec handler = true := by decide

/-- **P1's deliverable: one program, three certificates, one check each.** The
    handler of stage 1c carries a cost budget, complete mediation, *and*
    termination-sensitive noninterference at a partition where `secret` is High —
    and the three compose by three different laws: budgets add (`costGA.mul`),
    authorization sets thread (Hoare), noninterference is conjunctive. -/
theorem handler_three_certificates :
    ucheck [] handler = some (["db"], 6)
  ∧ (∀ n π s r, uexec n handler π s = some r → r.2.1 ≤ 6)
  ∧ UMediated handler
  ∧ (∀ n π s s', uLowEq Psec s s' →
      uOptLowEq Psec (uexec n handler π s) (uexec n handler π s')) :=
  ⟨handler_checks, handler_budget, handler_mediated, uNI_of_check handler_checks_NI⟩

/-- **The partition is not degenerate and the checker has teeth on it.** `secret` is
    High and the handler's own variable is Low; branching on the secret is rejected,
    and so is laundering it through a Low variable first. So `handler_three_certificates`
    is a claim about a program that *could* have leaked and does not. -/
theorem Psec_rejects_leaks :
    Psec "secret" = true
  ∧ Psec "n" = false
  ∧ ucheckNI Psec (.ite (.var "secret") .skip .skip) = false
  ∧ ucheckNI Psec (.seq (.assign "n" (.var "secret")) (.ite (.var "n") .skip .skip))
      = false := by decide

/-- **The price of the result, recorded.** `check`/`access` are unconditionally
    well-typed *because* their resource names are syntactic constants: the language
    has no `access (e)`. Were resource selection store-dependent, `reads` would be a
    genuine flow channel and these two rules would need side conditions. The
    statement below is the honest form of that — every `access` in the syntax names
    a fixed resource, so the read sequence of a well-typed run is a function of its
    control flow alone. Dynamic selection is IDOR-shaped and remains the follow-on
    named in brick 35. -/
theorem access_is_static_by_design (r : String) (P : Partition) :
    USecTy P (.access r) ∧ ucheckNI P (.access r) = true :=
  ⟨.access r, rfl⟩

/-- A leak *is* still expressible and still caught: a secret-guarded loop fails the
    check, exactly as in brick 7 — the new constructors did not weaken the
    discipline. -/
theorem secret_loop_still_rejected :
    ucheckNI (fun x => x == "b") (.loop (.var "b") .skip) = false := by decide

end ConfTyping
