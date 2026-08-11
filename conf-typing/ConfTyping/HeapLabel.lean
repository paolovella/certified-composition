/-
  Stage 1w: per-address heap labels — the invariant.

  Stage 1v made the heap real and, to keep noninterference sound, made it entirely
  public: `storing_a_secret_is_refused`. Lifting that needs a **label per address**, and
  the payoff rules — storing a secret through a secret pointer, loading with the
  destination's level determined by the cell's — can only be *syntactic* if the analysis
  can read a cell's level off the program text. That is what this stage establishes, and
  it is deliberately the whole of this stage: the rules that spend the invariant come
  next.

  The pieces:

  * `UState` gains `hlab : Int → Bool`, fixed at allocation, and `MemOp` gains `allocS`
    so the allocation *site* declares the cell's level.
  * **Allocation zeroes its cell.** This is not tidiness. With reuse (stage 1u), a freed
    *secret* cell handed back out as a *public* one would expose its old contents — a
    public address whose value differs between runs. Zeroing is what makes relabelling
    on reuse safe, and it is an interaction between two stages that neither produced
    alone.
  * `LabInv P V s` — **every tracked pointer points at a cell of its own level** — with
    `JSecTy.toLabInv` proving it inductive. Separation (stage 1i) is what makes it work:
    no two tracked pointers can share a cell, so no cell has two levels.
  * `JSecTy.alloc` gains `P x = false` and `allocS` requires `P x = true`. That is the
    price, and it is a *consistency* condition, not a secrecy one — see the corrected
    note on `alloc_rule_rests_on_low_guards`.

  **What this stage does not do**, stated plainly because the field would otherwise look
  like it earns more than it does: the observation still has `s.heap = s'.heap`, so the
  heap is still public and `storing_a_secret_is_refused` still holds. `LabInv` is proved
  and unused by noninterference. Stage 1x replaces the heap conjunct with
  "labels agree, and public cells agree" and adds the rules; this stage exists so that
  when it does, the invariant it needs is already there and audited.
-/
import ConfTyping.HeapValue

namespace ConfTyping

/-! ## The invariant -/

/-- Every tracked pointer points at a cell of its own security level. -/
def LabInv (P : Partition) (V : List String) (s : UState) : Prop :=
  s.dead = false → ∀ x ∈ V, s.hlab (s.store x) = P x

theorem LabInv.mono {P : Partition} {V W : List String} {s : UState}
    (hsub : ∀ x ∈ W, x ∈ V) (h : LabInv P V s) : LabInv P W s :=
  fun hd x hx => h hd x (hsub x hx)

/-- The invariant carries whenever a step leaves the labels alone and leaves the store
    alone on the *surviving* tracked variables. Every rule but the two allocations. -/
theorem labInv_carry {P : Partition} {V V' : List String} {s t : UState}
    (hsub : ∀ x ∈ V', x ∈ V) (hst : ∀ x ∈ V', t.store x = s.store x)
    (hhl : t.hlab = s.hlab) (hdd : t.dead = false → s.dead = false)
    (h : LabInv P V s) : LabInv P V' t := by
  intro hdt x hx
  rw [hst x hx, hhl]
  exact h (hdd hdt) x (hsub x hx)

/-! ## Steps that leave the store and the labels alone -/

def LabStable (c : UCmd) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    uexec n c π s = some r →
      (∀ x, r.1.store x = s.store x) ∧ r.1.hlab = s.hlab ∧
      (r.1.dead = false → s.dead = false)

theorem labStable_skip : LabStable .skip := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      exact ⟨fun _ => by simp, by simp, by simp⟩

theorem labStable_check (q : String) : LabStable (.check q) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hp : π q = true
        · simp only [if_pos hp]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hp]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labStable_access (q : String) : LabStable (.access q) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩

theorem labStable_sop (op : SOp) (x : String) (e : SExpr) : LabStable (.sop op x e) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        cases op with
        | set  => exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        | emit => exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩

theorem labStable_deref (x : String) : LabStable (.memop .deref x) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store x) s.live = true
        · simp only [if_pos hl]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hl]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labStable_free (x : String) : LabStable (.memop .free x) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store x) s.live = true
        · simp only [if_pos hl]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hl]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labStable_hstore (p v : String) : LabStable (.hop .store p v) := by
  intro n π s r hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨fun _ => by simp, by simp, by simp⟩
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store p) s.live = true
        · simp only [if_pos hl]
          exact ⟨fun _ => by simp, by simp, fun _ => by simpa using hd⟩
        · simp only [if_neg hl]
          exact ⟨fun _ => by simp, by simp, fun h => absurd h (by simp)⟩

theorem labInv_of_stable {P : Partition} {V : List String} {c : UCmd}
    (hc : LabStable c) {n : Nat} {π : MedPolicy} {s : UState}
    {r : UState × Nat × List Bool} (hL : LabInv P V s) (hr : uexec n c π s = some r) :
    LabInv P V r.1 :=
  labInv_carry (s := s) (fun _ hx => hx) (fun x _ => (hc n π s r hr).1 x)
    (hc n π s r hr).2.1 (hc n π s r hr).2.2 hL

/-! ## The three steps that move the store -/

theorem labInv_assign {P : Partition} {V : List String} {x : String} {e : Expr}
    {n : Nat} {π : MedPolicy} {s : UState} {r : UState × Nat × List Bool}
    (hL : LabInv P V s) (hr : uexec n (.assign x e) π s = some r) :
    LabInv P (dropStr x V) r.1 := by
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]
        exact labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun _ _ => rfl) rfl id hL
      · simp only [if_neg hd]
        refine labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun y hy => ?_) rfl id hL
        show upd s.store x (evalE e s.store) y = s.store y
        simp only [upd, if_neg (dropStr_ne hy)]

theorem labInv_load {P : Partition} {V : List String} {d p : String}
    {n : Nat} {π : MedPolicy} {s : UState} {r : UState × Nat × List Bool}
    (hL : LabInv P V s) (hr : uexec n (.hop .load d p) π s = some r) :
    LabInv P (dropStr d V) r.1 := by
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr; subst hr
      by_cases hd : s.dead = true
      · simp only [if_pos hd]
        exact labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun _ _ => rfl) rfl id hL
      · simp only [if_neg hd]
        by_cases hl : memInt (s.store p) s.live = true
        · simp only [if_pos hl]
          refine labInv_carry (s := s) (fun _ hz => dropStr_mem hz) (fun y hy => ?_) rfl id hL
          show upd s.store d (s.heap (s.store p)) y = s.store y
          simp only [upd, if_neg (dropStr_ne hy)]
        · simp only [if_neg hl]
          intro hc; exact absurd hc (by simp)

/-- **The allocation case**, and the only one that needs the separation invariant: the
    new cell takes the label the rule demands, and every variable already tracked keeps
    its own, because the new address is not live and therefore not any of theirs. -/
theorem labInv_alloc {P : Partition} {V : List String} {x : String} {b : Bool}
    {n : Nat} {π : MedPolicy} {s : UState} {r : UState × Nat × List Bool}
    (hb : P x = b) (hS : SepInv V s) (hL : LabInv P V s)
    (hr : uexec n (.memop (if b then .allocS else .alloc) x) π s = some r) :
    LabInv P (x :: V) r.1 := by
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      by_cases hd : s.dead = true
      · cases b <;>
          simp only [uexec, if_pos hd, Option.some.injEq, if_true, if_false] at hr <;>
          subst hr <;> intro hc <;> exact absurd (hd ▸ hc) (by simp)
      · have hd0 : s.dead = false := by simpa using hd
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hS.2 hd0
        have hnl : memInt (pickAddr s.freed s.fresh) s.live = false := by
          cases hq : s.freed with
          | nil =>
              show memInt s.fresh s.live = false
              by_cases hm : memInt s.fresh s.live = true
              · exact absurd (hfr _ hm) (by omega)
              · simpa using hm
          | cons c cs => exact hdisj c (by rw [hq]; simp [memInt])
        have key : ∀ (lab : Bool), P x = lab →
            LabInv P (x :: V)
              ({ s with store := upd s.store x (pickAddr s.freed s.fresh),
                        live := pickAddr s.freed s.fresh :: s.live,
                        freed := dropInt (pickAddr s.freed s.fresh) s.freed,
                        fresh := bumpFresh s.freed s.fresh,
                        hlab := updBU s.hlab (pickAddr s.freed s.fresh) lab,
                        heap := updHU s.heap (pickAddr s.freed s.fresh) 0 }) := by
          intro lab hlabx _ y hy
          show updBU s.hlab (pickAddr s.freed s.fresh) lab
                 (upd s.store x (pickAddr s.freed s.fresh) y) = P y
          by_cases hyx : y = x
          · subst hyx
            simp only [upd, if_pos rfl]
            show (if pickAddr s.freed s.fresh = pickAddr s.freed s.fresh then lab
                  else s.hlab (pickAddr s.freed s.fresh)) = P y
            rw [if_pos rfl, hlabx]
          · have hyV : y ∈ V := memCons_ne hy hyx
            have hne : ¬ (s.store y = pickAddr s.freed s.fresh) := by
              intro hc
              exact absurd (hc ▸ hlive y hyV) (by simp [hnl])
            simp only [upd, if_neg hyx, updBU, if_neg hne]
            exact hL hd0 y hyV
        cases b with
        | false =>
            simp only [uexec, if_neg hd, if_false, Option.some.injEq] at hr
            subst hr; exact key false hb
        | true =>
            simp only [uexec, if_neg hd, if_true, Option.some.injEq] at hr
            subst hr; exact key true hb

/-! ## Preservation -/

/-- **The label invariant is inductive.** Every rule of the joint judgment preserves
    "each tracked pointer points at a cell of its own level". The separation invariant
    is a hypothesis because the allocation case needs it — which is stage 1i paying for
    stage 1w. -/
theorem JSecTy.toLabInv {P : Partition} {V : List String} {c : UCmd} {V' : List String}
    (h : JSecTy P V c V') :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      SepInv V s → LabInv P V s → uexec n c π s = some r → LabInv P V' r.1 := by
  induction h with
  | skip _ => intro n π s r _ hL hr; exact labInv_of_stable labStable_skip hL hr
  | assignH _ x e _ => intro n π s r _ hL hr; exact labInv_assign hL hr
  | assignL _ x e _ => intro n π s r _ hL hr; exact labInv_assign hL hr
  | check _ q => intro n π s r _ hL hr; exact labInv_of_stable (labStable_check q) hL hr
  | access _ q => intro n π s r _ hL hr; exact labInv_of_stable (labStable_access q) hL hr
  | setH _ x e _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_sop .set x e) hL hr
  | setL _ x e _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_sop .set x e) hL hr
  | emit _ q e _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_sop .emit q e) hL hr
  | deref _ x _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_deref x) hL hr
  | storeL _ p v _ _ _ => intro n π s r _ hL hr; exact labInv_of_stable (labStable_hstore p v) hL hr
  | loadL _ d p _ _ => intro n π s r _ hL hr; exact labInv_load hL hr
  | loadH _ d p _ _ => intro n π s r _ hL hr; exact labInv_load hL hr
  | free _ x _ _ =>
      intro n π s r _ hL hr
      exact LabInv.mono (fun _ hz => dropStr_mem hz)
        (labInv_of_stable (labStable_free x) hL hr)
  | alloc _ x hx =>
      intro n π s r hS hL hr
      exact labInv_alloc (b := false) hx hS hL (by simpa using hr)
  | allocS _ x hx =>
      intro n π s r hS hL hr
      exact labInv_alloc (b := true) hx hS hL (by simpa using hr)
  | @seq V V₁ V₂ c₁ c₂ h₁ h₂ ih₁ ih₂ =>
      intro n π s r hS hL hr
      cases n with
      | zero => simp [uexec] at hr
      | succ m =>
          rw [uexec_seq_eq] at hr
          rcases e₁ : uexec m c₁ π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁, Option.bind_some] at hr
            rcases e₂ : uexec m c₂ π r₁.1 with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact ih₂ m π r₁.1 r₂ (h₁.toSepCert.safe m π s r₁ hS e₁)
                (ih₁ m π s r₁ hS hL e₁) e₂
  | @iteL V V₁ V₂ c₁ c₂ e _ h₁ h₂ ih₁ ih₂ =>
      intro n π s r hS hL hr
      cases n with
      | zero => simp [uexec] at hr
      | succ m =>
          rw [uexec_ite_eq] at hr
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg] at hr
            rcases e₁ : uexec m c₁ π s with _ | r₁
            · rw [e₁] at hr; simp at hr
            · rw [e₁] at hr; simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact LabInv.mono (fun _ hz => interStr_left hz) (ih₁ m π s r₁ hS hL e₁)
          · rw [if_neg hg] at hr
            rcases e₂ : uexec m c₂ π s with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact LabInv.mono (fun _ hz => interStr_right hz) (ih₂ m π s r₂ hS hL e₂)
  | @whileW V W W₁ c₀ e _ hWV h₀ hWW₁ ih =>
      have hbody : SepCert W c₀ W := SepCert.weakenPost h₀.toSepCert hWW₁
      have main : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
          SepInv W s → LabInv P W s → uexec n (.loop e c₀) π s = some r →
          LabInv P W r.1 := by
        intro n
        induction n with
        | zero => intro π s r _ _ hr; simp [uexec] at hr
        | succ m ihm =>
            intro π s r hSW hLW hr
            rw [uexec_loop_eq] at hr
            by_cases hg : evalE e s.store ≠ 0
            · rw [if_pos hg] at hr
              rcases e₁ : uexec m c₀ π s with _ | r₁
              · rw [e₁] at hr; simp at hr
              · rw [e₁, Option.bind_some] at hr
                rcases e₂ : uexec m (.loop e c₀) π r₁.1 with _ | r₂
                · rw [e₂] at hr; simp at hr
                · rw [e₂] at hr
                  simp only [Option.map_some, Option.some.injEq] at hr
                  subst hr
                  exact ihm π r₁.1 r₂ (hbody.safe m π s r₁ hSW e₁)
                    (LabInv.mono hWW₁ (ih m π s r₁ hSW hLW e₁)) e₂
            · rw [if_neg hg] at hr
              simp only [Option.some.injEq] at hr; subst hr; exact hLW
      intro n π s r hS hL hr
      exact main n π s r (SepInv.mono hWV hS) (LabInv.mono hWV hL) hr

/-- From a fresh state the invariant holds trivially, so a checked program maintains it
    all the way through. -/
theorem LabInv.initU {P : Partition} {σ : Store} : LabInv P [] (initU σ) := by
  intro _ x hx; simp at hx

theorem allcheck_maintains_labels {P : Partition} {c : UCmd} {A' V' : List String}
    {k : Nat} (h : allcheck P [] [] c = some (A', V', k)) :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n c π (initU σ) = some r → LabInv P V' r.1 :=
  fun n π σ r hr =>
    (allcheck_sound c [] [] A' V' k h).joint.toLabInv n π (initU σ) r
      SepInv.initU LabInv.initU hr

/-! ## Witnesses -/

/-- A public buffer and a secret one, side by side. -/
def twoCells : UCmd := .seq (.memop .alloc "buf") (.memop .allocS "secret")

theorem twoCells_checks : allcheck Psec [] [] twoCells = some ([], ["secret", "buf"], 2) := by
  decide

/-- **The labels really are set, and they differ.** The public cell is labelled `false`
    and the secret one `true`, at distinct addresses. -/
theorem twoCells_labels :
    ((uexec 5 twoCells (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.store "buf", r.1.store "secret",
                 r.1.hlab (r.1.store "buf"), r.1.hlab (r.1.store "secret"))))
      = some (0, 1, false, true) := by decide

/-- The allocation site must agree with the pointer's level: a public allocation into a
    secret variable, or the reverse, is refused. -/
theorem allocation_site_must_match_the_level :
    allcheck Psec [] [] (.memop .alloc "secret") = none
  ∧ allcheck Psec [] [] (.memop .allocS "buf") = none := by decide

/-- **Allocation zeroes.** With reuse, a recycled cell must not carry its old contents
    across a relabelling — so `alloc` clears it. Write 7 through a pointer, free it,
    allocate again, and the new cell reads 0 rather than 7. -/
theorem allocation_zeroes :
    ((uexec 13 (.seq (.memop .alloc "p")
                (.seq (.assign "v" (.num 7))
                 (.seq (.hop .store "p" "v")
                  (.seq (.memop .free "p")
                   (.seq (.memop .alloc "q") (.hop .load "d" "q"))))))
        (fun _ => true) (initU (fun _ => 0))).map (fun r => (r.1.store "d", r.1.err)))
      = some (0, false) := by decide

/-! ## What is not claimed

    The observation still contains `s.heap = s'.heap`: the heap is public, and
    `HeapValue.storing_a_secret_is_refused` still holds. `LabInv` is proved and *not yet
    used* by noninterference — which is the honest description of an invariant stage.

    Stage 1x is the other half: replace the heap conjunct with "labels agree, and public
    cells agree", and add the rules that spend the invariant — `storeH` (a secret
    through a secret pointer is invisible) and a label-aware `loadL`. Splitting it this
    way means the invariant is audited before anything depends on it, which is the order
    stages 1j and 1k used for the analogous problem. -/

/-- The scope, as a theorem: the heap is still public at this stage. -/
theorem heap_still_public_at_this_stage :
    jcheck Psec ["p"] (.hop .store "p" "secret") = none := by decide

end ConfTyping
