/-
  The composable core, stage 1i: `free`, and why stage 1h could not have it.

  Stage 1h shipped `MemCert` with a deliberate hole: `alloc` and `deref` had rules,
  `free` had none, and `free_has_no_rule` recorded the reason in prose — "dropping an
  address from `live` invalidates every alias of it". This stage does two things, and
  the second matters more than the first.

  **First**, it closes the hole. `SepInv` strengthens `MemInv` with two further
  conjuncts — the tracked variables hold *pairwise distinct* addresses, and every live
  address is below the allocation counter — and with those, `free` gets a rule and
  `slcheck_no_fault` extends memory safety to programs that deallocate. That is row 6's
  use-after-free half, CWE-416, on the unified machine.

  **Second**, and this is the part worth the module: it proves that stage 1h's hole was
  *real*. `memInv_not_preserved_by_free` exhibits a state satisfying `MemInv` in which a
  single `free` step breaks `MemInv`. So the missing rule was not laziness or an
  unfinished proof — the weaker invariant is genuinely not inductive for `free`, and no
  amount of work on stage 1h's `MemCert` could have added the rule. A limit that was
  recorded as a theorem is now *explained* by a theorem.

  The separation conjunct is load-bearing in the proof and unreachable in the language,
  which is an honest thing to have to say. `assign` always *drops* its target from the
  tracked set, so this `UCmd` cannot construct two tracked aliases; but soundness of the
  `free` rule quantifies over every state satisfying the invariant, not only over
  reachable ones, and `MemInv` alone does not imply separation. The witness above is
  exactly such an unreachable-but-admissible state. Weakening the invariant to
  "reachable states only" would trade a two-line conjunct for a global reachability
  argument, and would break the moment the language gained a pointer-copying assignment.

  `slcheck_extends_umcheck` records that this is a conservative extension: everything
  stage 1h accepted, stage 1i accepts, with the same result set. So nothing regressed,
  and `SepInv.toMemInv` lets a stage-1h consumer keep its weaker invariant.
-/
import ConfTyping.MemCert

namespace ConfTyping

/-! ## Two more facts about removing an address -/

theorem memInt_dropInt_of_ne {a b : Int} : ∀ {L : List Int},
    memInt a L = true → ¬ (a = b) → memInt a (dropInt b L) = true
  | [],      h, _  => by simp [memInt] at h
  | x :: xs, h, hn => by
      simp only [memInt, Bool.or_eq_true, beq_iff_eq] at h
      by_cases hx : x = b
      · rw [dropInt, if_pos (by simp [hx])]
        rcases h with h | h
        · exact absurd (hx ▸ h.symm) hn
        · exact memInt_dropInt_of_ne h hn
      · rw [dropInt, if_neg (by simpa using hx)]
        simp only [memInt, Bool.or_eq_true, beq_iff_eq]
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (memInt_dropInt_of_ne h hn)

theorem dropInt_memInt {a b : Int} : ∀ {L : List Int},
    memInt a (dropInt b L) = true → memInt a L = true
  | [],      h => by simp [dropInt, memInt] at h
  | x :: xs, h => by
      simp only [memInt, Bool.or_eq_true, beq_iff_eq]
      by_cases hx : x = b
      · rw [dropInt, if_pos (by simp [hx])] at h
        exact Or.inr (dropInt_memInt h)
      · rw [dropInt, if_neg (by simpa using hx)] at h
        simp only [memInt, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (dropInt_memInt h)

theorem memInt_dropInt_self (a : Int) : ∀ (L : List Int), memInt a (dropInt a L) = false
  | []      => rfl
  | x :: xs => by
      by_cases hx : x = a
      · rw [dropInt, if_pos (by simp [hx])]; exact memInt_dropInt_self a xs
      · rw [dropInt, if_neg (by simpa using hx)]
        simp only [memInt, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨by simpa using hx, memInt_dropInt_self a xs⟩

theorem memInt_cons_ne {a b : Int} {L : List Int} (hne : ¬ (b = a))
    (h : memInt b L = false) : memInt b (a :: L) = false := by
  simp only [memInt, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  exact ⟨fun hc => hne hc.symm, h⟩

/-! ## The separating invariant -/

/-- Stage 1h's invariant plus the two conjuncts `free` needs: distinct tracked
    variables hold **distinct** addresses, and every live address is below the
    allocation counter — which is what makes a freshly allocated address genuinely
    new. -/
def SepInv (V : List String) (s : UState) : Prop :=
  s.err = false ∧
  (s.dead = false →
      (∀ x ∈ V, memInt (s.store x) s.live = true)
    ∧ (∀ x ∈ V, ∀ y ∈ V, ¬ (x = y) → ¬ (s.store x = s.store y))
    ∧ (∀ a : Int, memInt a s.live = true → a < s.fresh)
    -- the two conjuncts a *reusing* allocator forces:
    ∧ (∀ a : Int, memInt a s.freed = true → memInt a s.live = false)
    ∧ (∀ a : Int, memInt a s.freed = true → a < s.fresh))

/-- The strengthening really is a strengthening, so anything downstream that only
    needs stage 1h's invariant can still be fed one. -/
theorem SepInv.toMemInv {V : List String} {s : UState} (h : SepInv V s) : MemInv V s :=
  ⟨h.1, fun hd => (h.2 hd).1⟩

/-- The fresh state satisfies it. -/
theorem SepInv.initU {σ : Store} : SepInv [] (initU σ) :=
  ⟨rfl, fun _ =>
    ⟨by intro x hx; simp at hx, by intro x hx; simp at hx,
     by intro a ha; have h0 : memInt a ([] : List Int) = true := ha; simp [memInt] at h0,
     by intro a ha; have h0 : memInt a ([] : List Int) = true := ha; simp [memInt] at h0,
     by intro a ha; have h0 : memInt a ([] : List Int) = true := ha; simp [memInt] at h0⟩⟩

/-- Membership in a cons, minus the head. Used four times in `SepCert.alloc`. -/
theorem memCons_ne {q x : String} {V : List String} (hq : q ∈ x :: V) (hqx : ¬ (q = x)) :
    q ∈ V := by
  rcases List.mem_cons.mp hq with h | h
  · exact absurd h hqx
  · exact h

/-- A **separation certificate**: the same Hoare-triple shape as `MemCert`, over the
    stronger invariant. -/
structure SepCert (V : List String) (c : UCmd) (V' : List String) : Prop where
  safe : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    SepInv V s → uexec n c π s = some r → SepInv V' r.1

/-! ## Composition — unchanged in shape from stage 1h -/

theorem SepCert.seq {V V₁ V₂ : List String} {c₁ c₂ : UCmd}
    (h₁ : SepCert V c₁ V₁) (h₂ : SepCert V₁ c₂ V₂) : SepCert V (.seq c₁ c₂) V₂ := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      rw [uexec_seq_eq] at hr
      rcases e₁ : uexec n c₁ π s with _ | r₁
      · rw [e₁] at hr; simp at hr
      · rw [e₁, Option.bind_some] at hr
        rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
        · rw [e₂] at hr; simp at hr
        · rw [e₂] at hr
          simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact h₂.safe n π r₁.1 r₂ (h₁.safe n π s r₁ hinv e₁) e₂

/-- Weakening the tracked set preserves the invariant: every conjunct is downward
    closed in `V`. This is what lets a branch join by intersection. -/
theorem SepInv.mono {V W : List String} {s : UState} (hsub : ∀ x ∈ W, x ∈ V)
    (h : SepInv V s) : SepInv W s :=
  ⟨h.1, fun hd =>
    ⟨fun x hx => (h.2 hd).1 x (hsub x hx),
     fun x hx y hy => (h.2 hd).2.1 x (hsub x hx) y (hsub y hy),
     (h.2 hd).2.2.1, (h.2 hd).2.2.2.1, (h.2 hd).2.2.2.2⟩⟩

theorem SepCert.ite {V V₁ V₂ : List String} {e : Expr} {c₁ c₂ : UCmd}
    (h₁ : SepCert V c₁ V₁) (h₂ : SepCert V c₂ V₂) :
    SepCert V (.ite e c₁ c₂) (interStr V₁ V₂) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      rw [uexec_ite_eq] at hr
      by_cases hg : evalE e s.store ≠ 0
      · rw [if_pos hg] at hr
        rcases e₁ : uexec n c₁ π s with _ | r₁
        · rw [e₁] at hr; simp at hr
        · rw [e₁] at hr; simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact SepInv.mono (fun _ hq => interStr_left hq) (h₁.safe n π s r₁ hinv e₁)
      · rw [if_neg hg] at hr
        rcases e₂ : uexec n c₂ π s with _ | r₂
        · rw [e₂] at hr; simp at hr
        · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
          subst hr
          exact SepInv.mono (fun _ hq => interStr_right hq) (h₂.safe n π s r₂ hinv e₂)

/-! ## The rules -/

theorem SepCert.skip {V : List String} : SepCert V .skip V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; exact hinv

theorem SepCert.assign {V : List String} (x : String) (e : Expr) :
    SepCert V (.assign x e) (dropStr x V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]
        exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [if_neg hd]
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hv hd0
        refine ⟨he, fun _ => ⟨?_, ?_, hfr, hdisj, hfb⟩⟩
        · intro q hq
          show memInt (upd s.store x (evalE e s.store) q) s.live = true
          simp only [upd, if_neg (dropStr_ne hq)]
          exact hlive q (dropStr_mem hq)
        · intro q hq y hy hne
          show ¬ (upd s.store x (evalE e s.store) q = upd s.store x (evalE e s.store) y)
          simp only [upd, if_neg (dropStr_ne hq), if_neg (dropStr_ne hy)]
          exact hinj q (dropStr_mem hq) y (dropStr_mem hy) hne

theorem SepCert.check {V : List String} (r₀ : String) : SepCert V (.check r₀) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [if_neg hd]
        by_cases hp : π r₀ = true
        · simp only [if_pos hp]; exact ⟨he, fun _ => hv hd0⟩
        · simp only [if_neg hp]; exact ⟨he, fun hc => absurd hc (by simp)⟩

theorem SepCert.access {V : List String} (r₀ : String) : SepCert V (.access r₀) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [if_neg hd]; exact ⟨he, fun _ => hv hd0⟩

/-- **Allocation, now with separation.** The new address is `s.fresh`, and every
    address already live is `< s.fresh`, so the new pointer is distinct from every
    tracked one — this is where the third conjunct pays for itself. -/
theorem SepCert.alloc {V : List String} (x : String) :
    SepCert V (.memop .alloc x) (x :: V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [if_neg hd]
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hv hd0
        -- the address handed out is not live, whether it came from the free list or
        -- the counter: from the free list by disjointness, from the counter by
        -- freshness. This is the step reuse makes non-trivial.
        have hnl : memInt (pickAddr s.freed s.fresh) s.live = false := by
          cases hq : s.freed with
          | nil =>
              show memInt s.fresh s.live = false
              by_cases hm : memInt s.fresh s.live = true
              · exact absurd (hfr _ hm) (by omega)
              · simpa using hm
          | cons b bs =>
              show memInt b s.live = false
              exact hdisj b (by rw [hq]; simp [memInt])
        have hlt : pickAddr s.freed s.fresh < bumpFresh s.freed s.fresh := by
          cases hq : s.freed with
          | nil => show s.fresh < s.fresh + 1; omega
          | cons b bs =>
              show b < s.fresh
              exact hfb b (by rw [hq]; simp [memInt])
        have hbump : s.fresh ≤ bumpFresh s.freed s.fresh := by
          cases s.freed with
          | nil => show s.fresh ≤ s.fresh + 1; omega
          | cons _ _ => exact Int.le_refl _
        refine ⟨he, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
        · intro q hq
          show memInt (upd s.store x (pickAddr s.freed s.fresh) q)
                 (pickAddr s.freed s.fresh :: s.live) = true
          by_cases hqx : q = x
          · subst hqx; simp [upd, memInt]
          · simp only [upd, if_neg hqx, memInt, Bool.or_eq_true]
            exact Or.inr (hlive q (memCons_ne hq hqx))
        · intro q hq y hy hne
          show ¬ (upd s.store x (pickAddr s.freed s.fresh) q
                = upd s.store x (pickAddr s.freed s.fresh) y)
          by_cases hqx : q = x
          · have hyx : ¬ (y = x) := fun h => hne (hqx.trans h.symm)
            simp only [upd, if_pos hqx, if_neg hyx]
            intro hc
            exact absurd (hc ▸ hlive y (memCons_ne hy hyx)) (by simp [hnl])
          · by_cases hyx : y = x
            · simp only [upd, if_neg hqx, if_pos hyx]
              intro hc
              exact absurd (hc ▸ hlive q (memCons_ne hq hqx)) (by simp [hnl])
            · simp only [upd, if_neg hqx, if_neg hyx]
              exact hinj q (memCons_ne hq hqx) y (memCons_ne hy hyx) hne
        · intro a ha
          show a < bumpFresh s.freed s.fresh
          simp only [memInt, Bool.or_eq_true, beq_iff_eq] at ha
          rcases ha with ha | ha
          · omega
          · have := hfr a ha; omega
        · intro a ha
          have ha' : memInt a s.freed = true :=
            dropInt_memInt (b := pickAddr s.freed s.fresh) ha
          have hne : ¬ (a = pickAddr s.freed s.fresh) := by
            intro hc
            have : memInt a (dropInt a s.freed) = true := by rw [hc] at ha ⊢; exact ha
            rw [memInt_dropInt_self] at this
            exact absurd this (by simp)
          exact memInt_cons_ne hne (hdisj a ha')
        · intro a ha
          show a < bumpFresh s.freed s.fresh
          have := hfb a (dropInt_memInt (b := pickAddr s.freed s.fresh) ha)
          omega

theorem SepCert.allocS {V : List String} (x : String) :
    SepCert V (.memop .allocS x) (x :: V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [if_neg hd]
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hv hd0
        -- the address handed out is not live, whether it came from the free list or
        -- the counter: from the free list by disjointness, from the counter by
        -- freshness. This is the step reuse makes non-trivial.
        have hnl : memInt (pickAddr s.freed s.fresh) s.live = false := by
          cases hq : s.freed with
          | nil =>
              show memInt s.fresh s.live = false
              by_cases hm : memInt s.fresh s.live = true
              · exact absurd (hfr _ hm) (by omega)
              · simpa using hm
          | cons b bs =>
              show memInt b s.live = false
              exact hdisj b (by rw [hq]; simp [memInt])
        have hlt : pickAddr s.freed s.fresh < bumpFresh s.freed s.fresh := by
          cases hq : s.freed with
          | nil => show s.fresh < s.fresh + 1; omega
          | cons b bs =>
              show b < s.fresh
              exact hfb b (by rw [hq]; simp [memInt])
        have hbump : s.fresh ≤ bumpFresh s.freed s.fresh := by
          cases s.freed with
          | nil => show s.fresh ≤ s.fresh + 1; omega
          | cons _ _ => exact Int.le_refl _
        refine ⟨he, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
        · intro q hq
          show memInt (upd s.store x (pickAddr s.freed s.fresh) q)
                 (pickAddr s.freed s.fresh :: s.live) = true
          by_cases hqx : q = x
          · subst hqx; simp [upd, memInt]
          · simp only [upd, if_neg hqx, memInt, Bool.or_eq_true]
            exact Or.inr (hlive q (memCons_ne hq hqx))
        · intro q hq y hy hne
          show ¬ (upd s.store x (pickAddr s.freed s.fresh) q
                = upd s.store x (pickAddr s.freed s.fresh) y)
          by_cases hqx : q = x
          · have hyx : ¬ (y = x) := fun h => hne (hqx.trans h.symm)
            simp only [upd, if_pos hqx, if_neg hyx]
            intro hc
            exact absurd (hc ▸ hlive y (memCons_ne hy hyx)) (by simp [hnl])
          · by_cases hyx : y = x
            · simp only [upd, if_neg hqx, if_pos hyx]
              intro hc
              exact absurd (hc ▸ hlive q (memCons_ne hq hqx)) (by simp [hnl])
            · simp only [upd, if_neg hqx, if_neg hyx]
              exact hinj q (memCons_ne hq hqx) y (memCons_ne hy hyx) hne
        · intro a ha
          show a < bumpFresh s.freed s.fresh
          simp only [memInt, Bool.or_eq_true, beq_iff_eq] at ha
          rcases ha with ha | ha
          · omega
          · have := hfr a ha; omega
        · intro a ha
          have ha' : memInt a s.freed = true :=
            dropInt_memInt (b := pickAddr s.freed s.fresh) ha
          have hne : ¬ (a = pickAddr s.freed s.fresh) := by
            intro hc
            have : memInt a (dropInt a s.freed) = true := by rw [hc] at ha ⊢; exact ha
            rw [memInt_dropInt_self] at this
            exact absurd this (by simp)
          exact memInt_cons_ne hne (hdisj a ha')
        · intro a ha
          show a < bumpFresh s.freed s.fresh
          have := hfb a (dropInt_memInt (b := pickAddr s.freed s.fresh) ha)
          omega

theorem SepCert.deref {V : List String} (x : String) (hx : memStr x V = true) :
    SepCert V (.memop .deref x) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        have hlive : memInt (s.store x) s.live = true := (hv hd0).1 x (memStr_mem hx)
        simp only [if_neg hd, if_pos hlive]
        exact ⟨he, fun _ => hv hd0⟩

/-- **Deallocation — the rule stage 1h could not state.** Freeing `x` removes one
    address from `live`, and every *other* tracked variable survives precisely because
    separation says its address is a different one. `x` itself leaves the tracked set,
    so a later dereference of it is rejected: that is use-after-free, CWE-416. -/
theorem SepCert.free {V : List String} (x : String) (hx : memStr x V = true) :
    SepCert V (.memop .free x) (dropStr x V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]
        exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hv hd0
        have hxV : x ∈ V := memStr_mem hx
        have hxl : memInt (s.store x) s.live = true := hlive x hxV
        simp only [if_neg hd, if_pos hxl]
        refine ⟨he, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
        · intro q hq
          show memInt (s.store q) (dropInt (s.store x) s.live) = true
          exact memInt_dropInt_of_ne (hlive q (dropStr_mem hq))
            (hinj q (dropStr_mem hq) x hxV (dropStr_ne hq))
        · intro q hq y hy hne
          exact hinj q (dropStr_mem hq) y (dropStr_mem hy) hne
        · intro a ha
          exact hfr a (dropInt_memInt ha)
        · -- the freed address is gone from `live`, and the ones already on the free
          -- list stay off it. A *secret* address is retired rather than listed, which
          -- is the branch that closes stage 1y's gap.
          intro a ha
          have hstep : ∀ b : Int,
              memInt b (if s.hlab (s.store x) then s.freed else s.store x :: s.freed) = true →
              b = s.store x ∨ memInt b s.freed = true := by
            intro b hb
            by_cases hlab : s.hlab (s.store x) = true
            · rw [if_pos hlab] at hb; exact Or.inr hb
            · rw [if_neg hlab] at hb
              simp only [memInt, Bool.or_eq_true, beq_iff_eq] at hb
              rcases hb with hb | hb
              · exact Or.inl hb.symm
              · exact Or.inr hb
          rcases hstep a ha with ha' | ha'
          · show memInt a (dropInt (s.store x) s.live) = false
            rw [ha']; exact memInt_dropInt_self _ _
          · show memInt a (dropInt (s.store x) s.live) = false
            by_cases hm : memInt a (dropInt (s.store x) s.live) = true
            · exact absurd (dropInt_memInt hm) (by simp [hdisj a ha'])
            · simpa using hm
        · intro a ha
          have hstep : ∀ b : Int,
              memInt b (if s.hlab (s.store x) then s.freed else s.store x :: s.freed) = true →
              b = s.store x ∨ memInt b s.freed = true := by
            intro b hb
            by_cases hlab : s.hlab (s.store x) = true
            · rw [if_pos hlab] at hb; exact Or.inr hb
            · rw [if_neg hlab] at hb
              simp only [memInt, Bool.or_eq_true, beq_iff_eq] at hb
              rcases hb with hb | hb
              · exact Or.inl hb.symm
              · exact Or.inr hb
          rcases hstep a ha with ha' | ha'
          · rw [ha']; exact hfr _ hxl
          · exact hfb a ha'

/-- **Loading through a live pointer is safe**, and the destination leaves the tracked
    set: what came out of the heap is a value, not a pointer we have any claim about. -/
theorem SepCert.load {V : List String} (d p : String) (hp : memStr p V = true) :
    SepCert V (.hop .load d p) (dropStr d V) := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        obtain ⟨hlive, hinj, hfr, hdisj, hfb⟩ := hv hd0
        have hl : memInt (s.store p) s.live = true := hlive p (memStr_mem hp)
        simp only [if_neg hd, if_pos hl]
        refine ⟨he, fun _ => ⟨?_, ?_, hfr, hdisj, hfb⟩⟩
        · intro q hq
          show memInt (upd s.store d (s.heap (s.store p)) q) s.live = true
          simp only [upd, if_neg (dropStr_ne hq)]
          exact hlive q (dropStr_mem hq)
        · intro q hq y hy hne
          show ¬ (upd s.store d (s.heap (s.store p)) q
                = upd s.store d (s.heap (s.store p)) y)
          simp only [upd, if_neg (dropStr_ne hq), if_neg (dropStr_ne hy)]
          exact hinj q (dropStr_mem hq) y (dropStr_mem hy) hne

/-- **Storing through a live pointer is safe**, and changes nothing the separation
    invariant tracks — the heap's *contents* are not part of it. -/
theorem SepCert.store {V : List String} (p v : String) (hp : memStr p V = true) :
    SepCert V (.hop .store p v) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        have hl : memInt (s.store p) s.live = true := (hv hd0).1 p (memStr_mem hp)
        simp only [if_neg hd, if_pos hl]
        exact ⟨he, fun _ => hv hd0⟩

/-- String operations do not touch the heap, so the separation invariant rides
    through untouched. -/
theorem SepCert.sop {V : List String} (op : SOp) (x : String) (e : SExpr) :
    SepCert V (.sop op x e) V := by
  constructor
  intro n π s r hinv hr
  cases n with
  | zero => simp [uexec] at hr
  | succ n =>
      simp only [uexec, Option.some.injEq] at hr
      subst hr
      obtain ⟨he, hv⟩ := hinv
      by_cases hd : s.dead = true
      · simp only [if_pos hd]; exact ⟨he, fun hc => absurd (hd ▸ hc) (by simp)⟩
      · have hd0 : s.dead = false := by simpa using hd
        simp only [if_neg hd]
        cases op with
        | set  => exact ⟨he, fun _ => hv hd0⟩
        | emit => exact ⟨he, fun _ => hv hd0⟩

/-! ## The checker -/

def slcheck : List String → UCmd → Option (List String)
  | V, .skip              => some V
  | V, .assign x _        => some (dropStr x V)
  | V, .check _           => some V
  | V, .access _          => some V
  | V, .memop .alloc x    => some (x :: V)
  | V, .memop .allocS x   => some (x :: V)
  | V, .memop .deref x    => if memStr x V then some V else none
  | V, .memop .free x     => if memStr x V then some (dropStr x V) else none
  | _, .sop _ _ _         => none
  | V, .hop .load d p     => if memStr p V then some (dropStr d V) else none
  | V, .hop .store p _    => if memStr p V then some V else none
  | V, .seq c₁ c₂         => (slcheck V c₁).bind fun V₁ => slcheck V₁ c₂
  | V, .ite _ c₁ c₂       => match slcheck V c₁, slcheck V c₂ with
                             | some V₁, some V₂ => some (interStr V₁ V₂)
                             | _, _ => none
  | _, .loop _ _          => none

theorem slcheck_sound : ∀ (c : UCmd) (V V' : List String),
    slcheck V c = some V' → SepCert V c V'
  | .skip, V, V', h => by
      simp only [slcheck, Option.some.injEq] at h; subst h; exact SepCert.skip
  | .assign x e, V, V', h => by
      simp only [slcheck, Option.some.injEq] at h; subst h; exact SepCert.assign x e
  | .check r, V, V', h => by
      simp only [slcheck, Option.some.injEq] at h; subst h; exact SepCert.check r
  | .access r, V, V', h => by
      simp only [slcheck, Option.some.injEq] at h; subst h; exact SepCert.access r
  | .memop .alloc x, V, V', h => by
      simp only [slcheck, Option.some.injEq] at h; subst h; exact SepCert.alloc x
  | .memop .allocS x, V, V', h => by
      simp only [slcheck, Option.some.injEq] at h; subst h; exact SepCert.allocS x
  | .memop .deref x, V, V', h => by
      simp only [slcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        exact SepCert.deref x hx
      · rw [if_neg hx] at h; simp at h
  | .memop .free x, V, V', h => by
      simp only [slcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq] at h; subst h
        exact SepCert.free x hx
      · rw [if_neg hx] at h; simp at h
  | .seq c₁ c₂, V, V', h => by
      simp only [slcheck] at h
      rcases e₁ : slcheck V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        exact SepCert.seq (slcheck_sound c₁ V V₁ e₁) (slcheck_sound c₂ V₁ V' h)
  | .ite e c₁ c₂, V, V', h => by
      simp only [slcheck] at h
      rcases e₁ : slcheck V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rcases e₂ : slcheck V c₂ with _ | V₂
        · rw [e₁, e₂] at h; simp at h
        · rw [e₁, e₂] at h
          simp only [Option.some.injEq] at h; subst h
          exact SepCert.ite (slcheck_sound c₁ V V₁ e₁) (slcheck_sound c₂ V V₂ e₂)
  | .hop .load d p, V, V', h => by
      simp only [slcheck] at h
      by_cases hp : memStr p V = true
      · rw [if_pos hp] at h
        simp only [Option.some.injEq] at h; subst h
        exact SepCert.load d p hp
      · rw [if_neg hp] at h; simp at h
  | .hop .store p v, V, V', h => by
      simp only [slcheck] at h
      by_cases hp : memStr p V = true
      · rw [if_pos hp] at h
        simp only [Option.some.injEq] at h; subst h
        exact SepCert.store p v hp
      · rw [if_neg hp] at h; simp at h
  | .loop _ _, _, _, h => by simp [slcheck] at h

/-- **Memory safety, with deallocation.** A checked program never faults — no wild
    dereference and no use-after-free. -/
theorem slcheck_no_fault {c : UCmd} {V' : List String} (h : slcheck [] c = some V') :
    ∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
      uexec n c π (initU σ) = some r → r.1.err = false := by
  intro n π σ r hr
  exact ((slcheck_sound c [] V' h).safe n π (initU σ) r SepInv.initU hr).1

/-! ## Why stage 1h could not do this

    The interesting direction: not "here is the rule" but "here is why the weaker
    invariant could not have one". -/

/-- A state in which two tracked variables alias the same live address. It satisfies
    stage 1h's `MemInv` — nothing there forbids aliasing — and violates `SepInv`. -/
def aliasState : UState :=
  { store := fun _ => 5, auth := [], reads := [], dead := false,
    heap := fun _ => 0, live := [5], fresh := 6, err := false, freed := [], hlab := fun _ => false, sstore := fun _ => [], sink := []  }

/-- **Stage 1h's invariant is not inductive for `free`.** From a state satisfying
    `MemInv ["p","q"]`, one `free "p"` step lands in a state violating `MemInv ["q"]`:
    `q`'s address has been deallocated underneath it. So `MemCert` could not have had a
    `free` rule for *any* post-set containing `q` — the missing rule of stage 1h was a
    genuine obstruction, not an unfinished proof. -/
theorem memInv_not_preserved_by_free :
    ∃ r : UState × Nat × List Bool,
      MemInv ["p", "q"] aliasState
    ∧ uexec 1 (.memop .free "p") (fun _ => true) aliasState = some r
    ∧ ¬ MemInv ["q"] r.1 := by
  refine ⟨_, ⟨rfl, ?_⟩, rfl, ?_⟩
  · intro _ x hx
    rcases List.mem_cons.mp hx with h | h
    · subst h; decide
    · rcases List.mem_cons.mp h with h | h
      · subst h; decide
      · simp at h
  · rintro ⟨-, hv⟩
    have := hv rfl "q" (by simp)
    revert this
    decide

/-- And `aliasState` is exactly what `SepInv` rules out, so the strengthening is
    aimed at this state and not at something incidental. -/
theorem aliasState_violates_SepInv : ¬ SepInv ["p", "q"] aliasState := by
  rintro ⟨-, hv⟩
  have := (hv rfl).2.1 "p" (by simp) "q" (by simp) (by decide)
  exact this rfl

/-! ## Witnesses, and the conservative-extension check -/

/-- Allocate, free, and the program is accepted and does not fault. -/
theorem alloc_free_ok :
    slcheck [] (.seq (.memop .alloc "p") (.memop .free "p")) = some []
  ∧ ((uexec 3 (.seq (.memop .alloc "p") (.memop .free "p")) (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some false := by decide

/-- **Use-after-free is rejected** — the pointer left the tracked set when it was
    freed, so the dereference has no rule to appeal to. -/
theorem use_after_free_rejected :
    slcheck [] (.seq (.memop .alloc "p")
                (.seq (.memop .free "p") (.memop .deref "p"))) = none := by decide

/-- And it really faults, so the rejection is not refusing something harmless. This is
    the pair that makes the guarantee non-vacuous, exactly as in stage 1h. -/
theorem use_after_free_faults :
    ((uexec 5 (.seq (.memop .alloc "p")
                (.seq (.memop .free "p") (.memop .deref "p"))) (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some true := by decide

/-- Double free is rejected too — it is the same mistake through the same rule. -/
theorem double_free_rejected_by_slcheck :
    slcheck [] (.seq (.memop .alloc "p")
                (.seq (.memop .free "p") (.memop .free "p"))) = none := by decide

/-- Freeing one of two separately allocated pointers leaves the other usable: the
    rule is not so conservative that it kills every later dereference. -/
theorem free_one_keep_other :
    slcheck [] (.seq (.memop .alloc "p")
                (.seq (.memop .alloc "q")
                 (.seq (.memop .free "p") (.memop .deref "q")))) = some ["q"]
  ∧ ((uexec 7 (.seq (.memop .alloc "p")
                (.seq (.memop .alloc "q")
                 (.seq (.memop .free "p") (.memop .deref "q")))) (fun _ => true)
        (initU (fun _ => 0))).map (fun r => r.1.err)) = some false := by decide

/-- **Conservative extension.** Everything stage 1h accepted, stage 1i accepts, with
    the same tracked set — so adding `free` regressed nothing. -/
theorem slcheck_extends_umcheck : ∀ (c : UCmd) (V V' : List String),
    umcheck V c = some V' → slcheck V c = some V'
  | .skip, _, _, h => by simpa [umcheck, slcheck] using h
  | .assign _ _, _, _, h => by simpa [umcheck, slcheck] using h
  | .check _, _, _, h => by simpa [umcheck, slcheck] using h
  | .access _, _, _, h => by simpa [umcheck, slcheck] using h
  | .memop .alloc _, _, _, h => by simpa [umcheck, slcheck] using h
  | .memop .allocS _, _, _, h => by simpa [umcheck, slcheck] using h
  | .memop .deref x, V, V', h => by
      simp only [umcheck] at h
      by_cases hx : memStr x V = true
      · rw [if_pos hx] at h
        simp only [slcheck, if_pos hx]
        exact h
      · rw [if_neg hx] at h; simp at h
  | .memop .free _, _, _, h => by simp [umcheck] at h
  | .seq c₁ c₂, V, V', h => by
      simp only [umcheck] at h
      rcases e₁ : umcheck V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        simp only [slcheck, slcheck_extends_umcheck c₁ V V₁ e₁, Option.bind_some]
        exact slcheck_extends_umcheck c₂ V₁ V' h
  | .ite e c₁ c₂, V, V', h => by
      simp only [umcheck] at h
      rcases e₁ : umcheck V c₁ with _ | V₁
      · rw [e₁] at h; simp at h
      · rcases e₂ : umcheck V c₂ with _ | V₂
        · rw [e₁, e₂] at h; simp at h
        · rw [e₁, e₂] at h
          simp only [Option.some.injEq] at h; subst h
          simp only [slcheck, slcheck_extends_umcheck c₁ V V₁ e₁,
                     slcheck_extends_umcheck c₂ V V₂ e₂]
  | .loop _ _, _, _, h => by simp [umcheck] at h

end ConfTyping
