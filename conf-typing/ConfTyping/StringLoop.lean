/-
  The composable core, stage 1r: loops for the two string certificates.

  Stage 1n's asymmetry — three of the four certificates compose over loops, the budget
  does not — was measured before there were string certificates. Stages 1o and 1q added
  two more, both with `| .loop _ _ => none`, so the honest count had slipped to three of
  six. This closes that: `tcheckW` and `pcheckW` get loop rules by exactly the narrowing
  stage 1l built for the tracked set, and the count returns to **five of six**, with the
  budget still the only law that cannot.

  Two things made this cheaper than stage 1l.

  **The emission list needs no widening.** `Ks` records *which* delimiter counts a
  program may emit — a set of possibilities, not a total — so a loop that emits the same
  query a thousand times emits counts drawn from the same `Ks`. The loop rule reuses the
  body's `Ks` unchanged. Only the environment needs a fixed point, and that is
  `interNat` iterated downwards, exactly `narrowFix` with a different meet.

  **The two certificates share the shape.** `TaintCert.loop` and `PathCert.loop` are the
  same fuel induction over the same weakening lemmas, which is the fourth and fifth time
  the Hoare-triple-with-a-tracked-set shape has appeared. That repetition is the
  evidence the shape was the right one.

  The fuel index is stage 1l's answer to the same problem for the same reason: the
  narrowing call sits under a closure, structural recursion on the command cannot see
  through it, and a well-founded definition would stop kernel-reducing and break every
  `decide`. `tcheckW_out_of_fuel` records that exhausting the fuel refuses rather than
  accepts.
-/
import ConfTyping.PathCert

namespace ConfTyping

/-! ## Weakening, for both string certificates -/

theorem TaintInv.mono {C D : TaintEnv} {s : UState} (hsub : ∀ p ∈ C, p ∈ D)
    (h : TaintInv D s) : TaintInv C s :=
  fun hd p hp => h hd p (hsub p hp)

theorem TaintCert.weakenPost {C C₁ C' : TaintEnv} {c : UCmd} {Ks : List Nat}
    (h : TaintCert C c C₁ Ks) (hsub : ∀ p ∈ C', p ∈ C₁) : TaintCert C c C' Ks :=
  ⟨fun n π s r hinv hr => TaintInv.mono hsub (h.env n π s r hinv hr), h.sink⟩

theorem TaintCert.strengthenPre {C C' D : TaintEnv} {c : UCmd} {Ks : List Nat}
    (h : TaintCert C' c D Ks) (hsub : ∀ p ∈ C', p ∈ C) : TaintCert C c D Ks :=
  ⟨fun n π s r hinv hr => h.env n π s r (TaintInv.mono hsub hinv) hr,
   fun n π s r hinv hr => h.sink n π s r (TaintInv.mono hsub hinv) hr⟩

theorem PathCert.weakenPost {fs : String} {C C₁ C' : TaintEnv} {c : UCmd}
    (h : PathCert fs C c C₁) (hsub : ∀ p ∈ C', p ∈ C₁) : PathCert fs C c C' :=
  ⟨fun n π s r hinv hr => TaintInv.mono hsub (h.env n π s r hinv hr), h.path⟩

theorem PathCert.strengthenPre {fs : String} {C C' D : TaintEnv} {c : UCmd}
    (h : PathCert fs C' c D) (hsub : ∀ p ∈ C', p ∈ C) : PathCert fs C c D :=
  ⟨fun n π s r hinv hr => h.env n π s r (TaintInv.mono hsub hinv) hr,
   fun n π s r hinv hr => h.path n π s r (TaintInv.mono hsub hinv) hr⟩

/-! ## The loop rules -/

/-- **A loop emits from the same set of counts as its body.** `Ks` is a set of
    possibilities rather than a running total, so repetition costs nothing — which is
    why only the environment needs a fixed point. -/
theorem TaintCert.loop {C C₁ : TaintEnv} {e : Expr} {c : UCmd} {Ks : List Nat}
    (h : TaintCert C c C₁ Ks) (hsub : ∀ p ∈ C, p ∈ C₁) :
    TaintCert C (.loop e c) C Ks := by
  have hb : TaintCert C c C Ks := TaintCert.weakenPost h hsub
  constructor
  · intro n
    induction n with
    | zero => intro π s r _ hr; simp [uexec] at hr
    | succ m ihm =>
        intro π s r hinv hr
        rw [uexec_loop_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at hr
          rcases e₁ : uexec m c π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁, Option.bind_some] at hr
            rcases e₂ : uexec m (.loop e c) π r₁.1 with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact ihm π r₁.1 r₂ (hb.env m π s r₁ hinv e₁) e₂
        · rw [ite_eq_right hg] at hr
          simp only [Option.some.injEq] at hr; subst hr; exact hinv
  · intro n
    induction n with
    | zero => intro π s r _ hr; simp [uexec] at hr
    | succ m ihm =>
        intro π s r hinv hr t ht
        rw [uexec_loop_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at hr
          rcases e₁ : uexec m c π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁, Option.bind_some] at hr
            rcases e₂ : uexec m (.loop e c) π r₁.1 with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              have hi₁ := hb.env m π s r₁ hinv e₁
              rcases ihm π r₁.1 r₂ hi₁ e₂ t ht with h' | h'
              · exact hb.sink m π s r₁ hinv e₁ t h'
              · exact Or.inr h'
        · rw [ite_eq_right hg] at hr
          simp only [Option.some.injEq] at hr; subst hr; exact Or.inl ht

theorem PathCert.loop {fs : String} {C C₁ : TaintEnv} {e : Expr} {c : UCmd}
    (h : PathCert fs C c C₁) (hsub : ∀ p ∈ C, p ∈ C₁) :
    PathCert fs C (.loop e c) C := by
  have hb : PathCert fs C c C := PathCert.weakenPost h hsub
  constructor
  · intro n
    induction n with
    | zero => intro π s r _ hr; simp [uexec] at hr
    | succ m ihm =>
        intro π s r hinv hr
        rw [uexec_loop_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at hr
          rcases e₁ : uexec m c π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁, Option.bind_some] at hr
            rcases e₂ : uexec m (.loop e c) π r₁.1 with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              exact ihm π r₁.1 r₂ (hb.env m π s r₁ hinv e₁) e₂
        · rw [ite_eq_right hg] at hr
          simp only [Option.some.injEq] at hr; subst hr; exact hinv
  · intro n
    induction n with
    | zero => intro π s r _ hr; simp [uexec] at hr
    | succ m ihm =>
        intro π s r hinv hr t ht
        rw [uexec_loop_eq] at hr
        by_cases hg : evalE e s.store ≠ 0
        · rw [ite_eq_left hg] at hr
          rcases e₁ : uexec m c π s with _ | r₁
          · rw [e₁] at hr; simp at hr
          · rw [e₁, Option.bind_some] at hr
            rcases e₂ : uexec m (.loop e c) π r₁.1 with _ | r₂
            · rw [e₂] at hr; simp at hr
            · rw [e₂] at hr
              simp only [Option.map_some, Option.some.injEq] at hr
              subst hr
              have hi₁ := hb.env m π s r₁ hinv e₁
              rcases ihm π r₁.1 r₂ hi₁ e₂ t ht with h' | h'
              · exact hb.path m π s r₁ hinv e₁ t h'
              · exact Or.inr h'
        · rw [ite_eq_right hg] at hr
          simp only [Option.some.injEq] at hr; subst hr; exact Or.inl ht

/-! ## Narrowing the environment -/

/-- Stage 1l's descending iteration, with `interNat` as the meet. -/
def narrowEnv (f : TaintEnv → Option TaintEnv) : Nat → TaintEnv → Option TaintEnv
  | 0,     _ => none
  | k + 1, C =>
      (f C).bind fun C₁ =>
        if interNat C C₁ == C then some C else narrowEnv f k (interNat C C₁)

theorem narrowEnv_spec {f : TaintEnv → Option TaintEnv} :
    ∀ (k : Nat) (C C' : TaintEnv), narrowEnv f k C = some C' →
      (∀ p ∈ C', p ∈ C) ∧ ∃ C₁, f C' = some C₁ ∧ ∀ p ∈ C', p ∈ C₁
  | 0,     _, _,  h => by simp [narrowEnv] at h
  | k + 1, C, C', h => by
      simp only [narrowEnv] at h
      rcases hf : f C with _ | C₁
      · rw [hf] at h; simp at h
      · rw [hf, Option.bind_some] at h
        by_cases hs : (interNat C C₁ == C) = true
        · rw [ite_eq_left hs] at h
          simp only [Option.some.injEq] at h
          subst h
          have he : interNat C C₁ = C := by simpa using hs
          exact ⟨fun _ hp => hp, C₁, hf,
                 fun p hp => interNat_right (by rw [he]; exact hp)⟩
        · rw [ite_eq_right hs] at h
          obtain ⟨hsub, hrest⟩ := narrowEnv_spec k (interNat C C₁) C' h
          exact ⟨fun p hp => interNat_left (hsub p hp), hrest⟩

/-! ## The widened checkers -/

def tcheckW : Nat → TaintEnv → UCmd → Option (TaintEnv × List Nat)
  | 0,     _, _                => none
  | _ + 1, C, .skip            => some (C, [])
  | _ + 1, C, .assign _ _      => some (C, [])
  | _ + 1, C, .check _         => some (C, [])
  | _ + 1, C, .access _        => some (C, [])
  | _ + 1, C, .memop _ _       => some (C, [])
  | _ + 1, C, .hop _ _ _       => some (C, [])
  | _ + 1, C, .sop .set x e    => match scount C e with
                                  | some k => some ((x, k) :: dropPair x C, [])
                                  | none   => some (dropPair x C, [])
  | _ + 1, C, .sop .emit _ e   => match scount C e with
                                  | some k => some (C, [k])
                                  | none   => none
  | k + 1, C, .seq c₁ c₂       => (tcheckW k C c₁).bind fun p₁ =>
                                    (tcheckW k p₁.1 c₂).map fun p₂ =>
                                      (p₂.1, p₁.2 ++ p₂.2)
  | k + 1, C, .ite _ c₁ c₂     => match tcheckW k C c₁, tcheckW k C c₂ with
                                  | some p₁, some p₂ =>
                                      some (interNat p₁.1 p₂.1, p₁.2 ++ p₂.2)
                                  | _, _ => none
  | k + 1, C, .loop _ c        =>
      match narrowEnv (fun D => (tcheckW k D c).map Prod.fst) (C.length + 1) C with
      | some C' => match tcheckW k C' c with
                   | some p => some (C', p.2)
                   | none   => none
      | none    => none

theorem tcheckW_out_of_fuel (C : TaintEnv) (c : UCmd) : tcheckW 0 C c = none := rfl

theorem tcheckW_sound : ∀ (k : Nat) (c : UCmd) (C C' : TaintEnv) (Ks : List Nat),
    tcheckW k C c = some (C', Ks) → TaintCert C c C' Ks := by
  intro k
  induction k with
  | zero => intro c C C' Ks h; simp [tcheckW] at h
  | succ k ih =>
    intro c C C' Ks h
    cases c with
    | skip =>
        simp only [tcheckW, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact TaintCert.skip
    | assign x e =>
        simp only [tcheckW, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact TaintCert.assign x e
    | check q =>
        simp only [tcheckW, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact TaintCert.check q
    | access q =>
        simp only [tcheckW, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact TaintCert.access q
    | memop op x =>
        simp only [tcheckW, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact TaintCert.memop op x
    | hop op x y =>
        simp only [tcheckW, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact TaintCert.hop op x y
    | sop op x e =>
        cases op with
        | set =>
            simp only [tcheckW] at h
            rcases hk : scount C e with _ | k'
            · rw [hk] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact TaintCert.setUnknown x e
            · rw [hk] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact TaintCert.set x e k' hk
        | emit =>
            simp only [tcheckW] at h
            rcases hk : scount C e with _ | k'
            · rw [hk] at h; simp at h
            · rw [hk] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h; exact TaintCert.emit x e k' hk
    | seq c₁ c₂ =>
        simp only [tcheckW] at h
        rcases e₁ : tcheckW k C c₁ with _ | p₁
        · rw [e₁] at h; simp at h
        · rw [e₁, Option.bind_some] at h
          rcases e₂ : tcheckW k p₁.1 c₂ with _ | p₂
          · rw [e₂] at h; simp at h
          · rw [e₂] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact TaintCert.seq (ih c₁ C p₁.1 p₁.2 (by rw [e₁]))
                                (ih c₂ p₁.1 p₂.1 p₂.2 (by rw [e₂]))
    | ite e c₁ c₂ =>
        simp only [tcheckW] at h
        rcases e₁ : tcheckW k C c₁ with _ | p₁
        · rw [e₁] at h; simp at h
        · rcases e₂ : tcheckW k C c₂ with _ | p₂
          · rw [e₁, e₂] at h; simp at h
          · rw [e₁, e₂] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact TaintCert.ite (ih c₁ C p₁.1 p₁.2 (by rw [e₁]))
                                (ih c₂ C p₂.1 p₂.2 (by rw [e₂]))
    | loop e c₀ =>
        simp only [tcheckW] at h
        rcases hn : narrowEnv (fun D => (tcheckW k D c₀).map Prod.fst) (C.length + 1) C
          with _ | D
        · rw [hn] at h; simp at h
        · simp only [hn] at h
          rcases hb : tcheckW k D c₀ with _ | p
          · rw [hb] at h; simp at h
          · rw [hb] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hsub, C₁, hmap, hDC₁⟩ := narrowEnv_spec (C.length + 1) C D hn
            rw [hb] at hmap
            simp only [Option.map_some, Option.some.injEq] at hmap
            subst hmap
            exact TaintCert.strengthenPre
              (TaintCert.loop (ih c₀ D p.1 p.2 hb) hDC₁) hsub

def pcheckW (fs : String) : Nat → TaintEnv → UCmd → Option TaintEnv
  | 0,     _, _                => none
  | _ + 1, C, .skip            => some C
  | _ + 1, C, .assign _ _      => some C
  | _ + 1, C, .check _         => some C
  | _ + 1, C, .access _        => some C
  | _ + 1, C, .memop _ _       => some C
  | _ + 1, C, .hop _ _ _       => some C
  | _ + 1, C, .sop .set x e    => match scount C e with
                                  | some k => some ((x, k) :: dropPair x C)
                                  | none   => some (dropPair x C)
  | _ + 1, C, .sop .emit q e   => if q == fs then
                                    match spath C 0 e with
                                    | some _ => some C
                                    | none   => none
                                  else some C
  | k + 1, C, .seq c₁ c₂       => (pcheckW fs k C c₁).bind fun C₁ => pcheckW fs k C₁ c₂
  | k + 1, C, .ite _ c₁ c₂     => match pcheckW fs k C c₁, pcheckW fs k C c₂ with
                                  | some C₁, some C₂ => some (interNat C₁ C₂)
                                  | _, _ => none
  | k + 1, C, .loop _ c        => narrowEnv (fun D => pcheckW fs k D c) (C.length + 1) C

theorem pcheckW_sound (fs : String) : ∀ (k : Nat) (c : UCmd) (C C' : TaintEnv),
    pcheckW fs k C c = some C' → PathCert fs C c C' := by
  intro k
  induction k with
  | zero => intro c C C' h; simp [pcheckW] at h
  | succ k ih =>
    intro c C C' h
    cases c with
    | skip => simp only [pcheckW, Option.some.injEq] at h; subst h; exact PathCert.skip
    | assign x e =>
        simp only [pcheckW, Option.some.injEq] at h; subst h; exact PathCert.assign x e
    | check q =>
        simp only [pcheckW, Option.some.injEq] at h; subst h; exact PathCert.check q
    | access q =>
        simp only [pcheckW, Option.some.injEq] at h; subst h; exact PathCert.access q
    | memop op x =>
        simp only [pcheckW, Option.some.injEq] at h; subst h; exact PathCert.memop op x
    | hop op x y =>
        simp only [pcheckW, Option.some.injEq] at h; subst h; exact PathCert.hop op x y
    | sop op x e =>
        cases op with
        | set =>
            simp only [pcheckW] at h
            rcases hk : scount C e with _ | k'
            · rw [hk] at h
              simp only [Option.some.injEq] at h; subst h
              exact PathCert.setUnknown x e
            · rw [hk] at h
              simp only [Option.some.injEq] at h; subst h
              exact PathCert.set x e k' hk
        | emit =>
            simp only [pcheckW] at h
            by_cases hq : (x == fs) = true
            · rw [ite_eq_left hq] at h
              rcases hd : spath C 0 e with _ | d
              · rw [hd] at h; simp at h
              · rw [hd] at h
                simp only [Option.some.injEq] at h; subst h
                exact PathCert.emit x e d hd
            · rw [ite_eq_right hq] at h
              simp only [Option.some.injEq] at h; subst h
              exact PathCert.emitElsewhere x e (by simpa using hq)
    | seq c₁ c₂ =>
        simp only [pcheckW] at h
        rcases e₁ : pcheckW fs k C c₁ with _ | C₁
        · rw [e₁] at h; simp at h
        · rw [e₁, Option.bind_some] at h
          exact PathCert.seq (ih c₁ C C₁ e₁) (ih c₂ C₁ C' h)
    | ite e c₁ c₂ =>
        simp only [pcheckW] at h
        rcases e₁ : pcheckW fs k C c₁ with _ | C₁
        · rw [e₁] at h; simp at h
        · rcases e₂ : pcheckW fs k C c₂ with _ | C₂
          · rw [e₁, e₂] at h; simp at h
          · rw [e₁, e₂] at h
            simp only [Option.some.injEq] at h; subst h
            exact PathCert.ite (ih c₁ C C₁ e₁) (ih c₂ C C₂ e₂)
    | loop e c₀ =>
        simp only [pcheckW] at h
        obtain ⟨hsub, C₁, hbody, hDC₁⟩ := narrowEnv_spec (C.length + 1) C C' h
        exact PathCert.strengthenPre (PathCert.loop (ih c₀ C' C₁ hbody) hDC₁) hsub

/-! ## The guarantees, now over loops -/

theorem tcheckW_no_injection {k : Nat} {c : UCmd} {C' : TaintEnv} {Ks : List Nat}
    (h : tcheckW k [] c = some (C', Ks)) :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n c π s = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ Ks := by
  intro n π s r hs hr t ht
  have hinv : TaintInv [] s := by intro _ p hp; simp at hp
  rcases (tcheckW_sound k c [] C' Ks h).sink n π s r hinv hr t ht with h' | h'
  · rw [hs] at h'; simp at h'
  · exact h'

theorem pcheckW_no_escape {fs : String} {k : Nat} {c : UCmd} {C' : TaintEnv}
    (h : pcheckW fs k [] c = some C') :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n c π s = some r →
      ∀ p ∈ r.1.sink, p.1 = fs → safePath p.2 = true := by
  intro n π s r hs hr p hp hfs
  have hinv : TaintInv [] s := by intro _ q hq; simp at hq
  rcases (pcheckW_sound fs k c [] C' h).path n π s r hinv hr p hp with h' | h'
  · rw [hs] at h'; simp at h'
  · exact h' hfs

/-! ## A server loop -/

/-- Build a sanitised query once, then serve it repeatedly. The emission happens inside
    the loop, so the guarantee has to survive an unbounded number of emissions. -/
def loopQuery : UCmd :=
  .seq (.sop .set "q" (.cat (.lit [.ord, .quote])
                        (.cat (.san (.var "input")) (.lit [.quote]))))
       (.loop (.var "n") (.seq (.sop .emit "db" (.var "q")) (.assign "n" (.num 0))))

theorem loopQuery_checks : tcheckW 8 [] loopQuery = some ([("q", 2)], [2]) := by decide

/-- Stage 1o's checker could not do this at all. -/
theorem loopQuery_needed_the_widening : tcheck [] loopQuery = none := by decide

/-- **However many times round the loop, every emitted query has two delimiters.** -/
theorem loopQuery_safe :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n loopQuery π s = some r →
      ∀ t ∈ r.1.sink, qcount t.2 = 2 := by
  intro n π s r hs hr t ht
  have := tcheckW_no_injection loopQuery_checks n π s r hs hr t ht
  simpa using this

/-- The same for a file server: serve paths inside the root, in a loop. -/
def loopServe : UCmd :=
  .seq (.sop .set "p" (.cat (.lit [.ord]) (.san (.var "input"))))
       (.loop (.var "n") (.seq (.sop .emit "fs" (.var "p")) (.assign "n" (.num 0))))

theorem loopServe_checks : pcheckW "fs" 8 [] loopServe = some [("p", 0)] := by decide

theorem loopServe_safe :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      s.sink = [] → uexec n loopServe π s = some r →
      ∀ p ∈ r.1.sink, p.1 = "fs" → safePath p.2 = true :=
  pcheckW_no_escape loopServe_checks

/-! ## The count, corrected

    Stage 1n measured "three of four compose over loops" before there were string
    certificates; stages 1o and 1q then added two that did not, quietly making it three
    of six. It is now **five of six**, and the budget is still the only law that cannot
    — for the reason stage 1n gave, which no amount of narrowing addresses: a cost bound
    over a loop needs an *iteration* bound, and that is a termination argument. -/

/-- Five of the six compose over loops; the budget is the exception, still. -/
theorem five_of_six_compose_over_loops :
    (∀ (P : Partition) (V : List String) (e : Expr) (c : UCmd), exprLow P e = true →
        JSecTy P V c V → JSecTy P V (.loop e c) V)
  ∧ (∀ (V : List String) (e : Expr) (c : UCmd), SepCert V c V → SepCert V (.loop e c) V)
  ∧ (∀ (C C₁ : TaintEnv) (e : Expr) (c : UCmd) (Ks : List Nat), TaintCert C c C₁ Ks →
        (∀ p ∈ C, p ∈ C₁) → TaintCert C (.loop e c) C Ks)
  ∧ (∀ (fs : String) (C C₁ : TaintEnv) (e : Expr) (c : UCmd), PathCert fs C c C₁ →
        (∀ p ∈ C, p ∈ C₁) → PathCert fs C (.loop e c) C)
  ∧ (∀ (P : Partition) (A V : List String) (e : Expr) (c : UCmd),
        allcheck P A V (.loop e c) = none) :=
  ⟨fun _ _ e _ hg hc => .whileW e hg (fun _ hx => hx) hc (fun _ hx => hx),
   fun _ _ _ h => SepCert.loop h,
   fun _ _ _ _ _ h hs => TaintCert.loop h hs,
   fun _ _ _ _ _ h hs => PathCert.loop h hs,
   fun _ _ _ _ _ => rfl⟩

end ConfTyping
