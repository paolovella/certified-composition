/-
  The composable core, stage 2j: the counted loop, natively.

  The standing summary of this core is "five of six laws compose over loops; the budget
  cannot" (`only_the_budget_lacks_a_loop_rule`), and it is true: a cost bound over a loop
  needs an *iteration* bound, brick 34's `dos_unbounded` proves no uniform one exists in
  general, and so `allcheck` returns `none` at every `.loop`.

  Stage 1f found one way past it — `UCert.ofEmbedded` gives a budget to a loop whose body
  is a **pure store program embedded wholesale** from the `While` development. That is why
  `handlerBounded`'s loop body is `.skip`: an embedded `WCmd` has no heap, no strings, no
  `check` and no `access`, so the certified loop cannot touch memory, cannot be mediated,
  and cannot emit. Every fully-certified program in this repo is therefore straight-line.

  This stage supplies the missing ingredient natively. `forU i k body` is the counted loop
  — initialise a counter from a constant, run the body, decrement, repeat — with `body` an
  arbitrary `UCmd`.
-/
import ConfTyping.SpecFused

namespace ConfTyping

/-! ## The counter must survive the body -/

/-- `c` never writes the store variable `x`. Conservative at `memop`: only `alloc` and
    `allocS` write their target, but `deref` and `free` naming the counter would be
    nonsense anyway, and one uniform condition is cheaper to check and to read. -/
def noWrite (x : String) : UCmd → Bool
  | .skip           => true
  | .assign y _     => y != x
  | .check _        => true
  | .access _       => true
  | .memop _ y      => y != x
  | .sop _ _ _      => true
  | .hop .load d _  => d != x
  | .hop .store _ _ => true
  | .seq a b        => noWrite x a && noWrite x b
  | .ite _ a b      => noWrite x a && noWrite x b
  | .loop _ a       => noWrite x a

/-- **A command that never writes `x` leaves `x` alone** — whatever it does to the heap,
    the string store, the authorization set or the liveness bit. -/
theorem noWrite_preserves : ∀ (n : Nat) (x : String) (c : UCmd) (π : MedPolicy)
    (s : UState) (r : UState × Nat × List Bool),
    noWrite x c = true → uexec n c π s = some r → r.1.store x = s.store x
  | 0,     _, _, _, _, _, _,   h => by simp [uexec] at h
  | n + 1, x, c, π, s, r, hnw, h => by
      cases c with
      | skip => simp only [uexec, Option.some.injEq] at h; subst h; rfl
      | check q =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true
          · simp [hd]
          · simp only [if_neg hd]; split <;> rfl
      | access q =>
          simp only [uexec, Option.some.injEq] at h; subst h
          by_cases hd : s.dead = true <;> simp [hd]
      | assign y e =>
          simp only [uexec, Option.some.injEq] at h; subst h
          have hxy : ¬ (x = y) := by
            simp only [noWrite, bne_iff_ne, ne_eq] at hnw
            exact fun hh => hnw hh.symm
          by_cases hd : s.dead = true
          · simp [hd]
          · simp only [if_neg hd]; show upd s.store y _ x = s.store x
            simp [upd, hxy]
      | sop op y e =>
          cases op
          case set =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]
          case emit =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]
      | memop op y =>
          have hxy : ¬ (x = y) := by
            simp only [noWrite, bne_iff_ne, ne_eq] at hnw
            exact fun hh => hnw hh.symm
          cases op
          case alloc =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]
              show upd s.store y (pickAddr s.freed s.fresh) x = s.store x
              simp [upd, hxy]
          case allocS =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]
              show upd s.store y (pickAddr s.freed s.fresh) x = s.store x
              simp [upd, hxy]
          case deref =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]; split <;> rfl
          case free =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]; split <;> rfl
      | hop op d y =>
          cases op
          case load =>
            have hxd : ¬ (x = d) := by
              simp only [noWrite, bne_iff_ne, ne_eq] at hnw
              exact fun hh => hnw hh.symm
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]
              split
              · show upd s.store d (s.heap (s.store y)) x = s.store x
                simp [upd, hxd]
              · rfl
          case store =>
            simp only [uexec, Option.some.injEq] at h; subst h
            by_cases hd : s.dead = true
            · simp [hd]
            · simp only [if_neg hd]; split <;> rfl
      | seq c₁ c₂ =>
          simp only [noWrite, Bool.and_eq_true] at hnw
          rw [uexec_seq_eq] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          rw [e₁, Option.bind_some] at h
          rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
          · rw [e₂] at h; simp at h
          rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
          rw [← h]
          show r₂.1.store x = s.store x
          rw [noWrite_preserves n x c₂ π r₁.1 r₂ hnw.2 e₂,
              noWrite_preserves n x c₁ π s r₁ hnw.1 e₁]
      | ite e c₁ c₂ =>
          simp only [noWrite, Bool.and_eq_true] at hnw
          rw [uexec_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg] at h
            rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]; exact noWrite_preserves n x c₁ π s r₁ hnw.1 e₁
          · rw [if_neg hg] at h
            rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]; exact noWrite_preserves n x c₂ π s r₂ hnw.2 e₂
      | loop e c₀ =>
          simp only [noWrite] at hnw
          rw [uexec_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg] at h
            rcases e₁ : uexec n c₀ π s with _ | r₁
            · rw [e₁] at h; simp at h
            rw [e₁, Option.bind_some] at h
            rcases e₂ : uexec n (.loop e c₀) π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]
            show r₂.1.store x = s.store x
            rw [noWrite_preserves n x (.loop e c₀) π r₁.1 r₂ (by simp [noWrite, hnw]) e₂,
                noWrite_preserves n x c₀ π s r₁ hnw e₁]
          · rw [if_neg hg] at h
            simp only [Option.some.injEq] at h; rw [← h]

/-! ## The counted loop -/

/-- Decrement by one. `Expr` has no subtraction, so this is `+ (-1)`. -/
def decOne (i : String) : UCmd := .assign i (.add (.var i) (.num (-1)))

/-- Run the body, decrement the counter, repeat while the counter is nonzero. -/
def countU (i : String) (body : UCmd) : UCmd := .loop (.var i) (.seq body (decOne i))

/-- **The counted loop**: initialise the counter from a *constant*, then count down.
    Stage 1f's `budget` on `WCmd`, with a native `UCmd` body. -/
def forU (i : String) (k : Nat) (body : UCmd) : UCmd :=
  .seq (.assign i (.num (k : Int))) (countU i body)

/-- **One turn.** The body costs what it costs plus the decrement, and afterwards either
    the counter really went down by one, or the machine died — in which case the counter
    did *not* move, because a dead machine's assignment is a no-op. That second disjunct
    is the whole difference between this and stage 1f's embedded loop, whose `WCmd` body
    has no way to die. -/
theorem countU_turn {i : String} {body : UCmd} {b : Nat}
    (hnw : noWrite i body = true)
    (hb : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
            uexec n body π s = some r → r.2.1 ≤ b)
    (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool)
    (h : uexec n (.seq body (decOne i)) π s = some r) :
    r.2.1 ≤ b + 1
      ∧ (r.1.store i = s.store i - 1 ∨ (r.1.dead = true ∧ r.1.store i = s.store i)) := by
  cases n with
  | zero => simp [uexec] at h
  | succ m =>
      rw [uexec_seq_eq] at h
      rcases e₁ : uexec m body π s with _ | r₁
      · rw [e₁] at h; simp at h
      rw [e₁, Option.bind_some] at h
      rcases e₂ : uexec m (decOne i) π r₁.1 with _ | r₂
      · rw [e₂] at h; simp at h
      rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
      have hcost := hb m π s r₁ e₁
      have hkeep : r₁.1.store i = s.store i := noWrite_preserves m i body π s r₁ hnw e₁
      cases m with
      | zero => simp [uexec] at e₂
      | succ m' =>
          simp only [decOne, uexec, Option.some.injEq] at e₂
          rw [← h]
          by_cases hd : r₁.1.dead = true
          · rw [← e₂]
            refine ⟨by show r₁.2.1 + 1 ≤ b + 1; omega, Or.inr ⟨by simp [hd], ?_⟩⟩
            show (if r₁.1.dead then r₁.1 else _).store i = s.store i
            rw [if_pos hd]; exact hkeep
          · rw [← e₂]
            refine ⟨by show r₁.2.1 + 1 ≤ b + 1; omega, Or.inl ?_⟩
            show (if r₁.1.dead then r₁.1 else _).store i = s.store i - 1
            rw [if_neg hd]
            show upd r₁.1.store i (evalE (.add (.var i) (.num (-1))) r₁.1.store) i
                   = s.store i - 1
            simp only [upd, evalE, hkeep, if_true, reduceIte]
            omega

/-- **The cost of a counted loop, natively.** The counter's value bounds the iterations,
    each costing at most `b + 2`, and the guard test at the end costs one.

    The proof has a case stage 1f's does not: if the machine dies inside the body, the
    decrement is a no-op, the guard is still true, and `uexec_dead_loop_diverges` says the
    loop then runs forever. So a *halting* run of a counted loop never dies — which is
    what makes the bound provable, and is recorded separately as
    `a_dead_counted_loop_does_not_halt`. -/
theorem countU_cost {i : String} {body : UCmd} {b : Nat}
    (hnw : noWrite i body = true)
    (hb : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
            uexec n body π s = some r → r.2.1 ≤ b) :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      0 ≤ s.store i → uexec n (countU i body) π s = some r →
      r.2.1 ≤ 1 + (s.store i).toNat * (b + 2)
  | 0,     _, _, _, _,    h => by simp [uexec] at h
  | n + 1, π, s, r, hpos, h => by
      rw [countU, uexec_loop_eq] at h
      by_cases hg : evalE (.var i) s.store ≠ 0
      · rw [if_pos hg] at h
        have hgi : s.store i ≠ 0 := by simpa [evalE] using hg
        rcases e₁ : uexec n (.seq body (decOne i)) π s with _ | r₁
        · rw [e₁] at h; simp at h
        rw [e₁, Option.bind_some] at h
        rcases e₂ : uexec n (countU i body) π r₁.1 with _ | r₂
        · rw [countU] at e₂; rw [e₂] at h; simp at h
        rw [countU] at e₂
        rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hcost, hstep⟩ := countU_turn hnw hb n π s r₁ e₁
        rcases hstep with hdec | ⟨hdead, hsame⟩
        · -- the live case: the counter really went down
          have hpos1 : 0 ≤ r₁.1.store i := by rw [hdec]; omega
          have hih := countU_cost hnw hb n π r₁.1 r₂ hpos1 e₂
          have hstep2 : (s.store i).toNat = (r₁.1.store i).toNat + 1 := by
            rw [hdec]; omega
          have hmul : (s.store i).toNat * (b + 2)
              = (r₁.1.store i).toNat * (b + 2) + (b + 2) := by
            rw [hstep2, Nat.succ_mul]
          rw [← h]
          show 1 + r₁.2.1 + r₂.2.1 ≤ 1 + (s.store i).toNat * (b + 2)
          rw [hmul]; omega
        · -- the dead case: the loop cannot have halted at all
          exfalso
          have hg1 : evalE (.var i) r₁.1.store ≠ 0 := by
            show r₁.1.store i ≠ 0
            rw [hsame]; exact hgi
          rw [uexec_dead_loop_diverges n (.var i) (.seq body (decOne i)) π r₁.1
                hdead hg1] at e₂
          cases e₂
      · rw [if_neg hg] at h
        simp only [Option.some.injEq] at h
        rw [← h]; exact Nat.le_add_right 1 _

/-! ## The mediation half -/

/-- Weakening the authorization set: `UMedInv` demands that everything in `A` has been
    authorized, so a *smaller* `A` is a weaker demand. -/
theorem UMedInv.mono {π : MedPolicy} {A A' : List String} {s : UState}
    (hsub : ∀ r ∈ A, r ∈ A') (h : UMedInv π A' s) : UMedInv π A s :=
  ⟨h.1, h.2.1, fun hd r hr => h.2.2 hd r (hsub r hr)⟩

/-- The authorization set survives the loop.

    **Widened (stage 2k).** The body need not return `A` on the nose — it need only *grow*
    it, which is what a `check` inside the loop does. The loop's post-condition stays `A`,
    because at zero iterations the body never runs; that is the same shape as `JSecTy`'s
    `whileW`, one component over. Corpus program 17 — a retry loop that re-authorizes —
    is what forced this, and it was a false rejection, not a soundness question. -/
theorem countU_auth {i : String} {A A' : List String} {body : UCmd} {b : Nat}
    (hsub : ∀ r ∈ A, r ∈ A') (hcert : UCert A body A' b) :
    ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
      UMedInv π A s → uexec n (countU i body) π s = some r → UMedInv π A r.1
  | 0,     _, _, _, _,    h => by simp [uexec] at h
  | n + 1, π, s, r, hinv, h => by
      rw [countU, uexec_loop_eq] at h
      by_cases hg : evalE (.var i) s.store ≠ 0
      · rw [if_pos hg] at h
        rcases e₁ : uexec n (.seq body (decOne i)) π s with _ | r₁
        · rw [e₁] at h; simp at h
        rw [e₁, Option.bind_some] at h
        rcases e₂ : uexec n (countU i body) π r₁.1 with _ | r₂
        · rw [countU] at e₂; rw [e₂] at h; simp at h
        rw [countU] at e₂
        rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
        have hturn : UMedInv π A r₁.1 := by
          cases n with
          | zero => simp [uexec] at e₁
          | succ m =>
              rw [uexec_seq_eq] at e₁
              rcases f₁ : uexec m body π s with _ | q₁
              · rw [f₁] at e₁; simp at e₁
              rw [f₁, Option.bind_some] at e₁
              rcases f₂ : uexec m (decOne i) π q₁.1 with _ | q₂
              · rw [f₂] at e₁; simp at e₁
              rw [f₂] at e₁; simp only [Option.map_some, Option.some.injEq] at e₁
              rw [← e₁]
              exact UMedInv.mono hsub
                ((UCert.assign (A := A') i (.add (.var i) (.num (-1)))).auth m π q₁.1 q₂
                  (hcert.auth m π s q₁ hinv f₁) f₂)
        rw [← h]
        exact countU_auth hsub hcert n π r₁.1 r₂ hturn e₂
      · rw [if_neg hg] at h
        simp only [Option.some.injEq] at h
        rw [← h]; exact hinv

/-! ## The certificate -/

/-- **The counted loop carries the bundle.** Budget `2 + k·(b+2)`: one step to initialise,
    one to test the guard a final time, and `k` turns of the body plus its decrement.

    This is the rule `only_the_budget_lacks_a_loop_rule` says cannot exist for a *general*
    loop — and does not: the iteration bound is supplied syntactically by the constant the
    counter is initialised from, which is the "analysis of a different kind" that theorem
    names. What is new here is that `body` is an arbitrary `UCmd`. -/
theorem UCert.forU {A A' : List String} {i : String} {k : Nat} {body : UCmd} {b : Nat}
    (hnw : noWrite i body = true) (hsub : ∀ r ∈ A, r ∈ A')
    (hcert : UCert A body A' b) :
    UCert A (forU i k body) A (2 + k * (b + 2)) := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ m =>
        rw [ConfTyping.forU, uexec_seq_eq] at hr
        rcases e₁ : uexec m (.assign i (.num (k : Int))) π s with _ | r₁
        · rw [e₁] at hr; simp at hr
        rw [e₁, Option.bind_some] at hr
        rcases e₂ : uexec m (countU i body) π r₁.1 with _ | r₂
        · rw [e₂] at hr; simp at hr
        rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
        have hc1 : r₁.2.1 = 1 := by
          cases m with
          | zero => simp [uexec] at e₁
          | succ m' => simp only [uexec, Option.some.injEq] at e₁; rw [← e₁]
        rw [← hr]
        show r₁.2.1 + r₂.2.1 ≤ 2 + k * (b + 2)
        by_cases hd : s.dead = true
        · -- a dead machine never reaches the loop body: it exits at the guard or hangs
          have hs1 : r₁.1 = s := uexec_dead_unchanged m _ π s r₁ hd e₁
          have hd1 : r₁.1.dead = true := by rw [hs1]; exact hd
          have hc2 : r₂.2.1 = 1 := by
            cases m with
            | zero => simp [uexec] at e₂
            | succ m' =>
                rw [countU] at e₂
                by_cases hg : evalE (.var i) r₁.1.store ≠ 0
                · rw [uexec_dead_loop_diverges (m' + 1) (.var i) (.seq body (decOne i))
                        π r₁.1 hd1 hg] at e₂
                  cases e₂
                · rw [uexec_loop_eq, if_neg hg] at e₂
                  simp only [Option.some.injEq] at e₂; rw [← e₂]
          rw [hc1, hc2]; omega
        · have hd0 : s.dead = false := by simpa using hd
          have hi : r₁.1.store i = (k : Int) := by
            cases m with
            | zero => simp [uexec] at e₁
            | succ m' =>
                simp only [uexec, Option.some.injEq] at e₁
                rw [← e₁]
                show (if s.dead then s else _).store i = (k : Int)
                rw [if_neg hd]
                show upd s.store i (evalE (.num (k : Int)) s.store) i = (k : Int)
                simp [upd, evalE]
          have hpos : 0 ≤ r₁.1.store i := by rw [hi]; exact Int.ofNat_nonneg k
          have hloop := countU_cost hnw hcert.budget m π r₁.1 r₂ hpos e₂
          rw [hi] at hloop
          simp only [Int.toNat_natCast] at hloop
          rw [hc1]; omega
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ m =>
        rw [ConfTyping.forU, uexec_seq_eq] at hr
        rcases e₁ : uexec m (.assign i (.num (k : Int))) π s with _ | r₁
        · rw [e₁] at hr; simp at hr
        rw [e₁, Option.bind_some] at hr
        rcases e₂ : uexec m (countU i body) π r₁.1 with _ | r₂
        · rw [e₂] at hr; simp at hr
        rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
        rw [← hr]
        exact countU_auth hsub hcert m π r₁.1 r₂
          ((UCert.assign (A := A) i (.num (k : Int))).auth m π s r₁ hinv e₁) e₂

/-! ## The flow and memory halves -/

theorem dropStr_idem (x : String) : ∀ (V : List String), dropStr x (dropStr x V) = dropStr x V
  | []      => rfl
  | y :: ys => by
      by_cases h : (y == x) = true
      · rw [dropStr, if_pos h, dropStr_idem x ys]
      · rw [dropStr, if_neg h, dropStr, if_neg h, dropStr_idem x ys]

/-- **The counted loop is typable by the joint judgment**, so it carries noninterference
    and memory safety too. The counter must be Low — a loop whose *length* is secret is
    refused, which is stage 1b's timing channel doing its job at the iteration level. -/
theorem JSecTy.forU {P : Partition} {V : List String} {i : String} {k : Nat} {body : UCmd}
    (hi : P i = false)
    (hbody : JSecTy P (dropStr i V) body (dropStr i V)) :
    JSecTy P V (forU i k body) (dropStr i V) := by
  have hlowi : exprLow P (.var i) = true := by simp [exprLow, hi]
  have hdec : JSecTy P (dropStr i V) (decOne i) (dropStr i V) := by
    have := JSecTy.assignL (P := P) (dropStr i V) i (.add (.var i) (.num (-1)))
      (by simp [exprLow, hi])
    rwa [dropStr_idem] at this
  exact .seq (.assignL V i (.num (k : Int)) (by simp [exprLow]))
    (.whileW (.var i) hlowi (fun _ hx => hx) (.seq hbody hdec) (fun _ hx => hx))

/-! ## Recognizing the idiom -/

/-- Is every name in `A` also in `B`? -/
def subStr (A B : List String) : Bool := A.all (fun r => memStr r B)

theorem subStr_mem {A B : List String} (h : subStr A B = true) : ∀ r ∈ A, r ∈ B := by
  intro r hr
  exact memStr_mem (List.all_eq_true.mp h r hr)


/-- The counted loop, as a *pattern*. A checker sees raw syntax, so the iteration bound
    has to be read off it: a constant-initialised counter, a guard that tests it, and a
    body ending in the decrement. -/
def asFor : UCmd → Option (String × Nat × UCmd)
  | .seq (.assign i (.num k))
      (.loop (.var j) (.seq body (.assign j' (.add (.var j'') (.num m))))) =>
      if i == j && i == j' && i == j'' && m == -1 && 0 ≤ k then
        some (i, k.toNat, body)
      else none
  | _ => none

/-- What the pattern recognises really is a counted loop. -/
theorem asFor_eq : ∀ {c : UCmd} {i : String} {k : Nat} {body : UCmd},
    asFor c = some (i, k, body) → c = forU i k body := by
  intro c i k body h
  match c with
  | .seq (.assign i₀ (.num k₀))
      (.loop (.var j) (.seq body₀ (.assign j' (.add (.var j'') (.num m))))) =>
      simp only [asFor] at h
      split at h
      · rename_i hcond
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨⟨hij, hij'⟩, hij''⟩, hm⟩, hk0⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hi, hk, hb⟩ := h
        subst hi; subst hk; subst hb
        subst hij; subst hij'; subst hij''; subst hm
        show _ = ConfTyping.forU _ _ _
        rw [ConfTyping.forU, countU, decOne, Int.toNat_of_nonneg hk0]
      · cases h
  | .skip | .assign _ _ | .check _ | .access _ | .memop _ _ | .sop _ _ _ | .hop _ _ _
  | .ite _ _ _ | .loop _ _ => simp [asFor] at h
  | .seq .skip _ | .seq (.assign _ (.var _)) _ | .seq (.assign _ (.add _ _)) _
  | .seq (.check _) _ | .seq (.access _) _ | .seq (.memop _ _) _ | .seq (.sop _ _ _) _
  | .seq (.hop _ _ _) _ | .seq (.seq _ _) _ | .seq (.ite _ _ _) _
  | .seq (.loop _ _) _ => simp [asFor] at h
  | .seq (.assign _ (.num _)) .skip | .seq (.assign _ (.num _)) (.assign _ _)
  | .seq (.assign _ (.num _)) (.check _) | .seq (.assign _ (.num _)) (.access _)
  | .seq (.assign _ (.num _)) (.memop _ _) | .seq (.assign _ (.num _)) (.sop _ _ _)
  | .seq (.assign _ (.num _)) (.hop _ _ _) | .seq (.assign _ (.num _)) (.seq _ _)
  | .seq (.assign _ (.num _)) (.ite _ _ _) => simp [asFor] at h

/-! ## One checker, loops included -/

/-- `allcheck`, plus the counted-loop rule. Everything that is not a `seq` or an `ite`
    goes straight to `allcheck`, so every earlier result applies verbatim; the new content
    is one clause. The loop body is checked by `allcheck`, so it may not itself contain a
    loop — nesting is a follow-on, not a claim. -/
def bcheck (P : Partition) :
    List String → List String → UCmd → Option (List String × List String × Nat)
  | A, V, .seq c₁ c₂ =>
      match asFor (.seq c₁ c₂) with
      | some (i, k, body) =>
          if !(P i) && noWrite i body then
            match allcheck P A (dropStr i V) body with
            | some (A₂, V₂, b) =>
                if subStr A A₂ && V₂ == dropStr i V then
                  some (A, dropStr i V, 2 + k * (b + 2))
                else none
            | none => none
          else none
      | none =>
          (bcheck P A V c₁).bind fun p₁ =>
            (bcheck P p₁.1 p₁.2.1 c₂).map fun p₂ =>
              (p₂.1, p₂.2.1, p₁.2.2 + p₂.2.2)
  | A, V, .ite e c₁ c₂ =>
      if exprLow P e then
        match bcheck P A V c₁, bcheck P A V c₂ with
        | some p₁, some p₂ =>
            some (interStr p₁.1 p₂.1, interStr p₁.2.1 p₂.2.1, 1 + max p₁.2.2 p₂.2.2)
        | _, _ => none
      else none
  | A, V, c => allcheck P A V c

/-- **The checker is sound, loops included.** One run, and the result is the same
    `FullCert` every earlier stage consumes — so the budget, mediation, noninterference
    and memory-safety guarantees attach to a program that iterates. -/
theorem bcheck_sound {P : Partition} : ∀ (c : UCmd) (A V A' V' : List String) (k : Nat),
    bcheck P A V c = some (A', V', k) → FullCert P A V c A' V' k := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
      intro A V A' V' k h
      rcases hf : asFor (.seq c₁ c₂) with _ | ⟨i, k₀, body⟩
      · simp only [bcheck, hf] at h
        rcases e₁ : bcheck P A V c₁ with _ | p₁
        · rw [e₁] at h; simp at h
        rw [e₁, Option.bind_some] at h
        rcases e₂ : bcheck P p₁.1 p₁.2.1 c₂ with _ | p₂
        · rw [e₂] at h; simp at h
        rw [e₂] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        have f₁ := ih₁ A V p₁.1 p₁.2.1 p₁.2.2 (by rw [e₁])
        have f₂ := ih₂ p₁.1 p₁.2.1 p₂.1 p₂.2.1 p₂.2.2 (by rw [e₂])
        obtain ⟨hA, hV, hk⟩ := h
        subst hA; subst hV; subst hk
        exact ⟨UCert.seq f₁.bundle f₂.bundle, .seq f₁.joint f₂.joint⟩
      · rw [asFor_eq hf]
        simp only [bcheck, hf] at h
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          rcases eb : allcheck P A (dropStr i V) body with _ | q
          · rw [eb] at h; simp at h
          rw [eb] at h
          split at h
          · rename_i _ A₂ V₂ b hfix
            simp only [Option.some.injEq] at hfix
            subst hfix
            split at h
            · rename_i hfix2
              simp only [Bool.and_eq_true, beq_iff_eq] at hfix2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hA, hV, hk⟩ := h
              subst hA; subst hV; subst hk
              have hq : allcheck P A (dropStr i V) body = some (A₂, dropStr i V, b) := by
                rw [eb, hfix2.2]
              have hbody := allcheck_sound body A (dropStr i V) A₂ (dropStr i V) b hq
              exact ⟨UCert.forU hcond.2 (subStr_mem hfix2.1) hbody.bundle,
                     JSecTy.forU (by simpa using hcond.1) hbody.joint⟩
            · cases h
          · cases h
        · cases h
  | ite e c₁ c₂ ih₁ ih₂ =>
      intro A V A' V' k h
      simp only [bcheck] at h
      split at h
      · rename_i he
        rcases e₁ : bcheck P A V c₁ with _ | p₁
        · rw [e₁] at h; simp at h
        rcases e₂ : bcheck P A V c₂ with _ | p₂
        · rw [e₁, e₂] at h; simp at h
        rw [e₁, e₂] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hA, hV, hk⟩ := h
        subst hA; subst hV; subst hk
        have f₁ := ih₁ A V p₁.1 p₁.2.1 p₁.2.2 (by rw [e₁])
        have f₂ := ih₂ A V p₂.1 p₂.2.1 p₂.2.2 (by rw [e₂])
        exact ⟨UCert.ite f₁.bundle f₂.bundle, .iteL e he f₁.joint f₂.joint⟩
      · cases h
  | skip => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | assign _ _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | check _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | access _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | memop _ _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | sop _ _ _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | hop _ _ _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h
  | loop _ _ => intro A V A' V' k h; exact allcheck_sound _ _ _ _ _ _ h

/-! ## A program that iterates -/

/-- The loop body: a mediated read, a scratch allocation, a heap write, a sanitized
    query emitted, and the allocation released. Every one of these is impossible in
    stage 1f's embedded loop, whose body is a `WCmd`. -/
def loopBody : UCmd :=
  .seq (.access "db")
    (.seq (.memop .alloc "t")
      (.seq (.hop .store "t" "z")
        (.seq (.sop .emit "db"
                (.cat (.lit [.ord, .quote]) (.cat (.san (.var "input")) (.lit [.quote]))))
          (.memop .free "t"))))

/-- Authorize, allocate, do bounded work in a loop, release. -/
def loopHandler : UCmd :=
  .seq (.check "db")
    (.seq (.memop .alloc "buf")
      (.seq (forU "n" 5 loopBody)
        (.memop .free "buf")))

theorem loopHandler_checks : bcheck Psec [] [] loopHandler = some (["db"], [], 40) := by
  decide

/-- **And the old checker refuses it**, for the reason the standing record gives: it
    contains a `.loop`. This is the difference the stage makes, on one program. -/
theorem allcheck_refuses_loopHandler : allcheck Psec [] [] loopHandler = none := by decide

theorem loopHandler_strings : tcheckW 12 [] loopHandler = some ([], [2]) := by decide

/-- **Five certificates on a program that iterates.** Budget 40 over every input and
    every fuel; every resource read was authorized; noninterference; no memory fault; and
    every emitted query carries exactly the two delimiters the template put there.

    Every previous program in this repo carrying all five is straight-line. -/
theorem loopHandler_five :
    (∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
        uexec n loopHandler π s = some r → r.2.1 ≤ 40)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n loopHandler π (initU σ) = some r → ∀ q ∈ r.1.reads, π q = true)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Psec σ σ' →
        uOptLowEq Psec (uexec n loopHandler π (initU σ)) (uexec n loopHandler π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n loopHandler π (initU σ) = some r → r.1.err = false)
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n loopHandler π (initU σ) = some r → ∀ t ∈ r.1.sink, qcount t.2 ∈ [2]) := by
  have hf := bcheck_sound loopHandler [] [] ["db"] [] 40 loopHandler_checks
  refine ⟨hf.bundle.budget, ?_, fun n π σ σ' hσ => ?_, fun n π σ r hr => ?_,
          fun n π σ r hr => tcheckW_no_injection loopHandler_strings n π (initU σ) r
            (by simp [initU]) hr⟩
  · intro n π σ r hr q hq
    have hinv : UMedInv π [] (initU σ) := ⟨by simp [initU], by simp [initU], by simp⟩
    exact (hf.bundle.auth n π (initU σ) r hinv hr).2.1 q hq
  · exact uOptLowEqA.toLowEq (jsecTy_sound n loopHandler [] [] hf.joint π (initU σ)
      (initU σ') SepInv.initU SepInv.initU LabInv.initU LabInv.initU
      ⟨hσ, rfl, rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  · exact (hf.joint.toSepCert.safe n π (initU σ) r SepInv.initU hr).1

/-- And stage 2i's trace theorem covers it: the addresses a *loop* touches are a function
    of the Low part of the input, at every misprediction window. Stage 2i noted that its
    restriction to loop-free programs was the budget's and not the trace's; with the
    budget's restriction lifted, both halves now hold of the same program. -/
theorem loopHandler_trace_is_low (n w : Nat) (π : MedPolicy) (σ σ' : Store)
    (h : lowEq Psec σ σ') :
    straceU n w loopHandler π (initU σ) = straceU n w loopHandler π (initU σ') :=
  jcheck_strace n w loopHandler [] [] (by decide) π (initU σ) (initU σ') (FusedInv.initU h)

/-! ## The boundary, kept where brick 34 put it -/

/-- **The unbounded countdown is still refused.** `bcheck` reads its iteration bound off
    the *constant* the counter is initialised from; a loop whose counter comes from
    anywhere else matches no rule. Brick 34's `dos_unbounded` is why this must stay so —
    no uniform budget exists for it — and `only_the_budget_lacks_a_loop_rule` stays true
    as written: there is still no rule for a general `.loop`. -/
theorem unbounded_countdown_still_refused :
    bcheck Psec [] [] (countU "u" .skip) = none
  ∧ allcheck Psec [] [] (countU "u" .skip) = none := by decide

/-- **A counted loop that dies does not halt.** Stage 1e's `dead` bit makes every command
    a no-op, the decrement included — so a mediation check that fails *inside* a counted
    loop leaves the counter frozen and the loop runs forever. The budget is not violated:
    there is no halting run to violate it, which is exactly why `countU_cost` is provable.

    Recorded as a defect of the *language*, not of the certificate. The fix is a `dead`
    short-circuit in `uexec`'s loop rule, which changes the semantics every module below
    depends on; that is a stage of its own, and naming it is cheaper than guessing at it
    here. -/
theorem a_dead_counted_loop_does_not_halt (n : Nat) (i : String) (body : UCmd)
    (π : MedPolicy) (s : UState) (hd : s.dead = true) (hg : s.store i ≠ 0) :
    uexec n (countU i body) π s = none :=
  uexec_dead_loop_diverges n (.var i) (.seq body (decOne i)) π s hd hg

end ConfTyping
