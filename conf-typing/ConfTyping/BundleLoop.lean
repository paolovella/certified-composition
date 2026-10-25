/-
  The composable core, stage 1f: bounded loops enter the bundle.

  Every stage so far carried the same limit: `ucheck` returns `none` at a `loop`, so
  the bundle covered straight-line and branching code only. That is brick 34's limit
  inherited — no uniform budget exists for a general loop — but brick 34 also showed
  the way out: a countdown whose counter is initialised from a **constant** has a
  budget that does not depend on the input. This stage lifts that construct.

  One obstacle had to be cleared first, and it is the interesting part. A bundle's
  budget must hold from **any** starting state, including an aborted one — otherwise
  `UCert.seq` cannot compose, because the first component may abort and hand a dead
  state to the second. So what does an aborted run actually do? Three lemmas settle it,
  and they are worth having in their own right:

  * `uexec_dead_unchanged` — from a dead state **no command changes the state at all**.
    The abort is total, not merely read-suppressing;
  * `uexec_dead_loop_diverges` — a dead run whose loop guard holds *never returns*: the
    store is frozen, so the guard can never become false and the fuel simply runs out;
  * `uexec_dead_cost` — hence an aborted run's cost is bounded by a static `deadCost`,
    with loops contributing 1 because the only terminating case is the guard already
    being false.

  With those, `UCert.ofEmbedded` admits any separately-certified While program — loops
  included — into the bundle, by splitting on whether the run starts live (where
  `uexec_embed_eq` hands the whole of brick 34 over) or dead (where the three lemmas
  apply). `handlerBounded` is the payoff: the stage-1c handler with a **bounded work
  loop** spliced in, still carrying its certificates.

  What remains, stated: this admits loops that are *already certified as While
  programs*, so the counter must be constant-initialised and the body check-free. A
  loop containing a `check` can go dead mid-iteration, and the analysis above covers
  that case only by divergence, not by a bound. General ranking-function analysis is
  still external, exactly as brick 34 said.
-/
import ConfTyping.BundleLedger

namespace ConfTyping

/-! ## What an aborted run does -/

/-- **The abort is total.** From a dead state no command changes the state — not the
    store, not `auth`, not `reads`. Every constructor's dead branch is the identity,
    and `seq`/`ite`/`loop` inherit it. -/
theorem uexec_dead_unchanged : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool), s.dead = true → uexec n c π s = some r → r.1 = s
  | 0,     _, _, _, _, _,  h => by simp [uexec] at h
  | n + 1, c, π, s, r, hd, h => by
      cases c with
      | memop op x =>
          simp only [uexec, ite_eq_left hd, Option.some.injEq] at h; subst h; rfl
      | sop op x e =>
          simp only [uexec, ite_eq_left hd, Option.some.injEq] at h; subst h; rfl
      | hop op x y =>
          simp only [uexec, ite_eq_left hd, Option.some.injEq] at h; subst h; rfl
      | skip => simp only [uexec, Option.some.injEq] at h; subst h; rfl
      | assign x e =>
          simp only [uexec, ite_eq_left hd, Option.some.injEq] at h; subst h; rfl
      | check q =>
          simp only [uexec, ite_eq_left hd, Option.some.injEq] at h; subst h; rfl
      | access q =>
          simp only [uexec, ite_eq_left hd, Option.some.injEq] at h; subst h; rfl
      | seq c₁ c₂ =>
          rw [uexec_seq_eq] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          · rw [e₁, Option.bind_some] at h
            have h1 : r₁.1 = s := uexec_dead_unchanged n c₁ π s r₁ hd e₁
            rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have hd1 : r₁.1.dead = true := by rw [h1]; exact hd
              exact (uexec_dead_unchanged n c₂ π r₁.1 r₂ hd1 e₂).trans h1
      | ite e c₁ c₂ =>
          rw [uexec_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact uexec_dead_unchanged n c₁ π s r₁ hd e₁
          · rw [ite_eq_right hg] at h
            rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact uexec_dead_unchanged n c₂ π s r₂ hd e₂
      | loop e c₀ =>
          rw [uexec_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₀ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁, Option.bind_some] at h
              have h1 : r₁.1 = s := uexec_dead_unchanged n c₀ π s r₁ hd e₁
              rcases e₂ : uexec n (.loop e c₀) π r₁.1 with _ | r₂
              · rw [e₂] at h; simp at h
              · rw [e₂] at h
                simp only [Option.map_some, Option.some.injEq] at h
                subst h
                have hd1 : r₁.1.dead = true := by rw [h1]; exact hd
                exact (uexec_dead_unchanged n (.loop e c₀) π r₁.1 r₂ hd1 e₂).trans h1
          · rw [ite_eq_right hg] at h
            simp only [Option.some.injEq] at h; subst h; rfl

/-- **A dead run cannot leave a loop it is already inside.** The store is frozen, so a
    guard that holds keeps holding, and the fuel simply runs out. -/
theorem uexec_dead_loop_diverges : ∀ (n : Nat) (e : Expr) (c : UCmd) (π : MedPolicy)
    (s : UState), s.dead = true → evalE e s.store ≠ 0 → uexec n (.loop e c) π s = none
  | 0,     _, _, _, _, _,  _  => rfl
  | n + 1, e, c, π, s, hd, hg => by
      rw [uexec_loop_eq, ite_eq_left hg]
      rcases e₁ : uexec n c π s with _ | r₁
      · simp
      · have h1 : r₁.1 = s := uexec_dead_unchanged n c π s r₁ hd e₁
        have hd1 : r₁.1.dead = true := by rw [h1]; exact hd
        have hg1 : evalE e r₁.1.store ≠ 0 := by rw [h1]; exact hg
        rw [Option.bind_some, uexec_dead_loop_diverges n e c π r₁.1 hd1 hg1]
        simp

/-- The cost an aborted run can accrue: everything is a no-op, and a loop can only
    terminate by its guard already being false. -/
def deadCost : UCmd → Nat
  | .skip        => 1
  | .assign _ _  => 1
  | .check _     => 1
  | .access _    => 1
  | .seq a b     => deadCost a + deadCost b
  | .ite _ a b   => 1 + max (deadCost a) (deadCost b)
  | .loop _ _    => 1
  | .memop _ _   => 1
  | .sop _ _ _   => 1
  | .hop _ _ _   => 1

theorem uexec_dead_cost : ∀ (n : Nat) (c : UCmd) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool), s.dead = true → uexec n c π s = some r →
    r.2.1 ≤ deadCost c
  | 0,     _, _, _, _, _,  h => by simp [uexec] at h
  | n + 1, c, π, s, r, hd, h => by
      cases c with
      | memop op x =>
          simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | sop op x e =>
          simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | hop op x y =>
          simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | skip => simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | assign x e =>
          simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | check q => simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | access q => simp only [uexec, Option.some.injEq] at h; subst h; simp [deadCost]
      | seq c₁ c₂ =>
          rw [uexec_seq_eq] at h
          rcases e₁ : uexec n c₁ π s with _ | r₁
          · rw [e₁] at h; simp at h
          · rw [e₁, Option.bind_some] at h
            have h1 : r₁.1 = s := uexec_dead_unchanged n c₁ π s r₁ hd e₁
            have hd1 : r₁.1.dead = true := by rw [h1]; exact hd
            rcases e₂ : uexec n c₂ π r₁.1 with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              exact Nat.add_le_add (uexec_dead_cost n c₁ π s r₁ hd e₁)
                                   (uexec_dead_cost n c₂ π r₁.1 r₂ hd1 e₂)
      | ite e c₁ c₂ =>
          rw [uexec_ite_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₁ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have := uexec_dead_cost n c₁ π s r₁ hd e₁
              simp only [deadCost]; omega
          · rw [ite_eq_right hg] at h
            rcases e₂ : uexec n c₂ π s with _ | r₂
            · rw [e₂] at h; simp at h
            · rw [e₂] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h
              have := uexec_dead_cost n c₂ π s r₂ hd e₂
              simp only [deadCost]; omega
      | loop e c₀ =>
          rw [uexec_loop_eq] at h
          by_cases hg : evalE e s.store ≠ 0
          · rw [ite_eq_left hg] at h
            rcases e₁ : uexec n c₀ π s with _ | r₁
            · rw [e₁] at h; simp at h
            · rw [e₁, Option.bind_some] at h
              have h1 : r₁.1 = s := uexec_dead_unchanged n c₀ π s r₁ hd e₁
              have hd1 : r₁.1.dead = true := by rw [h1]; exact hd
              have hg1 : evalE e r₁.1.store ≠ 0 := by rw [h1]; exact hg
              rw [uexec_dead_loop_diverges n e c₀ π r₁.1 hd1 hg1] at h
              simp at h
          · rw [ite_eq_right hg] at h
            simp only [Option.some.injEq] at h; subst h; simp [deadCost]

/-! ## Admitting a certified While program — loops included -/

/-- **Any separately-certified While program joins the bundle.** Its budget is the
    larger of the live bound (which `uexec_embed_eq` hands over from the While
    development wholesale) and the aborted bound; and since an embedded program has
    no `check`/`access`, it moves the authorization set nowhere. -/
theorem UCert.ofEmbedded {A : List String} {c : WCmd} {k : Nat} (h : CostAtMost c k) :
    UCert A (uembed c) A (max k (deadCost (uembed c))) := by
  constructor
  · intro n π s r hr
    by_cases hd : s.dead = true
    · exact Nat.le_trans (uexec_dead_cost n (uembed c) π s r hd hr) (Nat.le_max_right _ _)
    · have hd0 : s.dead = false := by simpa using hd
      have := ucost_of_cost h n π s r hd0 hr
      exact Nat.le_trans this (Nat.le_max_left _ _)
  · intro n π s r hinv hr
    by_cases hd : s.dead = true
    · rw [uexec_dead_unchanged n (uembed c) π s r hd hr]; exact hinv
    · have hd0 : s.dead = false := by simpa using hd
      rw [uexec_embed_eq n c π s hd0] at hr
      rcases ho : wexec n c s.store with _ | o
      · rw [ho] at hr; simp at hr
      · rw [ho] at hr
        simp only [Option.map_some, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hdd⟩ := hinv
        exact ⟨ha, hrd, hdd⟩

/-! ## The payoff: a handler that does bounded work -/

/-- The stage-1c handler, with a **bounded work loop** spliced in: authorize, read,
    then do at most five units of constant-budgeted work. -/
def handlerBounded : UCmd :=
  .seq (.check "db")
    (.seq (.access "db")
      (uembed (budget "w" 5 .skip)))

/-- The bounded-work fragment is certified as a While program by brick 34, so it
    enters the bundle by `UCert.ofEmbedded`. -/
theorem work_cert {A : List String} :
    UCert A (uembed (budget "w" 5 .skip))
      A (max (1 + (1 + 5 * (1 + 3))) (deadCost (uembed (budget "w" 5 .skip)))) :=
  UCert.ofEmbedded (budget_cost 5 (by decide) cost_skip)

/-- **Loops are in the bundle.** The handler authorizes, reads, and runs a bounded
    loop — and still carries a budget and its authorization triple, composed by the
    same `UCert.seq`. -/
theorem handlerBounded_cert :
    UCert [] handlerBounded ["db"]
      (costGA.mul 1 (costGA.mul 1
        (max (1 + (1 + 5 * (1 + 3))) (deadCost (uembed (budget "w" 5 .skip)))))) :=
  UCert.seq (UCert.check "db")
    (UCert.seq (UCert.access "db" (by decide)) work_cert)

/-- The loop-free limit is gone: a `loop` really is present in the certified program. -/
theorem handlerBounded_contains_a_loop :
    ∃ e c, (uembed (budget "w" 5 .skip)) = .seq (.assign "w" (.num 5)) (.loop e c) :=
  ⟨.var "w", uembed (.seq .skip (dec1 "w")), rfl⟩

/-- **The numbers, and an honest difference from stage 1c.** The certified budget is
    22; the permitting run spends 19 and the refused run 4. Unlike the straight-line
    handler, whose bound was *tight*, this one over-approximates by 3 — the price of
    an analytic bound across a loop. The refused run also shows the three lemmas at
    work: the abort suppresses the counter's initialisation, so the guard is already
    false and the loop exits at once rather than spinning. -/
theorem handlerBounded_numbers :
    ((uexec 80 handlerBounded (fun _ => true) (initU (fun _ => 0))).map
      (fun r => r.2.1)) = some 19
  ∧ ((uexec 80 handlerBounded (fun _ => false) (initU (fun _ => 0))).map
      (fun r => (r.2.1, r.1.dead))) = some (4, true) := by decide

/-- And the bundle's mediation reading survives the loop. -/
theorem handlerBounded_mediated : UMediated handlerBounded := by
  intro n π σ r hr x hx
  have hinv : UMedInv π [] (initU σ) := ⟨by simp [initU], by simp [initU], by simp⟩
  exact (handlerBounded_cert.auth n π (initU σ) r hinv hr).2.1 x hx

end ConfTyping
