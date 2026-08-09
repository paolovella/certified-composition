/-
  The composable core, stage 1b: one language, and the embedding that makes the
  earlier bricks transfer rather than fork.

  The security program's structural weakness, measured: sixteen distinct instruction
  types across thirty modules, and **zero** cross-brick composition — not one module
  mentions two brick languages, and the only bridge in the repo is brick 7's
  `embed : Cmd → WCmd`. So thirty-five bricks each prove "for *my* toy language this
  class is excluded", and no program carries two guarantees at once. That undercuts
  the repo's own headline — composition *accumulates* certificates — exactly where
  the goal needs it.

  Stage 1a added the algebra (`GradedAction.prod`, `Bridge.pair_comp_cert`: bundles
  accumulate componentwise). This stage adds the object: **one language** carrying
  the three dimensions that the bricks treat separately —

  * store and control flow, so noninterference applies (bricks 3–10);
  * a **cost** counter, so budgets apply (brick 34);
  * **authorization**, so mediation applies (brick 35).

  `UCmd` is `WCmd` plus `check` and `access`. The state gains `auth`, `reads` and a
  `dead` flag: a refused check aborts, and after that every step is a no-op, which is
  what makes "nothing is read after a refusal" hold definitionally rather than by
  proof.

  The load-bearing theorem is **`uexec_embed_eq`**: on the image of `uembed`, the
  unified machine's store, cost and branch trace are *exactly* `wexec`'s, and `auth`,
  `reads` and `dead` are untouched. One equation, so the earlier While development is
  a fragment of this one rather than a parallel copy — the same standard brick 7 set
  with `wexec_embed_eq`, applied one level up. Two transfers follow immediately:
  `ucost_of_cost` (a brick-34 budget is a budget here) and `uembed_mediated` (a
  program with no `access` reads nothing, so it is mediated for free).

  Honest scope. This stage builds the object and the transfers; it does not yet
  re-derive the *checkers* on it — that is stage 1c, which retargets noninterference,
  cost and mediation onto `UCmd` and proves one program carrying all three composed
  certificates. Nothing here is claimed to supersede the existing bricks: they remain
  the record of what was proved, and the transfers are what make them reusable.
-/
import ConfTyping.CostBound
import ConfTyping.Mediation

namespace ConfTyping

/-! ## The language -/

/-- `WCmd` plus authorization. Everything the earlier While bricks can say is still
    sayable, and two dimensions are added. -/
inductive UCmd where
  | skip   : UCmd
  | assign : String → Expr → UCmd
  | seq    : UCmd → UCmd → UCmd
  | ite    : Expr → UCmd → UCmd → UCmd
  | loop   : Expr → UCmd → UCmd
  | check  : String → UCmd        -- consult the policy; a refusal aborts
  | access : String → UCmd        -- the protected read

/-- The unified state: the store the While bricks use, plus what the mediation brick
    needs. `dead` records a refused check. -/
structure UState where
  store : Store
  auth  : List String
  reads : List String
  dead  : Bool

def initU (σ : Store) : UState := ⟨σ, [], [], false⟩

/-- The evaluator. Shaped to mirror `wexec` line for line, so the embedding theorem
    is a structural induction and not a translation. After a refusal every step is a
    no-op: the abort is definitional. -/
def uexec : Nat → UCmd → MedPolicy → UState → Option (UState × Nat × List Bool)
  | 0,     _,            _, _ => none
  | _ + 1, .skip,        _, s => some (s, 1, [])
  | _ + 1, .assign x e,  _, s =>
      some (if s.dead then s else { s with store := upd s.store x (evalE e s.store) }, 1, [])
  | _ + 1, .check r,     π, s =>
      some (if s.dead then s
            else if π r then { s with auth := r :: s.auth }
            else { s with dead := true }, 1, [])
  | _ + 1, .access r,    _, s =>
      some (if s.dead then s else { s with reads := r :: s.reads }, 1, [])
  | n + 1, .seq c₁ c₂,   π, s =>
      (uexec n c₁ π s).bind fun r₁ =>
        (uexec n c₂ π r₁.1).map fun r₂ =>
          (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2)
  | n + 1, .ite e c₁ c₂, π, s =>
      if evalE e s.store ≠ 0 then
        (uexec n c₁ π s).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
      else
        (uexec n c₂ π s).map fun r => (r.1, 1 + r.2.1, false :: r.2.2)
  | n + 1, .loop e c,    π, s =>
      if evalE e s.store ≠ 0 then
        (uexec n c π s).bind fun r₁ =>
          (uexec n (.loop e c) π r₁.1).map fun r₂ =>
            (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
      else some (s, 1, [false])

theorem uexec_seq_eq (n : Nat) (c₁ c₂ : UCmd) (π : MedPolicy) (s : UState) :
    uexec (n+1) (.seq c₁ c₂) π s
      = (uexec n c₁ π s).bind fun r₁ =>
          (uexec n c₂ π r₁.1).map fun r₂ =>
            (r₂.1, r₁.2.1 + r₂.2.1, r₁.2.2 ++ r₂.2.2) := rfl

theorem uexec_ite_eq (n : Nat) (e : Expr) (c₁ c₂ : UCmd) (π : MedPolicy) (s : UState) :
    uexec (n+1) (.ite e c₁ c₂) π s
      = if evalE e s.store ≠ 0 then
          (uexec n c₁ π s).map fun r => (r.1, 1 + r.2.1, true :: r.2.2)
        else (uexec n c₂ π s).map fun r => (r.1, 1 + r.2.1, false :: r.2.2) := rfl

theorem uexec_loop_eq (n : Nat) (e : Expr) (c : UCmd) (π : MedPolicy) (s : UState) :
    uexec (n+1) (.loop e c) π s
      = if evalE e s.store ≠ 0 then
          (uexec n c π s).bind fun r₁ =>
            (uexec n (.loop e c) π r₁.1).map fun r₂ =>
              (r₂.1, 1 + r₁.2.1 + r₂.2.1, true :: (r₁.2.2 ++ r₂.2.2))
        else some (s, 1, [false]) := rfl

/-! ## The embedding -/

/-- The While language sits inside the unified one, structurally. -/
def uembed : WCmd → UCmd
  | .skip       => .skip
  | .assign x e => .assign x e
  | .seq a b    => .seq (uembed a) (uembed b)
  | .ite e a b  => .ite e (uembed a) (uembed b)
  | .loop e a   => .loop e (uembed a)

/-- **The model grew rather than forked.** On the image of `uembed`, started live, the
    unified machine's store, cost and branch trace are *exactly* `wexec`'s, and
    `auth`, `reads` and `dead` are untouched — one equation. Everything the While
    bricks proved therefore holds here, and nothing about the two new dimensions can
    be disturbed by an old program. -/
theorem uexec_embed_eq : ∀ (n : Nat) (c : WCmd) (π : MedPolicy) (s : UState),
    s.dead = false →
    uexec n (uembed c) π s
      = (wexec n c s.store).map (fun o => ({ s with store := o.1 }, o.2.1, o.2.2))
  | 0,     _, _, _, _ => rfl
  | n + 1, c, π, s, hd => by
      cases c with
      | skip =>
          simp only [uembed, uexec, wexec, Option.map_some]
      | assign x e =>
          simp only [uembed, uexec, wexec, Option.map_some, hd, Bool.false_eq_true,
                     if_false]
      | seq c₁ c₂ =>
          rw [uembed, uexec_seq_eq, wexec_seq_eq,
              uexec_embed_eq n c₁ π s hd]
          rcases h₁ : wexec n c₁ s.store with _ | o₁
          · simp
          · simp only [Option.map_some, Option.bind_some]
            have hd' : ({ s with store := o₁.1 } : UState).dead = false := hd
            rw [uexec_embed_eq n c₂ π { s with store := o₁.1 } hd']
            rcases h₂ : wexec n c₂ o₁.1 with _ | o₂
            · simp
            · simp
      | ite e c₁ c₂ =>
          rw [uembed, uexec_ite_eq, wexec_ite_eq]
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg, if_pos hg, uexec_embed_eq n c₁ π s hd]
            rcases h₁ : wexec n c₁ s.store with _ | o₁ <;> simp
          · rw [if_neg hg, if_neg hg, uexec_embed_eq n c₂ π s hd]
            rcases h₁ : wexec n c₂ s.store with _ | o₁ <;> simp
      | loop e c₀ =>
          rw [uembed, uexec_loop_eq, wexec_loop_eq]
          by_cases hg : evalE e s.store ≠ 0
          · rw [if_pos hg, if_pos hg, uexec_embed_eq n c₀ π s hd]
            rcases h₁ : wexec n c₀ s.store with _ | o₁
            · simp
            · simp only [Option.map_some, Option.bind_some]
              have hd' : ({ s with store := o₁.1 } : UState).dead = false := hd
              have := uexec_embed_eq n (.loop e c₀) π { s with store := o₁.1 } hd'
              rw [uembed] at this
              rw [this]
              rcases h₂ : wexec n (.loop e c₀) o₁.1 with _ | o₂
              · simp
              · simp
          · rw [if_neg hg, if_neg hg]
            simp only [Option.map_some]

/-! ## What transfers -/

/-- A uniform cost budget on the unified machine, started live. -/
def UCostAtMost (c : UCmd) (k : Nat) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    s.dead = false → uexec n c π s = some r → r.2.1 ≤ k

/-- Complete mediation on the unified machine: started live with nothing read, every
    resource read is one the policy permits. -/
def UMediated (c : UCmd) : Prop :=
  ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    s.dead = false → s.reads = [] → uexec n c π s = some r →
    ∀ x ∈ r.1.reads, π x = true

/-- **Brick 34's budgets transfer.** A `CostAtMost` proof about a While program is a
    budget for its image here — no reproof. -/
theorem ucost_of_cost {c : WCmd} {k : Nat} (h : CostAtMost c k) :
    UCostAtMost (uembed c) k := by
  intro n π s r hd hr
  rw [uexec_embed_eq n c π s hd] at hr
  rcases ho : wexec n c s.store with _ | o
  · rw [ho] at hr; simp at hr
  · rw [ho] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    exact h n s.store o ho

/-- **Old programs are mediated for free.** An embedded While program has no `access`,
    so it reads nothing, and mediation holds vacuously — the new dimension cannot be
    violated by code that predates it. -/
theorem uembed_mediated (c : WCmd) : UMediated (uembed c) := by
  intro n π s r hd hrd hr x hx
  rw [uexec_embed_eq n c π s hd] at hr
  rcases ho : wexec n c s.store with _ | o
  · rw [ho] at hr; simp at hr
  · rw [ho] at hr
    simp only [Option.map_some, Option.some.injEq] at hr
    subst hr
    simp only [hrd] at hx
    exact absurd hx (by simp)

/-! ## The new dimensions are live, not decorative -/

/-- A program that reads without checking: expressible here, and *not* mediated. -/
def uVictim : UCmd := .access "db"

/-- A program that checks first. -/
def uFixed : UCmd := .seq (.check "db") (.access "db")

theorem uVictim_not_mediated : ¬ UMediated uVictim := by
  intro h
  have := h 1 (fun _ => false) (initU (fun _ => 0)) _ rfl rfl rfl
  simp only [uexec, initU] at this
  exact absurd (this "db" (by simp)) (by simp)

/-- Under a refusing policy the fixed program aborts and reads nothing — the abort is
    definitional, not proved. -/
theorem uFixed_refused_reads_nothing :
    ((uexec 2 uFixed (fun _ => false) (initU (fun _ => 0))).map (fun r => r.1.reads))
      = some [] := by decide

/-- Under a permitting policy it reads, and the read is permitted. -/
theorem uFixed_permitted_reads :
    ((uexec 2 uFixed (fun _ => true) (initU (fun _ => 0))).map (fun r => r.1.reads))
      = some ["db"] := by decide

end ConfTyping
