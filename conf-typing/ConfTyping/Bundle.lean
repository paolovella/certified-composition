/-
  The composable core, stage 1c: one program, one check, two certificates, composed.

  Stage 1a gave the algebra (`GradedAction.prod`: bundles accumulate componentwise).
  Stage 1b gave the object (`UCmd`, with `uexec_embed_eq` making the While bricks a
  fragment rather than a fork). This stage closes the loop: **one checker** over
  `UCmd` that emits a *bundle* of certificates, one soundness theorem, and a worked
  program that carries the bundle end to end.

  The two certificates were chosen because they compose by genuinely different laws,
  which is the whole point of bundling:

  * a **cost budget** — a graded certificate, accumulating by `costGA.mul` (`+`);
  * an **authorization transformation** — a Hoare-style triple `{A} c {A'}` on the
    set of resources known to be authorized, accumulating by *threading*.

  `UCert A c A' k` bundles them. `UCert.seq` is the composition law and shows the two
  halves advancing independently: the budgets add, the authorization sets thread, and
  neither mentions the other — the concrete instance of `Bridge.pair_comp_cert`'s
  "no interaction term". `UCert.ite` joins by intersecting the authorization sets and
  taking the worse budget.

  `ucheck` is the single decidable analysis emitting both, and `ucheck_sound` is the
  single soundness theorem. The artifact is `handler`: a small request handler that
  authorizes, reads, computes and conditionally logs, for which
  `handler_bundle_end_to_end` reports a budget **and** complete mediation from one
  `decide` plus one theorem — the first program in this repo carrying two guarantees
  at once.

  Honest scope, and it is real. **Two certificates, not three**: noninterference is
  not retargeted here. Lifting it needs a low-equivalence on `UState` and a decision
  about whether `reads` and `auth` are observable — a design question, not a
  transcription, and rushing it would be worse than naming it. For embedded While
  programs NI still transfers via stage 1b. **Loop-free only**: `ucheck` returns
  `none` at a `loop`, exactly as brick 34's `costCheck` does, because no uniform
  budget exists there in general; brick 34's constant-initialised `budget` construct
  is the lift, and is a follow-on. So this is a demonstration that the bundle
  mechanism works on a real program, not a claim that the whole map now composes —
  `VULN-COVERAGE` says the same.
-/
import ConfTyping.Unified

namespace ConfTyping

/-! ## The invariant the authorization half maintains -/

/-- Everything the run has authorized was permitted, everything read was permitted,
    and — while the run is live — the statically-tracked set under-approximates the
    dynamic one. The `dead = false` guard is what lets a *refused* check be sound:
    after a refusal the static set may promise more than the state holds, and nothing
    can be read anyway. -/
def UMedInv (π : MedPolicy) (A : List String) (s : UState) : Prop :=
  (∀ r ∈ s.auth, π r = true) ∧ (∀ r ∈ s.reads, π r = true) ∧
  (s.dead = false → ∀ r ∈ A, r ∈ s.auth)

/-! ## The bundle -/

/-- **A bundled certificate.** A cost budget (graded, accumulating by `+`) and an
    authorization triple `{A} c {A'}` (Hoare-shaped, accumulating by threading),
    carried by one program. -/
structure UCert (A : List String) (c : UCmd) (A' : List String) (k : Nat) : Prop where
  budget : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    uexec n c π s = some r → r.2.1 ≤ k
  auth   : ∀ (n : Nat) (π : MedPolicy) (s : UState) (r : UState × Nat × List Bool),
    UMedInv π A s → uexec n c π s = some r → UMedInv π A' r.1

/-- **The composition law.** Budgets add — `costGA.mul` on the nose — and
    authorization sets thread. Neither half mentions the other: this is
    `Bridge.pair_comp_cert`'s "no interaction term", concretely. -/
theorem UCert.seq {A A₁ A₂ : List String} {c₁ c₂ : UCmd} {k₁ k₂ : Nat}
    (h₁ : UCert A c₁ A₁ k₁) (h₂ : UCert A₁ c₂ A₂ k₂) :
    UCert A (.seq c₁ c₂) A₂ (costGA.mul k₁ k₂) := by
  constructor
  · intro n π s r hr
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
            exact Nat.add_le_add (h₁.budget n π s r₁ e₁) (h₂.budget n π r₁.1 r₂ e₂)
  · intro n π s r hinv hr
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
            exact h₂.auth n π r₁.1 r₂ (h₁.auth n π s r₁ hinv e₁) e₂

/-- Joining two branches: intersect what they guarantee, take the worse budget. -/
theorem UCert.ite {A A₁ A₂ : List String} {e : Expr} {c₁ c₂ : UCmd} {k₁ k₂ : Nat}
    (h₁ : UCert A c₁ A₁ k₁) (h₂ : UCert A c₂ A₂ k₂) :
    UCert A (.ite e c₁ c₂) (interStr A₁ A₂) (1 + max k₁ k₂) := by
  constructor
  · intro n π s r hr
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
            have := h₁.budget n π s r₁ e₁
            simp only []
            omega
        · rw [if_neg hg] at hr
          rcases e₂ : uexec n c₂ π s with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            have := h₂.budget n π s r₂ e₂
            simp only []
            omega
  · intro n π s r hinv hr
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
            obtain ⟨ha, hrd, hd⟩ := h₁.auth n π s r₁ hinv e₁
            exact ⟨ha, hrd, fun hdead q hq => hd hdead q (interStr_left hq)⟩
        · rw [if_neg hg] at hr
          rcases e₂ : uexec n c₂ π s with _ | r₂
          · rw [e₂] at hr; simp at hr
          · rw [e₂] at hr; simp only [Option.map_some, Option.some.injEq] at hr
            subst hr
            obtain ⟨ha, hrd, hd⟩ := h₂.auth n π s r₂ hinv e₂
            exact ⟨ha, hrd, fun hdead q hq => hd hdead q (interStr_right hq)⟩

/-! ## The straight-line certificates -/

theorem UCert.skip {A : List String} : UCert A .skip A 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; exact hinv

theorem UCert.assign {A : List String} (x : String) (e : Expr) :
    UCert A (.assign x e) A 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hd⟩ := hinv
        by_cases hdead : s.dead = true
        · simp only [if_pos hdead]; exact ⟨ha, hrd, hd⟩
        · simp only [if_neg hdead]; exact ⟨ha, hrd, hd⟩

/-- A `check` extends the authorization set statically. When the policy *refuses*, the
    run goes dead and the third clause is vacuous — which is exactly why the static
    set may promise what the state does not hold. -/
theorem UCert.check {A : List String} (r₀ : String) :
    UCert A (.check r₀) (r₀ :: A) 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hd⟩ := hinv
        by_cases hdead : s.dead = true
        · simp only [if_pos hdead]
          exact ⟨ha, hrd, fun hc => absurd (hdead ▸ hc) (by simp)⟩
        · have hd0 : s.dead = false := by simpa using hdead
          simp only [if_neg hdead]
          by_cases hp : π r₀ = true
          · simp only [if_pos hp]
            refine ⟨?_, hrd, ?_⟩
            · intro q hq
              rcases List.mem_cons.mp hq with h | h
              · exact h ▸ hp
              · exact ha q h
            · intro _ q hq
              rcases List.mem_cons.mp hq with h | h
              · exact h ▸ List.mem_cons_self ..
              · exact List.mem_cons_of_mem _ (hd hd0 q h)
          · simp only [if_neg hp]
            exact ⟨ha, hrd, fun hc => absurd hc (by simp)⟩

/-- An `access` is certified exactly when the resource is in the authorization set. -/
theorem UCert.access {A : List String} (r₀ : String) (hmem : memStr r₀ A = true) :
    UCert A (.access r₀) A 1 := by
  constructor
  · intro n π s r hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n => simp only [uexec, Option.some.injEq] at hr; subst hr; simp
  · intro n π s r hinv hr
    cases n with
    | zero => simp [uexec] at hr
    | succ n =>
        simp only [uexec, Option.some.injEq] at hr
        subst hr
        obtain ⟨ha, hrd, hd⟩ := hinv
        by_cases hdead : s.dead = true
        · simp only [if_pos hdead]; exact ⟨ha, hrd, hd⟩
        · have hd0 : s.dead = false := by simpa using hdead
          simp only [if_neg hdead]
          refine ⟨ha, ?_, hd⟩
          intro q hq
          rcases List.mem_cons.mp hq with h | h
          · exact h ▸ ha r₀ (hd hd0 r₀ (memStr_mem hmem))
          · exact hrd q h

theorem UCert.weaken {A A' : List String} {c : UCmd} {k k' : Nat}
    (h : UCert A c A' k) (hle : k ≤ k') : UCert A c A' k' :=
  ⟨fun n π s r hr => Nat.le_trans (h.budget n π s r hr) hle, h.auth⟩

/-! ## One checker, both certificates -/

/-- The single decidable analysis: it threads the authorization set and accumulates
    the budget in one pass. `none` at a `loop`, where no uniform budget exists. -/
def ucheck : List String → UCmd → Option (List String × Nat)
  | A, .skip        => some (A, 1)
  | A, .assign _ _  => some (A, 1)
  | A, .check r     => some (r :: A, 1)
  | A, .access r    => if memStr r A then some (A, 1) else none
  | A, .seq c₁ c₂   => (ucheck A c₁).bind fun p₁ =>
                         (ucheck p₁.1 c₂).map fun p₂ => (p₂.1, p₁.2 + p₂.2)
  | A, .ite _ c₁ c₂ => match ucheck A c₁, ucheck A c₂ with
                       | some p₁, some p₂ => some (interStr p₁.1 p₂.1, 1 + max p₁.2 p₂.2)
                       | _, _ => none
  | _, .loop _ _    => none
  | _, .memop _ _   => none   -- stage 1h placeholder; the real rule is `UCert.memop`
  | _, .sop _ _ _   => none   -- stage 1o: strings get their own certificate; see TaintCert

/-- **One soundness theorem for the bundle.** A passing check yields both
    certificates at once. -/
theorem ucheck_sound : ∀ (c : UCmd) (A A' : List String) (k : Nat),
    ucheck A c = some (A', k) → UCert A c A' k
  | .skip, A, A', k, h => by
      simp only [ucheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact UCert.skip
  | .assign x e, A, A', k, h => by
      simp only [ucheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact UCert.assign x e
  | .check r, A, A', k, h => by
      simp only [ucheck, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1; subst h2; exact UCert.check r
  | .access r, A, A', k, h => by
      simp only [ucheck] at h
      by_cases hmem : memStr r A = true
      · rw [if_pos hmem] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h; subst h1; subst h2
        exact UCert.access r hmem
      · rw [if_neg hmem] at h; simp at h
  | .seq c₁ c₂, A, A', k, h => by
      simp only [ucheck] at h
      rcases e₁ : ucheck A c₁ with _ | p₁
      · rw [e₁] at h; simp at h
      · rw [e₁, Option.bind_some] at h
        rcases e₂ : ucheck p₁.1 c₂ with _ | p₂
        · rw [e₂] at h; simp at h
        · rw [e₂] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h; subst h1; subst h2
          exact UCert.seq (ucheck_sound c₁ A p₁.1 p₁.2 e₁)
                          (ucheck_sound c₂ p₁.1 p₂.1 p₂.2 e₂)
  | .ite e c₁ c₂, A, A', k, h => by
      simp only [ucheck] at h
      rcases e₁ : ucheck A c₁ with _ | p₁
      · rw [e₁] at h; simp at h
      · rcases e₂ : ucheck A c₂ with _ | p₂
        · rw [e₁, e₂] at h; simp at h
        · rw [e₁, e₂] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h; subst h1; subst h2
          exact UCert.ite (ucheck_sound c₁ A p₁.1 p₁.2 e₁)
                          (ucheck_sound c₂ A p₂.1 p₂.2 e₂)
  | .loop _ _, _, _, _, h => by simp [ucheck] at h
  | .memop _ _, _, _, _, h => by simp [ucheck] at h
  | .sop _ _ _, _, _, _, h => by simp [ucheck] at h

/-! ## The artifact: one program, both guarantees -/

/-- A small request handler: authorize the database, read it, compute, and log on one
    branch — with the log authorized on the branch that uses it. -/
def handler : UCmd :=
  .seq (.check "db")
    (.seq (.access "db")
      (.seq (.assign "n" (.num 3))
        (.ite (.var "n")
          (.seq (.check "log") (.access "log"))
          (.assign "n" (.num 0)))))

/-- One `decide`: the handler passes, with its authorization set and its budget. -/
theorem handler_checks : ucheck [] handler = some (["db"], 6) := by decide

/-- One theorem: the bundle. -/
theorem handler_bundle : UCert [] handler ["db"] 6 :=
  ucheck_sound handler [] ["db"] 6 handler_checks

/-- Read off the cost half. -/
theorem handler_budget (n : Nat) (π : MedPolicy) (s : UState)
    (r : UState × Nat × List Bool) (hr : uexec n handler π s = some r) : r.2.1 ≤ 6 :=
  handler_bundle.budget n π s r hr

/-- Read off the authorization half, in the standard vocabulary: started fresh, the
    handler reads only what the policy permits. -/
theorem handler_mediated : UMediated handler := by
  intro n π σ r hr x hx
  have hinv : UMedInv π [] (initU σ) :=
    ⟨by simp [initU], by simp [initU], by simp⟩
  exact (handler_bundle.auth n π (initU σ) r hinv hr).2.1 x hx

/-- **The artifact, as one theorem.** A single program, a single decidable check, and
    two certificates that a single composition law carried through it: a cost budget
    and complete mediation. This is the first program in the repo holding two
    guarantees at once. -/
theorem handler_bundle_end_to_end :
    ucheck [] handler = some (["db"], 6)
  ∧ (∀ n π s r, uexec n handler π s = some r → r.2.1 ≤ 6)
  ∧ UMediated handler :=
  ⟨handler_checks, handler_budget, handler_mediated⟩

/-- **Mediation doing per-resource work.** Under a policy that permits the database
    but refuses the log, the handler reads the database and is stopped before the log:
    `reads = ["db"]`, `dead = true`. Not an all-or-nothing gate — the certificate
    tracks resources individually, and the refusal lands exactly where it should. -/
theorem handler_partial_policy :
    ((uexec 12 handler (fun x => x == "db") (initU (fun _ => 0))).map
      (fun r => (r.1.reads, r.1.dead))) = some (["db"], true) := by decide

/-- The certified budget is **tight** on the permitting run — 6 certified, 6 spent —
    so the bound is not slack padding. -/
theorem handler_budget_tight :
    ((uexec 12 handler (fun _ => true) (initU (fun _ => 0))).map (fun r => r.2.1))
      = some 6 := by decide

/-- The check has teeth on this program too: drop the `check` and it is rejected. -/
theorem handler_without_check_rejected :
    ucheck [] (.seq (.access "db") (.assign "n" (.num 3))) = none := by decide

end ConfTyping
