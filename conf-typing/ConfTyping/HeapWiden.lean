/-
  The composable core, stage 1l: widening, and the last of stage 1k's conservatism.

  Stage 1k's loop rule demanded that the body preserve the tracked set *exactly*, so
  `allocating_loop_rejected` — a loop that allocates was refused although nothing about
  it is unsafe. The fix was named there rather than hidden: a widening step, "iterate
  the body's effect to a fixed point, as brick 30's `loopFix` does for intervals". This
  is that step, on a different lattice.

  The tracked set is a **must** set — every variable in it holds a live pointer — so
  weakening means *shrinking*, and the fixed point is reached by descending iteration:
  start at the entry set, intersect with the body's effect, repeat. `narrowFix` does
  that and `narrowFix_spec` extracts exactly the two side-conditions `JSecTy.whileW`
  asks for: the result is contained in the entry set, and the body maps it into a
  superset of itself. Since the sets shrink and are finite, `V.length + 1` steps
  suffice, so the iteration budget is computed rather than guessed.

  `widenProg` is the payoff and it is deliberately not a toy: allocate a pointer,
  enter a loop whose body allocates *another* pointer and dereferences the first, then
  dereference the first again after the loop. Stage 1k's checker rejects it —
  `widening_beats_the_exact_rule` — because the body's tracked set grows. The widened one
  accepts it and still tracks `p` afterwards, which is what makes the final dereference
  typable at all.

  **Why a fuel index rather than well-founded recursion.** The narrowing call sits under
  a closure (`fun W => jcheckW P k W c`), which structural recursion on the *command*
  cannot see through. Recursing on a fuel argument instead keeps the definition
  structural, and structural definitions kernel-reduce — so every witness here is still
  a `decide`. A well-founded version was written first and did type-check, but it broke
  `decide` on all the stage-1k witnesses, which is the same trap nested inductives set
  in bricks 32, 33 and 35. The fuel is bounded by the command's depth, and
  `jcheckW_out_of_fuel` records that running out is a refusal, never an acceptance.

  Stage 1k's `jcheck` is left exactly as it was audited, so its theorems and its
  `decide`-checked witnesses stand unchanged.
-/
import ConfTyping.HeapJoint

namespace ConfTyping

/-! ## Narrowing -/

/-- Descending iteration on the tracked set: intersect with the body's effect until it
    stabilises. Returns the invariant, or `none` if the budget runs out. -/
def narrowFix (f : List String → Option (List String)) :
    Nat → List String → Option (List String)
  | 0,     _ => none
  | k + 1, W =>
      (f W).bind fun W₁ =>
        if interStr W W₁ == W then some W else narrowFix f k (interStr W W₁)

/-- **What a successful narrowing gives you**: a subset of where it started, on which
    the body's effect is a superset — a genuine loop invariant for the tracked set.
    These are precisely the two side-conditions of `JSecTy.whileW`. -/
theorem narrowFix_spec {f : List String → Option (List String)} :
    ∀ (k : Nat) (W W' : List String), narrowFix f k W = some W' →
      (∀ x ∈ W', x ∈ W) ∧ ∃ W₁, f W' = some W₁ ∧ ∀ x ∈ W', x ∈ W₁
  | 0,     _, _,  h => by simp [narrowFix] at h
  | k + 1, W, W', h => by
      simp only [narrowFix] at h
      rcases hf : f W with _ | W₁
      · rw [hf] at h; simp at h
      · rw [hf, Option.bind_some] at h
        by_cases hs : (interStr W W₁ == W) = true
        · rw [if_pos hs] at h
          simp only [Option.some.injEq] at h
          subst h
          have he : interStr W W₁ = W := by simpa using hs
          exact ⟨fun _ hx => hx, W₁, hf,
                 fun x hx => interStr_right (by rw [he]; exact hx)⟩
        · rw [if_neg hs] at h
          obtain ⟨hsub, hrest⟩ := narrowFix_spec k (interStr W W₁) W' h
          exact ⟨fun x hx => interStr_left (hsub x hx), hrest⟩

/-! ## The widened checker -/

/-- Stage 1k's analysis with the loop rule replaced by a narrowing. Recursion is on the
    fuel, not the command, so the closure in the loop case is unproblematic *and* the
    definition still kernel-reduces. -/
def jcheckW (P : Partition) : Nat → List String → UCmd → Option (List String)
  | 0,     _, _                => none
  | _ + 1, V, .skip            => some V
  | _ + 1, V, .assign x e      => if P x || exprLow P e then some (dropStr x V) else none
  | _ + 1, V, .check _         => some V
  | _ + 1, V, .access _        => some V
  | _ + 1, V, .memop .alloc x  => if P x then some (x :: V) else none
  | _ + 1, V, .memop .deref x  => if memStr x V then some V else none
  | _ + 1, V, .memop .free x   => if memStr x V then some (dropStr x V) else none
  | k + 1, V, .seq c₁ c₂       => (jcheckW P k V c₁).bind fun V₁ => jcheckW P k V₁ c₂
  | k + 1, V, .ite e c₁ c₂     => if exprLow P e then
                                    match jcheckW P k V c₁, jcheckW P k V c₂ with
                                    | some V₁, some V₂ => some (interStr V₁ V₂)
                                    | _, _ => none
                                  else none
  | k + 1, V, .loop e c        => if exprLow P e then
                                    narrowFix (fun W => jcheckW P k W c) (V.length + 1) V
                                  else none

/-- Running out of fuel is a **refusal**, never an acceptance — so the fuel can only
    make the analysis more conservative, never unsound. -/
theorem jcheckW_out_of_fuel (P : Partition) (V : List String) (c : UCmd) :
    jcheckW P 0 V c = none := rfl

theorem jcheckW_sound {P : Partition} : ∀ (k : Nat) (c : UCmd) (V V' : List String),
    jcheckW P k V c = some V' → JSecTy P V c V' := by
  intro k
  induction k with
  | zero => intro c V V' h; simp [jcheckW] at h
  | succ k ih =>
    intro c V V' h
    cases c with
    | skip => simp only [jcheckW, Option.some.injEq] at h; subst h; exact .skip V
    | check r => simp only [jcheckW, Option.some.injEq] at h; subst h; exact .check V r
    | access r => simp only [jcheckW, Option.some.injEq] at h; subst h; exact .access V r
    | assign x e =>
        simp only [jcheckW] at h
        by_cases hx : (P x || exprLow P e) = true
        · rw [if_pos hx] at h
          simp only [Option.some.injEq] at h; subst h
          rcases Bool.or_eq_true _ _ |>.mp hx with h' | h'
          · exact .assignH V x e h'
          · exact .assignL V x e h'
        · rw [if_neg hx] at h; simp at h
    | memop op x =>
        cases op with
        | alloc =>
            simp only [jcheckW] at h
            by_cases hx : P x = true
            · rw [if_pos hx] at h
              simp only [Option.some.injEq] at h; subst h; exact .allocH V x hx
            · rw [if_neg hx] at h; simp at h
        | deref =>
            simp only [jcheckW] at h
            by_cases hx : memStr x V = true
            · rw [if_pos hx] at h
              simp only [Option.some.injEq] at h; subst h; exact .deref V x hx
            · rw [if_neg hx] at h; simp at h
        | free =>
            simp only [jcheckW] at h
            by_cases hx : memStr x V = true
            · rw [if_pos hx] at h
              simp only [Option.some.injEq] at h; subst h; exact .free V x hx
            · rw [if_neg hx] at h; simp at h
    | seq c₁ c₂ =>
        simp only [jcheckW] at h
        rcases e₁ : jcheckW P k V c₁ with _ | V₁
        · rw [e₁] at h; simp at h
        · rw [e₁, Option.bind_some] at h
          exact .seq (ih c₁ V V₁ e₁) (ih c₂ V₁ V' h)
    | ite e c₁ c₂ =>
        simp only [jcheckW] at h
        by_cases hg : exprLow P e = true
        · rw [if_pos hg] at h
          rcases e₁ : jcheckW P k V c₁ with _ | V₁
          · rw [e₁] at h; simp at h
          · rcases e₂ : jcheckW P k V c₂ with _ | V₂
            · rw [e₁, e₂] at h; simp at h
            · rw [e₁, e₂] at h
              simp only [Option.some.injEq] at h; subst h
              exact .iteL e hg (ih c₁ V V₁ e₁) (ih c₂ V V₂ e₂)
        · rw [if_neg hg] at h; simp at h
    | loop e c₀ =>
        simp only [jcheckW] at h
        by_cases hg : exprLow P e = true
        · rw [if_pos hg] at h
          obtain ⟨hsub, W₁, hbody, hWW₁⟩ := narrowFix_spec (V.length + 1) V V' h
          exact .whileW e hg hsub (ih c₀ V' W₁ hbody) hWW₁
        · rw [if_neg hg] at h; simp at h

/-- **Both guarantees, from the widened checker.** Same statement as stage 1k's, now
    available for programs whose loops change the tracked set. -/
theorem jcheckW_gives_both {P : Partition} {k : Nat} {c : UCmd} {V' : List String}
    (h : jcheckW P k [] c = some V') :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq P σ σ' →
        uOptLowEq P (uexec n c π (initU σ)) (uexec n c π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n c π (initU σ) = some r → r.1.err = false) := by
  have hty := jcheckW_sound k c [] V' h
  refine ⟨fun n π σ σ' hσ => ?_, fun n π σ r hr => ?_⟩
  · exact jsecTy_sound n c [] V' hty π (initU σ) (initU σ')
      SepInv.initU SepInv.initU ⟨hσ, rfl, rfl⟩
  · exact (hty.toSepCert.safe n π (initU σ) r SepInv.initU hr).1

/-! ## What widening buys -/

/-- Both heap variables are secret; the loop counter is public. -/
def Pheap : Partition := fun x => x == "p" || x == "q"

/-- Allocate `p`; loop, allocating `q` and using `p` each time round; then use `p`
    again. The body's tracked set **grows**, which is what stage 1k could not handle,
    and `p` must survive the loop for the final dereference to be typable. -/
def widenProg : UCmd :=
  .seq (.memop .alloc "p")
   (.seq (.loop (.var "n")
           (.seq (.memop .alloc "q") (.seq (.memop .deref "p") (.assign "n" (.num 0)))))
    (.memop .deref "p"))

/-- **The conservatism is gone, and the difference is visible.** Stage 1k's exact rule
    refuses the program; the widened rule accepts it *and* still tracks `p` afterwards,
    which is what makes the dereference after the loop typable. -/
theorem widening_beats_the_exact_rule :
    jcheck Pheap [] widenProg = none
  ∧ jcheckW Pheap 10 [] widenProg = some ["p"] := by decide

/-- Stage 1k's `allocating_loop_rejected`, now accepted. The invariant found is `[]` —
    the loop allocates and never frees, so nothing survives it — which is the right
    answer rather than a refusal. -/
theorem allocating_loop_now_accepted :
    jcheck Psec [] (.loop (.num 1) (.memop .alloc "secret")) = none
  ∧ jcheckW Psec 6 [] (.loop (.num 1) (.memop .alloc "secret")) = some [] := by decide

/-- And nothing regressed on stage 1k's worked program. -/
theorem widened_agrees_on_safeHeapProg :
    jcheckW Psec 10 [] safeHeapProg = some [] := by decide

/-- The two guarantees, spelled out on `widenProg`: noninterference through a loop that
    allocates, and no memory fault. -/
theorem widenProg_both :
    (∀ (n : Nat) (π : MedPolicy) (σ σ' : Store), lowEq Pheap σ σ' →
        uOptLowEq Pheap (uexec n widenProg π (initU σ)) (uexec n widenProg π (initU σ')))
  ∧ (∀ (n : Nat) (π : MedPolicy) (σ : Store) (r : UState × Nat × List Bool),
        uexec n widenProg π (initU σ) = some r → r.1.err = false) :=
  jcheckW_gives_both widening_beats_the_exact_rule.2

/-- And it runs: no fault, not refused, with `p`'s allocation still live at the end. -/
theorem widenProg_runs :
    ((uexec 9 widenProg (fun _ => true) (initU (fun _ => 0))).map
      (fun r => (r.1.err, r.1.dead, r.1.live))) = some (false, false, [0]) := by decide

/-! ## What is still conservative

    One item survives from stage 1k's list, and it is the design question rather than
    an engineering gap: `allocL` is still absent, so allocation into a *Low* variable
    has no rule. That needs `fresh` in the observation — whether allocation addresses
    are visible to a Low adversary — and `HeapNI.allocL_would_be_unsound` is the
    standing witness that it cannot simply be added.

    The narrowing itself is complete for this lattice: the tracked sets are finite and
    the iteration is descending, so `V.length + 1` steps always reach the fixed point
    when one exists. There is no hidden incompleteness in the *loop* rule any more —
    which is why the remaining conservatism can be stated in one sentence. -/

/-- The budget is not a guess: descending iteration on subsets of a list of length `n`
    stabilises within `n + 1` steps, and the checker passes exactly that. -/
theorem narrowing_budget_is_computed (P : Partition) (k : Nat) (V : List String)
    (e : Expr) (c : UCmd) (hg : exprLow P e = true) :
    jcheckW P (k+1) V (.loop e c)
      = narrowFix (fun W => jcheckW P k W c) (V.length + 1) V := by
  simp only [jcheckW, if_pos hg]

end ConfTyping
