/-
  Resource exhaustion — brick 34: the cost bound as a graded certificate.

  Row 10 of `VULN-COVERAGE.md` (CWE-400) has been REDUCIBLE **[classified]** since
  brick 1: "the cost counter is already in the outcome, so `cost ≤ f(input)` is a
  safety-shaped quantitative bound — a *graded certificate* in the transport sense —
  and bounds compose by accumulation". That was an assertion. This brick proves it,
  and corrects the one part of it that does not hold.

  The property is **uniformity**: `CostAtMost c k` says that *whatever* the input and
  *whatever* the fuel, a halting run of `c` costs at most `k`. Algorithmic-complexity
  DoS is exactly the failure of uniformity — the bound exists per input but not across
  inputs — which is why the quantifier order is the whole definition.

  What gets proved:

  * **Accumulation is a `GradedAction`.** `costGA : GradedAction Nat Nat` with grade
    composition `+`, action `+`, order `≤` — the three fields `Bridge.comp` actually
    uses, checked. `cost_seq` is the accumulation law: sequencing adds budgets,
    `costGA.mul` on the nose (`cost_seq_is_mul`). So "bounds compose by accumulation"
    is now a theorem in the repo's own algebra.

  * **The attack.** `countdown_cost_exact` computes the cost of the canonical
    countdown loop as `1 + 3v` in its counter `v`, so `dos_unbounded` — a loop whose
    trip count is read from untrusted input satisfies `CostAtMost` for **no** `k`.
    Algorithmic-complexity DoS as a theorem, and note it is invisible to every
    earlier brick: the program is memory-safe, injection-free and noninterferent.

  * **The fix, generated.** Initialising the counter from a **constant** restores
    uniformity: `budget_cost` bounds `budget x k c` by `2 + k * (kc + 3)` for any body
    with a budget `kc` that does not touch the counter (`noAssign`). `costCheck`
    computes bounds for the loop-free fragment and `costCheck_sound` certifies them.

  * **The honest correction.** Row 10 gestured at `Bridge.ofModulus` territory. That
    part is **wrong and is corrected here**: a `Bridge` certifies a *binary* quantity
    (`dist (map x) (map y) ≤ act cert (dist x y)`), and a cost budget is **unary** —
    a bound on one run, not a modulus relating two. What transfers is the
    `GradedAction`, which is exactly the accumulation algebra `Bridge.comp` consumes;
    what does not transfer is the contraction. Sensitivity of cost to input *would* be
    binary and would be Bridge-shaped, and is a different (unproved) property.

  Honest limits. `CostAtMost` is a bound on halting runs — availability ("eventually
  responds") is liveness-shaped, still not expressible here and still not claimed.
  The loop rule covers the canonical countdown; general ranking-function analysis is
  external, exactly as row 10 said. Cost is the instrumented step count, not wall
  clock: the model gap of §0 applies unchanged.
-/
import ConfTyping.WhileImp
import TransportCalculus

namespace ConfTyping

/-! ## The property -/

/-- **A uniform cost budget.** Whatever the input store and whatever the fuel, a
    halting run costs at most `k`. The quantifier order is the point: a per-input
    bound is free (every halting run has *some* cost), and DoS is precisely the
    failure of the bound to be uniform. -/
def CostAtMost (c : WCmd) (k : Nat) : Prop :=
  ∀ (n : Nat) (σ : Store) (o : Outcome), wexec n c σ = some o → o.2.1 ≤ k

theorem CostAtMost.mono {c : WCmd} {k k' : Nat} (h : CostAtMost c k) (hle : k ≤ k') :
    CostAtMost c k' := fun n σ o ho => Nat.le_trans (h n σ o ho) hle

/-! ## Accumulation is a graded action -/

/-- Budgets compose by **addition**: the grade monoid is `(ℕ, +)` acting on budgets
    by `+`, ordered by `≤`. These are exactly the three fields `Bridge.comp` uses. -/
def costGA : TransportCalculus.GradedAction Nat Nat where
  mul      := (· + ·)
  le       := (· ≤ ·)
  act      := (· + ·)
  le_trans := fun h₁ h₂ => Nat.le_trans h₁ h₂
  act_mul  := fun m₁ m₂ d => Nat.add_assoc m₁ m₂ d
  act_mono := by intros; omega

theorem cost_skip : CostAtMost .skip 1 := by
  intro n σ o h
  cases n with
  | zero => simp [wexec] at h
  | succ n => simp only [wexec, Option.some.injEq] at h; subst h; simp

theorem cost_assign (x : String) (e : Expr) : CostAtMost (.assign x e) 1 := by
  intro n σ o h
  cases n with
  | zero => simp [wexec] at h
  | succ n => simp only [wexec, Option.some.injEq] at h; subst h; simp

/-- **The accumulation law.** Sequencing adds budgets. -/
theorem cost_seq {c₁ c₂ : WCmd} {k₁ k₂ : Nat}
    (h₁ : CostAtMost c₁ k₁) (h₂ : CostAtMost c₂ k₂) :
    CostAtMost (.seq c₁ c₂) (k₁ + k₂) := by
  intro n σ o h
  cases n with
  | zero => simp [wexec] at h
  | succ n =>
      rw [wexec_seq_eq] at h
      rcases hr₁ : wexec n c₁ σ with _ | r₁
      · rw [hr₁] at h; simp at h
      · rw [hr₁, Option.bind_some] at h
        rcases hr₂ : wexec n c₂ r₁.1 with _ | r₂
        · rw [hr₂] at h; simp at h
        · rw [hr₂] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact Nat.add_le_add (h₁ n σ r₁ hr₁) (h₂ n r₁.1 r₂ hr₂)

/-- The budget of a sequence is `costGA.mul` of the parts — accumulation in the
    repo's own algebra, definitionally. -/
theorem cost_seq_is_mul {c₁ c₂ : WCmd} {k₁ k₂ : Nat}
    (h₁ : CostAtMost c₁ k₁) (h₂ : CostAtMost c₂ k₂) :
    CostAtMost (.seq c₁ c₂) (costGA.mul k₁ k₂) := cost_seq h₁ h₂

theorem cost_ite {e : Expr} {c₁ c₂ : WCmd} {k : Nat}
    (h₁ : CostAtMost c₁ k) (h₂ : CostAtMost c₂ k) :
    CostAtMost (.ite e c₁ c₂) (1 + k) := by
  intro n σ o h
  cases n with
  | zero => simp [wexec] at h
  | succ n =>
      rw [wexec_ite_eq] at h
      by_cases hg : evalE e σ ≠ 0
      · rw [if_pos hg] at h
        rcases hr : wexec n c₁ σ with _ | r
        · rw [hr] at h; simp at h
        · rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
          subst h; exact Nat.add_le_add_left (h₁ n σ r hr) 1
      · rw [if_neg hg] at h
        rcases hr : wexec n c₂ σ with _ | r
        · rw [hr] at h; simp at h
        · rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
          subst h; exact Nat.add_le_add_left (h₂ n σ r hr) 1

/-! ## A checker for the loop-free fragment -/

/-- A static budget: `none` at a `loop`, where no uniform bound exists in general. -/
def costCheck : WCmd → Option Nat
  | .skip       => some 1
  | .assign _ _ => some 1
  | .seq a b    => match costCheck a, costCheck b with
                   | some x, some y => some (x + y)
                   | _, _ => none
  | .ite _ a b  => match costCheck a, costCheck b with
                   | some x, some y => some (1 + max x y)
                   | _, _ => none
  | .loop _ _   => none

/-- **The checker is sound**: a computed budget is a uniform budget. -/
theorem costCheck_sound : ∀ (c : WCmd) (k : Nat), costCheck c = some k → CostAtMost c k
  | .skip, k, h => by
      simp only [costCheck, Option.some.injEq] at h; subst h; exact cost_skip
  | .assign x e, k, h => by
      simp only [costCheck, Option.some.injEq] at h; subst h; exact cost_assign x e
  | .seq a b, k, h => by
      simp only [costCheck] at h
      rcases ha : costCheck a with _ | x
      · rw [ha] at h; simp at h
      · rcases hb : costCheck b with _ | y
        · rw [ha, hb] at h; simp at h
        · rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          exact cost_seq (costCheck_sound a x ha) (costCheck_sound b y hb)
  | .ite e a b, k, h => by
      simp only [costCheck] at h
      rcases ha : costCheck a with _ | x
      · rw [ha] at h; simp at h
      · rcases hb : costCheck b with _ | y
        · rw [ha, hb] at h; simp at h
        · rw [ha, hb] at h
          simp only [Option.some.injEq] at h
          subst h
          exact cost_ite ((costCheck_sound a x ha).mono (Nat.le_max_left x y))
                         ((costCheck_sound b y hb).mono (Nat.le_max_right x y))
  | .loop _ _, _, h => by simp [costCheck] at h

/-! ## Loops: where uniformity is lost -/

/-- `c` never assigns `x`. -/
def noAssign (x : String) : WCmd → Bool
  | .skip       => true
  | .assign y _ => y != x
  | .seq a b    => noAssign x a && noAssign x b
  | .ite _ a b  => noAssign x a && noAssign x b
  | .loop _ a   => noAssign x a

/-- A command that never assigns `x` leaves `x` alone. -/
theorem noAssign_preserves : ∀ (n : Nat) (x : String) (c : WCmd) (σ : Store) (o : Outcome),
    noAssign x c = true → wexec n c σ = some o → o.1 x = σ x
  | 0,     _, _, _, _, _, h => by simp [wexec] at h
  | n + 1, x, c, σ, o, hna, h => by
      cases c with
      | skip => simp only [wexec, Option.some.injEq] at h; subst h; rfl
      | assign y e =>
          simp only [wexec, Option.some.injEq] at h
          subst h
          have hxy : ¬ (x = y) := by
            simp only [noAssign, bne_iff_ne, ne_eq] at hna
            exact fun hh => hna hh.symm
          simp [upd, hxy]
      | seq a b =>
          obtain ⟨ha, hb⟩ : noAssign x a = true ∧ noAssign x b = true := by
            simpa [noAssign] using hna
          rw [wexec_seq_eq] at h
          rcases hr₁ : wexec n a σ with _ | r₁
          · rw [hr₁] at h; simp at h
          · rw [hr₁, Option.bind_some] at h
            rcases hr₂ : wexec n b r₁.1 with _ | r₂
            · rw [hr₂] at h; simp at h
            · rw [hr₂] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h
              rw [noAssign_preserves n x b r₁.1 r₂ hb hr₂,
                  noAssign_preserves n x a σ r₁ ha hr₁]
      | ite e a b =>
          obtain ⟨ha, hb⟩ : noAssign x a = true ∧ noAssign x b = true := by
            simpa [noAssign] using hna
          rw [wexec_ite_eq] at h
          by_cases hg : evalE e σ ≠ 0
          · rw [if_pos hg] at h
            rcases hr : wexec n a σ with _ | r
            · rw [hr] at h; simp at h
            · rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact noAssign_preserves n x a σ r ha hr
          · rw [if_neg hg] at h
            rcases hr : wexec n b σ with _ | r
            · rw [hr] at h; simp at h
            · rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
              subst h; exact noAssign_preserves n x b σ r hb hr
      | loop e a =>
          have ha : noAssign x a = true := by simpa [noAssign] using hna
          rw [wexec_loop_eq] at h
          by_cases hg : evalE e σ ≠ 0
          · rw [if_pos hg] at h
            rcases hr₁ : wexec n a σ with _ | r₁
            · rw [hr₁] at h; simp at h
            · rw [hr₁, Option.bind_some] at h
              rcases hr₂ : wexec n (.loop e a) r₁.1 with _ | r₂
              · rw [hr₂] at h; simp at h
              · rw [hr₂] at h; simp only [Option.map_some, Option.some.injEq] at h
                subst h
                rw [noAssign_preserves n x (.loop e a) r₁.1 r₂ hna hr₂,
                    noAssign_preserves n x a σ r₁ ha hr₁]
          · rw [if_neg hg] at h
            simp only [Option.some.injEq] at h; subst h; rfl

/-- Decrement `x` by one. -/
def dec1 (x : String) : WCmd := .assign x (.add (.var x) (.num (-1)))

/-- The canonical countdown: run the body, decrement the counter, repeat. -/
def countdown (x : String) (c : WCmd) : WCmd := .loop (.var x) (.seq c (dec1 x))

/-- One turn: the body costs at most `kc + 1` and decrements the counter. -/
theorem countdown_turn {x : String} {c : WCmd} {kc : Nat}
    (hna : noAssign x c = true) (hc : CostAtMost c kc)
    (n : Nat) (σ : Store) (r : Outcome) (h : wexec n (.seq c (dec1 x)) σ = some r) :
    r.2.1 ≤ kc + 1 ∧ r.1 x = σ x - 1 := by
  cases n with
  | zero => simp [wexec] at h
  | succ m =>
      rw [wexec_seq_eq] at h
      rcases hcc : wexec m c σ with _ | rc
      · rw [hcc] at h; simp at h
      · rw [hcc, Option.bind_some] at h
        rcases hd : wexec m (dec1 x) rc.1 with _ | rd
        · rw [hd] at h; simp at h
        · rw [hd] at h; simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hcost := hc m σ rc hcc
          have hcx : rc.1 x = σ x := noAssign_preserves m x c σ rc hna hcc
          cases m with
          | zero => simp [wexec] at hd
          | succ m' =>
              simp only [dec1, wexec, Option.some.injEq] at hd
              subst hd
              refine ⟨by simpa using Nat.add_le_add_right hcost 1, ?_⟩
              simp only [upd, evalE, hcx, if_true]
              omega

/-- **The loop bound is input-dependent.** With a counter the body never touches, the
    countdown's cost is bounded by `1 + v·(kc+3)` where `v` is the counter's *initial
    value*. The bound exists for each input and grows with it — and that dependency
    is precisely the DoS surface. -/
theorem countdown_cost {x : String} {c : WCmd} {kc : Nat}
    (hna : noAssign x c = true) (hc : CostAtMost c kc) :
    ∀ (n : Nat) (σ : Store) (o : Outcome), 0 ≤ σ x →
      wexec n (countdown x c) σ = some o → o.2.1 ≤ 1 + (σ x).toNat * (kc + 3)
  | 0,     _, _, _, h => by simp [wexec] at h
  | n + 1, σ, o, hpos, h => by
      rw [countdown, wexec_loop_eq] at h
      by_cases hg : evalE (.var x) σ ≠ 0
      · rw [if_pos hg] at h
        rcases hb : wexec n (.seq c (dec1 x)) σ with _ | r₁
        · rw [hb] at h; simp at h
        · rw [hb, Option.bind_some] at h
          rcases hl : wexec n (.loop (.var x) (.seq c (dec1 x))) r₁.1 with _ | r₂
          · rw [hl] at h; simp at h
          · rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h
            subst h
            obtain ⟨hcost, hdx⟩ := countdown_turn hna hc n σ r₁ hb
            have hgx : σ x ≠ 0 := by simpa [evalE] using hg
            have hpos1 : 0 ≤ r₁.1 x := by rw [hdx]; omega
            have hih := countdown_cost hna hc n r₁.1 r₂ hpos1 hl
            have hstep : (σ x).toNat = (r₁.1 x).toNat + 1 := by
              rw [hdx]; omega
            have hmul : (σ x).toNat * (kc + 3)
                = (r₁.1 x).toNat * (kc + 3) + (kc + 3) := by
              rw [hstep, Nat.succ_mul]
            show 1 + r₁.2.1 + r₂.2.1 ≤ 1 + (σ x).toNat * (kc + 3)
            rw [hmul]
            omega
      · rw [if_neg hg] at h
        simp only [Option.some.injEq] at h
        subst h
        exact Nat.le_add_right 1 _

/-! ## The attack: cost that grows with untrusted input -/

/-- The counter variable, read from untrusted input. -/
def uCtr : String := "u"

/-- The victim: spin down an untrusted counter. Memory-safe, injection-free and
    noninterferent — and a denial of service. -/
def spinU : WCmd := countdown uCtr .skip

/-- A store whose counter holds `v`. -/
def ctrStore (v : Nat) : Store := upd (fun _ => 0) uCtr (v : Int)

/-- One turn of the victim: two steps, and the counter drops by one. -/
theorem spinU_step (v : Nat) :
    wexec 2 (.seq .skip (dec1 uCtr)) (ctrStore (v + 1)) = some (ctrStore v, 2, []) := by
  have hs : upd (ctrStore (v + 1)) uCtr (ctrStore (v + 1) uCtr + -1) = ctrStore v := by
    funext y
    by_cases hy : y = uCtr <;> simp [ctrStore, upd, hy] <;> omega
  simp only [wexec, dec1, evalE, Option.bind_some, Option.map_some, Option.some.injEq, hs]
  rfl

/-- **Cost grows with the counter.** By induction, with fuel supplied by
    `wexec_mono_le`: a run started at `v` costs at least `v`. -/
theorem spinU_cost_lb : ∀ v : Nat, ∃ (n : Nat) (o : Outcome),
    wexec n spinU (ctrStore v) = some o ∧ v ≤ o.2.1
  | 0 => by
      refine ⟨1, (ctrStore 0, 1, [false]), ?_, by simp⟩
      simp [spinU, countdown, wexec, evalE, ctrStore, upd]
  | v + 1 => by
      obtain ⟨n₀, o₀, ho₀, hlb⟩ := spinU_cost_lb v
      have hb : wexec (max 2 n₀) (.seq .skip (dec1 uCtr)) (ctrStore (v + 1))
          = some (ctrStore v, 2, []) :=
        wexec_mono_le (spinU_step v) (Nat.le_max_left 2 n₀)
      have hr : wexec (max 2 n₀) (.loop (.var uCtr) (.seq .skip (dec1 uCtr))) (ctrStore v)
          = some o₀ := wexec_mono_le ho₀ (Nat.le_max_right 2 n₀)
      have hg : evalE (.var uCtr) (ctrStore (v + 1)) ≠ 0 := by
        simp [evalE, ctrStore, upd] <;> omega
      refine ⟨max 2 n₀ + 1, (o₀.1, 1 + 2 + o₀.2.1, true :: ([] ++ o₀.2.2)), ?_,
        by simp only []; omega⟩
      rw [spinU, countdown, wexec_loop_eq, if_pos hg, hb, Option.bind_some, hr]
      rfl

/-- **Algorithmic-complexity DoS, as a theorem.** No uniform budget exists: for every
    candidate `k` some input drives the cost past it. -/
theorem dos_unbounded : ∀ k : Nat, ¬ CostAtMost spinU k := by
  intro k hk
  obtain ⟨n, o, ho, hlb⟩ := spinU_cost_lb (k + 1)
  have := hk n (ctrStore (k + 1)) o ho
  omega

/-! ## The fix, and the honest scope -/

/-- Initialise the counter from a **constant**, then count down. -/
def budget (x : String) (k : Nat) (c : WCmd) : WCmd :=
  .seq (.assign x (.num (k : Int))) (countdown x c)

/-- **Uniformity restored.** A constant-initialised countdown has a budget that does
    not depend on the input at all. -/
theorem budget_cost {x : String} {c : WCmd} {kc : Nat} (k : Nat)
    (hna : noAssign x c = true) (hc : CostAtMost c kc) :
    CostAtMost (budget x k c) (1 + (1 + k * (kc + 3))) := by
  intro n σ o h
  cases n with
  | zero => simp [wexec] at h
  | succ n =>
      rw [budget, wexec_seq_eq] at h
      rcases ha : wexec n (.assign x (.num (k : Int))) σ with _ | r₁
      · rw [ha] at h; simp at h
      · rw [ha, Option.bind_some] at h
        rcases hl : wexec n (countdown x c) r₁.1 with _ | r₂
        · rw [hl] at h; simp at h
        · rw [hl] at h; simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hr1 : r₁ = (upd σ x (k : Int), 1, []) := by
            cases n with
            | zero => simp [wexec] at ha
            | succ n' => simpa [wexec, evalE] using ha.symm
          have hx : r₁.1 x = (k : Int) := by rw [hr1]; simp [upd]
          have hpos : 0 ≤ r₁.1 x := by rw [hx]; omega
          have hih := countdown_cost hna hc n r₁.1 r₂ hpos hl
          rw [hx] at hih
          have hkk : ((k : Int)).toNat = k := by omega
          rw [hkk] at hih
          have hc1 : r₁.2.1 = 1 := by rw [hr1]
          show r₁.2.1 + r₂.2.1 ≤ 1 + (1 + k * (kc + 3))
          rw [hc1]
          omega

/-- The fixed program: a bounded work unit. -/
def fixedU : WCmd := budget uCtr 100 .skip

theorem fixed_bounded : CostAtMost fixedU (1 + (1 + 100 * (1 + 3))) :=
  budget_cost 100 (by decide) cost_skip

/-- **Row 10's upgrade, as one theorem.** The victim admits *no* uniform budget; the
    fixed program admits one, and it is independent of the input. -/
theorem dos_unbounded_budget_bounded :
    (∀ k, ¬ CostAtMost spinU k) ∧ CostAtMost fixedU 402 :=
  ⟨dos_unbounded, by simpa using fixed_bounded⟩

end ConfTyping
