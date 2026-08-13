/-
  Stage F — bounded guarantees as grades, and the first grade that does not factor.

  Alloy's `check A for 4 AbacPolicy, 3 Attribute`, CBMC's unwinding depth, TLC's
  finite instance: three tools, one shape. **A guarantee quantified by a budget.**
  The assurance-case literature handles these by downgrading them to *confidence*
  ("complement the incomplete result with testing"); this module asks the
  algebraic question instead — what is the composite of two bounded guarantees?

  ── The tempting answer, and why it is wrong ──
  The obvious rule is `min`: if `f` is safe to bound 80 and `g` to bound 10, the
  composite is safe to 10. **`min` is unsound, and not marginally.**
  `min_unsound` exhibits `f x = x + 20` and `g` well-behaved only below 10: the
  rule claims safety up to 10 and the composite fails at *every* input, including
  size 0. There is no bound at all for which the composite is safe.

  The reason is that `f` **grows the state past `g`'s bound**. A bounded
  certificate that reports only its bound has thrown away the thing the next
  composition step needs.

  ── The grade is a pair ──
  `BGrade` carries `(bound, growth)`, and `bmul` composes them:

      bmul ⟨b₂, g₂⟩ ⟨b₁, g₁⟩ = ⟨min b₁ (b₂ - g₁), g₁ + g₂⟩

  `bounded_comp_sound` proves this is sound, and — this is what the encoding
  buys — **with no side condition**. The bound is stored *strictly*: `b` means
  "every state of size `< b`", so `b = 0` is the vacuous certificate and Nat's
  truncated subtraction lands exactly on it when the growth overruns. An earlier
  formulation with `Option Nat` and a `g₁ ≤ b₂` guard proves the same theorem with
  a hypothesis and eight case splits; the shift removes both.

  ── The result that matters: this grade does not factor ──
  Every certificate in this repo so far has been carryable *componentwise*.
  `Bridge.pair_comp_cert` is the free-lunch theorem: bundle `n` guarantees, pay
  `n` independent accumulations, no interaction term. Stage 1j already found that
  two properties cannot always be *derived* independently
  (`ni_and_memory_do_not_factor`), while insisting that bundling the results stays
  free.

  **`bounded_grade_does_not_factor` breaks that second half.** The composite bound
  is provably *not a function of the two bounds*: it reads the inner certificate's
  **growth**. Two grade pairs with identical bounds and different growths compose
  to different bounds. So a bounded certificate cannot be presented as a product
  of an independent bound-certificate and an independent growth-certificate, and
  `pair_comp_cert` — which is true — simply does not cover it.

  That is a genuine limit on the repo's central claim, found by the first example
  that was not built to fit it. The taxonomy now has three kinds of component:

  * **contracting** (Lipschitz, Dobrushin, cost, growth) — acts on the distance;
  * **inert** (the ledger) — rides along, `act` ignores it (`ledger_act_phantom`);
  * **coupled** (the bound) — ignored by `act`, but its *composition reads another
    component*. New here, and the reason `min` looked plausible.

  ── Scope ──
  `GrowsBy` is a **constant** growth bound. Input-dependent growth needs the grade
  to carry a monotone map rather than a number — which is `universalGA`'s `Mono`,
  already in `TransportCalculus`, and is the named follow-on. Nothing here is
  transcribed from Alloy or CBMC; this is the algebra, and stage E's census is
  what would connect it to real emitted bounds.
-/
import ConfTyping.CNReceive

namespace ConfTyping

open TransportCalculus

/-! ## Bounded guarantees

A certificate that holds only below a budget, and the growth that budget must
survive. -/

/-- **The bounded guarantee.** `f` preserves `P` on every state *strictly* below
    `b`. The strictness is the encoding trick: `b = 0` certifies nothing, so the
    vacuous certificate is representable and Nat subtraction lands on it. -/
def BSafe {X : Type} (size : X → Nat) (P : X → Prop) (f : X → X) (b : Nat) : Prop :=
  ∀ x, size x < b → P x → P (f x)

/-- **What a bounded certificate must also report.** `f` inflates the size
    measure by at most `k`. Without this the next composition step is blind. -/
def GrowsBy {X : Type} (size : X → Nat) (f : X → X) (k : Nat) : Prop :=
  ∀ x, size (f x) ≤ size x + k

/-- The vacuous certificate is free, and says nothing. -/
theorem bsafe_zero {X : Type} (size : X → Nat) (P : X → Prop) (f : X → X) :
    BSafe size P f 0 := by
  intro x hx
  exact absurd hx (Nat.not_lt_zero _)

/-- Bounds weaken downwards. -/
theorem bsafe_mono {X : Type} {size : X → Nat} {P : X → Prop} {f : X → X}
    {b b' : Nat} (h : BSafe size P f b) (hle : b' ≤ b) : BSafe size P f b' :=
  fun x hx => h x (Nat.lt_of_lt_of_le hx hle)

/-! ## The counterexample: `min` is unsound

Concrete, and the failure is total rather than marginal. -/

/-- The safety property: stay below 100. -/
def bP (x : Nat) : Prop := x ≤ 100

/-- Grows the state by 20. -/
def bF (x : Nat) : Nat := x + 20

/-- Well-behaved only below 10 — above it, it explodes. -/
def bG (y : Nat) : Nat := if y ≤ 10 then y else 1000

theorem bF_safe : BSafe id bP bF 81 := by
  intro x hx hp
  simp only [bP, bF, id] at *
  omega

theorem bF_grows : GrowsBy id bF 20 := by
  intro x; simp [bF, id]

theorem bG_safe : BSafe id bP bG 11 := by
  intro y hy hp
  simp only [bP, bG, id] at *
  rw [if_pos (by omega)]
  omega

/-- **`min` is unsound.** Both parts are certified — `f` to 81, `g` to 11 — and
    the `min` rule claims the composite is safe below 11. It is not: the composite
    fails at **0**, the smallest state there is. `f` pushes the state to 20, which
    is outside `g`'s certified region, and `g`'s certificate never spoke about it.

    Note what makes this bite: neither certificate is wrong, and neither tool made
    an error. The rule that combined them threw away the growth. -/
theorem min_unsound :
    BSafe id bP bF 81 ∧ BSafe id bP bG 11
    ∧ ¬ BSafe id bP (bG ∘ bF) (min 81 11) := by
  refine ⟨bF_safe, bG_safe, ?_⟩
  intro h
  have h0 : id (0 : Nat) < min 81 11 := by decide
  have hp : bP 0 := by simp [bP]
  have hbad : ¬ bP ((bG ∘ bF) 0) := by simp [bP, Function.comp, bF, bG]
  exact absurd (h 0 h0 hp) hbad

/-! ## The grade that works -/

/-- A bounded certificate's grade: the budget it is valid below, and the growth
    it inflicts. -/
structure BGrade where
  /-- Valid on every state of size **strictly** below this. `0` is vacuous. -/
  bound  : Nat
  /-- Inflates the size measure by at most this. -/
  growth : Nat
deriving DecidableEq, Repr

/-- **The composition law.** Outer `∘` inner, matching `Bridge.comp g f`. The
    inner certificate's growth is subtracted from the outer's budget; truncated
    subtraction delivers the vacuous grade exactly when the growth overruns. -/
def bmul (o i : BGrade) : BGrade :=
  ⟨min i.bound (o.bound - i.growth), i.growth + o.growth⟩

/-- **Soundness, with no side condition.** Composing two bounded certificates
    yields a bounded certificate at `min b₁ (b₂ - g₁)`. The `g₁ > b₂` case is not
    excluded by hypothesis — it lands on the vacuous grade by arithmetic. -/
theorem bounded_comp_sound {X : Type} {size : X → Nat} {P : X → Prop}
    {f g : X → X} {b₁ b₂ g₁ : Nat}
    (hf : BSafe size P f b₁) (hg : BSafe size P g b₂) (hgrow : GrowsBy size f g₁) :
    BSafe size P (g ∘ f) (bmul ⟨b₂, 0⟩ ⟨b₁, g₁⟩).bound := by
  intro x hx hPx
  simp only [bmul] at hx
  have hfx : P (f x) := hf x (by omega) hPx
  have hsize : size (f x) < b₂ := by
    have := hgrow x
    omega
  exact hg (f x) hsize hfx

/-- **The monoid.** `bmul` is associative — checked here, and consistent with an
    exhaustive search over 42 875 triples before it was proved. -/
theorem bmul_assoc (a b c : BGrade) : bmul (bmul a b) c = bmul a (bmul b c) := by
  simp only [bmul, BGrade.mk.injEq]
  constructor <;> omega

/-! ## The law is tight, not merely sound

A composition law that always answered "nothing certified" would satisfy
`bounded_comp_sound` and be worthless. On the counterexample's own machinery,
with the growth reduced until it fits, the law returns a bound that is **exactly
right** — safe one below it, and broken at it. -/

/-- The same shape as `bF`, growing by 3 instead of 20. -/
def bF3 (x : Nat) : Nat := x + 3

theorem bF3_safe : BSafe id bP bF3 81 := by
  intro x hx hp
  simp only [bP, bF3, id] at *
  omega

theorem bF3_grows : GrowsBy id bF3 3 := by
  intro x; simp [bF3, id]

/-- The law's answer here is `min 81 (11 - 3) = 8`. -/
theorem bounded_comp_gives_eight : (bmul ⟨11, 0⟩ ⟨81, 3⟩).bound = 8 := by
  simp [bmul]

/-- **Tight.** The composite really is safe below 8, and really does break at 8 —
    `bF3` pushes 8 to 11, one step outside `bG`'s certified region. The law is
    not being conservative to buy its soundness. -/
theorem bounded_comp_tight :
    BSafe id bP (bG ∘ bF3) 8 ∧ ¬ BSafe id bP (bG ∘ bF3) 9 := by
  constructor
  · have h := bounded_comp_sound (size := id) (P := bP) bF3_safe bG_safe bF3_grows
    simpa [bmul] using h
  · intro h
    have h8 : id (8 : Nat) < 9 := by decide
    have hp : bP 8 := by simp [bP]
    have hbad : ¬ bP ((bG ∘ bF3) 8) := by simp [bP, Function.comp, bF3, bG]
    exact absurd (h 8 h8 hp) hbad

/-! ## `min` is right exactly when nothing grows -/

/-- The condition that rescues the tempting rule: a size-non-increasing artifact
    composes by `min`, and that is the whole of when it is safe to think in
    bounds alone. -/
theorem min_sound_when_nongrowing (b₁ b₂ : Nat) :
    (bmul ⟨b₂, 0⟩ ⟨b₁, 0⟩).bound = min b₁ b₂ := by
  simp [bmul]

/-! ## The finding: this grade does not factor

`Bridge.pair_comp_cert` says bundled certificates accumulate componentwise with
no interaction term. It is true, and it does not apply here. -/

/-- **The composite bound is not a function of the two bounds.** Same bounds,
    different growth, different answer — so no `mulB : Nat → Nat → Nat` can
    reproduce `bmul`'s bound component, and a bounded certificate cannot be
    carried as a product of an independent bound and an independent growth.

    This is the first place in this repo where the *composition* of a bundle is
    genuinely coupled. Stage 1j found two properties that cannot be **derived**
    independently while bundling stayed free; this is the other half. -/
theorem bounded_grade_does_not_factor :
    ¬ ∃ mulB : Nat → Nat → Nat,
        ∀ a b : BGrade, (bmul a b).bound = mulB a.bound b.bound := by
  rintro ⟨mulB, h⟩
  have h1 := h ⟨5, 0⟩ ⟨5, 0⟩
  have h2 := h ⟨5, 0⟩ ⟨5, 3⟩
  simp only [bmul] at h1 h2
  omega

/-- Spelled out, so the mechanism is visible rather than inferred: identical
    bounds, growth 0 versus 3, composite bounds 5 versus 2. -/
theorem bounded_coupling_witness :
    (bmul ⟨5, 0⟩ ⟨5, 0⟩).bound = 5 ∧ (bmul ⟨5, 0⟩ ⟨5, 3⟩).bound = 2 := by
  constructor <;> simp [bmul]

/-! ## Where it does fit: growth is an ordinary contracting grade

The bound is coupled, but the growth half is exactly the repo's existing shape —
`act` on the size measure, composing by addition, like cost budgets. So the
bounded certificate is a `GradedAction` in which the bound rides as a **phantom
that is not inert**: `act` ignores it (as `act` ignores the ledger), yet `mul`
reads the other component (as `mul` never reads across the ledger). -/

/-- The bounded graded action: the action inflates a size by the growth; the
    bound rides along. -/
def boundedGA : GradedAction BGrade Nat where
  mul      := bmul
  le       := (· ≤ ·)
  act      := fun m d => d + m.growth
  le_trans := fun h₁ h₂ => Nat.le_trans h₁ h₂
  act_mul  := by intro m₁ m₂ d; simp only [bmul]; omega
  act_mono := by intro m d d' h; omega

/-- The action sees only the growth — the bound is phantom in it. -/
theorem bounded_act_phantom (b g d : Nat) :
    boundedGA.act ⟨b, g⟩ d = d + g := rfl

/-- **But the phantom is not inert.** `ledger_act_phantom`'s ledger is ignored by
    `act` *and* composes without reading anything else. The bound is ignored by
    `act` and **does** read the other component, which is exactly the difference
    `bounded_grade_does_not_factor` makes precise. -/
theorem bounded_phantom_not_inert :
    (boundedGA.mul ⟨5, 0⟩ ⟨5, 0⟩).bound ≠ (boundedGA.mul ⟨5, 0⟩ ⟨5, 3⟩).bound := by
  simp [boundedGA, bmul]

end ConfTyping
