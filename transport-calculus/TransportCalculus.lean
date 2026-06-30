/-
  The transport calculus — a common interface for transport theorems, with its composition law.

  A certified transport morphism (`Bridge`) is a map bundled with a *certificate*:
  a grade `c` and a proof that the map contracts the ambient distance by `c`.
  Composition is composition *of certificates*: it MULTIPLIES the grades and
  threads the two contraction proofs into the composite's — accumulation is the
  primitive, never silent discharge.

  ── Eighth catch, delivered by a real instance (not by me) ──
  v1 of this file used a single type `G` for both the grade and the distance,
  with one `mul : G → G → G`. That was over-identification: mathlib's actual
  `LipschitzWith` carries grades in `ℝ≥0` and distances in `ℝ≥0∞` — TWO types,
  the certificate a scalar *action* of the grade on the distance. The `Nat`
  instance hid this because there grade and distance coincide (`M = D`). The
  real instance does not *refute* the single-type version (it fits via the
  coercion `ℝ≥0 ↪ ℝ≥0∞`) — it reveals the conflation. The faithful structure,
  below, separates a grade monoid `M` acting monotonically on a distance order
  `D`; `Nat` is recovered as the degenerate `M = D` coincidence.

  Mathlib-free, by design: the corrected interface compiles with no reals and no
  measure theory, so that structure is incidental to it. The Markov-kernel /
  Dobrushin instance (`M = ℝ≥0`, `D = ℝ≥0∞`, `act = ↑· * ·`, contraction = the
  strong data-processing inequality — not in mathlib, a real formalization) is a
  separate artifact; the interface here only has to *receive* it.
-/

namespace TransportCalculus

/-- The earned abstraction, corrected by contact with `LipschitzWith`: a grade
    monoid `M` acting on a distance order `D`. Exactly what `Bridge.comp` uses —
    grade composition `mul`, a monotone action `act`, transitivity. No addition,
    no triangle inequality, no identity, no `M = D`. A bundle passed explicitly,
    so the operations the proof needs are visible and nothing is conflated. -/
structure GradedAction (M : Type) (D : Type) where
  mul      : M → M → M                                   -- grade composition
  le       : D → D → Prop                                -- distance order
  act      : M → D → D                                   -- a grade scales a distance
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  act_mul  : ∀ m₁ m₂ d, act (mul m₁ m₂) d = act m₁ (act m₂ d)
  act_mono : ∀ (m : M) {d d' : D}, le d d' → le (act m d) (act m d')

/-- A **certified transport morphism**: a map, a grade `cert : M`, and a
    certificate that the map contracts the distance `dist : X → X → D` by the
    *action* of `cert`. The map bundled with its hypotheses, not the map alone. -/
structure Bridge (X M D : Type) (GA : GradedAction M D) (dist : X → X → D) where
  map       : X → X
  cert     : M
  contracts : ∀ x y, GA.le (dist (map x) (map y)) (GA.act cert (dist x y))

/-- **The composition law.** Composing two certified bridges yields
    a certified bridge whose grade is the *product* of the two, and whose
    contraction proof is *threaded from* the two inputs via the action's
    compatibility `act_mul` and monotonicity. Drop the multiplication and the
    certificate no longer type-checks. -/
def Bridge.comp {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) : Bridge X M D GA dist where
  map   := g.map ∘ f.map
  cert := GA.mul g.cert f.cert
  contracts := fun x y => by
    have h1 := g.contracts (f.map x) (f.map y)
    have h2 := GA.act_mono g.cert (f.contracts x y)
    have h3 := GA.le_trans h1 h2
    rw [← GA.act_mul] at h3
    exact h3

/-- The composite's grade is exactly the product — accumulation, definitionally. -/
theorem Bridge.comp_cert {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) :
    (g.comp f).cert = GA.mul g.cert f.cert := rfl

/-! ## The degenerate instance that hid the conflation: `M = D = Nat`

Distance `|a-b|`, grade = Lipschitz constant — *both* `Nat`, the action *is*
multiplication. This is the `M = D` coincidence. The doubling map is Lipschitz-2;
two compose to Lipschitz-4, the grade multiplied, by `rfl`. -/

def natGA : GradedAction Nat Nat where
  mul      := Nat.mul
  le       := Nat.le
  act      := Nat.mul
  le_trans := Nat.le_trans
  act_mul  := Nat.mul_assoc
  act_mono := fun m {_ _} h => Nat.mul_le_mul (Nat.le_refl m) h

def dist (a b : Nat) : Nat := (a - b) + (b - a)

def double : Bridge Nat Nat Nat natGA dist where
  map   := fun n => 2 * n
  cert := 2
  contracts := fun x y => by
    show dist (2 * x) (2 * y) ≤ 2 * dist x y
    unfold dist
    omega

/-- Accumulation, concretely: two Lipschitz-2 bridges compose to Lipschitz-4. -/
example : (double.comp double).cert = 4 := rfl

end TransportCalculus
