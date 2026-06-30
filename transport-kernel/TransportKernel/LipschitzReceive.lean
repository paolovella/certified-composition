/-
  Tier-2 test: does the corrected genus RECEIVE a real mathlib instance?

  The `GradedAction`/`Bridge` core is re-stated here (mathlib-free, ~25 lines —
  canonical home is the `transport-calculus` repo) so this repo can plug it into
  mathlib's actual `LipschitzWith`. The point is the last theorem: the generic
  `Bridge.comp` *reconstructs* `LipschitzWith.comp` — the instance mathlib hands
  us fits the interface, and the interface's accumulation law reproduces the
  library's own composition law. ℝ≥0 acts on ℝ≥0∞: grade ≠ distance, the `M ≠ D`
  separation the eighth catch forced, now exercised by the object that forced it.
-/
import Mathlib.Topology.EMetricSpace.Lipschitz

open NNReal ENNReal

namespace TransportKernel

/-! ## The genus core (re-stated; canonical = transport-calculus, mathlib-free) -/

structure GradedAction (M : Type) (D : Type) where
  mul      : M → M → M
  le       : D → D → Prop
  act      : M → D → D
  le_trans : ∀ {a b c}, le a b → le b c → le a c
  act_mul  : ∀ m₁ m₂ d, act (mul m₁ m₂) d = act m₁ (act m₂ d)
  act_mono : ∀ (m : M) {d d' : D}, le d d' → le (act m d) (act m d')

structure Bridge (X M D : Type) (GA : GradedAction M D) (dist : X → X → D) where
  map       : X → X
  cert      : M
  contracts : ∀ x y, GA.le (dist (map x) (map y)) (GA.act cert (dist x y))

def Bridge.comp {X M D : Type} {GA : GradedAction M D} {dist : X → X → D}
    (g f : Bridge X M D GA dist) : Bridge X M D GA dist where
  map   := g.map ∘ f.map
  cert  := GA.mul g.cert f.cert
  contracts := fun x y => by
    have h1 := g.contracts (f.map x) (f.map y)
    have h2 := GA.act_mono g.cert (f.contracts x y)
    have h3 := GA.le_trans h1 h2
    rw [← GA.act_mul] at h3
    exact h3

/-! ## The real instance: ℝ≥0 acting on ℝ≥0∞ (grade ≠ distance) -/

/-- The graded action mathlib's metric world actually has: contraction constants
    in `ℝ≥0` act on extended distances in `ℝ≥0∞` by (coerced) multiplication.
    This is the `M ≠ D` structure — and the coercion `ℝ≥0 ↪ ℝ≥0∞` is exactly the
    bridge that let the degenerate `Nat` (`M = D`) version fit without refutation. -/
noncomputable def lipGA : GradedAction ℝ≥0 ℝ≥0∞ where
  mul      := (· * ·)
  le       := (· ≤ ·)
  act      := fun k d => (k : ℝ≥0∞) * d
  le_trans := le_trans
  act_mul  := fun k₁ k₂ d => by rw [ENNReal.coe_mul, mul_assoc]
  act_mono := by intro k d d' h; gcongr

/-- A `LipschitzWith` map IS a certified bridge: its defining inequality
    `edist (f x) (f y) ≤ K * edist x y` is exactly `contracts`. No proof work —
    the library hypothesis lands directly in the interface's certificate slot. -/
noncomputable def Bridge.ofLipschitz {X : Type} [PseudoEMetricSpace X]
    {K : ℝ≥0} {f : X → X} (hf : LipschitzWith K f) :
    Bridge X ℝ≥0 ℝ≥0∞ lipGA edist where
  map       := f
  cert      := K
  contracts := fun x y => hf x y

/-- **The reception, made a theorem.** The generic `Bridge.comp` applied to two
    Lipschitz bridges *reconstructs* mathlib's `LipschitzWith.comp`: the
    composite's certificate field is, definitionally, a proof of
    `LipschitzWith (Kf * Kg) (f ∘ g)`. The interface receives the real instance
    and reproduces the library's composition law from generic accumulation. -/
theorem comp_reconstructs_lipschitz {X : Type} [PseudoEMetricSpace X]
    {Kf Kg : ℝ≥0} {f g : X → X}
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (Kf * Kg) (f ∘ g) :=
  ((Bridge.ofLipschitz hf).comp (Bridge.ofLipschitz hg)).contracts

end TransportKernel
