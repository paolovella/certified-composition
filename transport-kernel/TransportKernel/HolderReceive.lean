/-
  Second mathlib instance, deliberately a *different shape* of certificate.

  Lipschitz gave a scalar certificate (one `ℝ≥0`) accumulating by multiplication.
  Hölder continuity gives a **pair** certificate `(C, r) : ℝ≥0 × ℝ≥0` whose
  accumulation is NOT plain multiplication: `HolderWith.comp` composes them by

      (Cg, rg) ⋄ (Cf, rf) = (Cg · Cf ^ rg,  rg · rf)

  a semidirect-product-style monoid law, acting on distance by `C · d ^ r`.

  This is the instance that tests the review's point — the certificate need not be
  numeric. If the *same* generic `Bridge.comp` reconstructs `HolderWith.comp`
  under this non-scalar monoid, the interface is genuinely reusable across
  accumulation *algebras*, not just across objects with the same multiplication.
-/
import Mathlib.Topology.MetricSpace.Holder
import TransportKernel.LipschitzReceive   -- reuse the GradedAction/Bridge core

open NNReal ENNReal

namespace TransportKernel

/-- The Hölder graded action: certificate `(C, r) : ℝ≥0 × ℝ≥0` acting on extended
    distance by `C · d ^ r`, with the semidirect-product composition law. The
    `act_mul` proof is where the rpow algebra has to actually close. -/
noncomputable def holderGA : GradedAction (ℝ≥0 × ℝ≥0) ℝ≥0∞ where
  mul := fun a b => (a.1 * b.1 ^ (a.2 : ℝ), a.2 * b.2)
  le  := (· ≤ ·)
  act := fun c d => (c.1 : ℝ≥0∞) * d ^ (c.2 : ℝ)
  le_trans := le_trans
  act_mul := by
    rintro ⟨Cg, rg⟩ ⟨Cf, rf⟩ d
    dsimp only
    rw [ENNReal.mul_rpow_of_nonneg _ _ (NNReal.coe_nonneg rg),
        ← ENNReal.rpow_mul,
        ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ (NNReal.coe_nonneg rg),
        NNReal.coe_mul,
        mul_comm (rf : ℝ) (rg : ℝ),
        ← mul_assoc]
  act_mono := by
    rintro ⟨C, r⟩ d d' h
    dsimp only
    gcongr

/-- A `HolderWith C r f` hypothesis lands directly in the `contracts` slot:
    `edist (f x) (f y) ≤ C · edist x y ^ r` is exactly the certificate. -/
noncomputable def Bridge.ofHolder {X : Type} [PseudoEMetricSpace X]
    {C r : ℝ≥0} {f : X → X} (hf : HolderWith C r f) :
    Bridge X (ℝ≥0 × ℝ≥0) ℝ≥0∞ holderGA edist where
  map       := f
  cert      := (C, r)
  contracts := fun x y => hf x y

/-- **The reception, second instance.** The *same* generic `Bridge.comp` — now
    over the pair-certificate Hölder monoid — reconstructs mathlib's
    `HolderWith.comp`: the composite's certificate field is, definitionally, a
    proof of `HolderWith (Cg · Cf ^ rg) (rg · rf) (g ∘ f)`. Different certificate
    algebra, same accumulation machinery, no extra proof work. -/
theorem comp_reconstructs_holder {X : Type} [PseudoEMetricSpace X]
    {Cf rf Cg rg : ℝ≥0} {f g : X → X}
    (hg : HolderWith Cg rg g) (hf : HolderWith Cf rf f) :
    HolderWith (Cg * Cf ^ (rg : ℝ)) (rg * rf) (g ∘ f) :=
  ((Bridge.ofHolder hg).comp (Bridge.ofHolder hf)).contracts

end TransportKernel
