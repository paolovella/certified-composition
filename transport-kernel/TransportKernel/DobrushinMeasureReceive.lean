/-
  Tier-3b: the measure-theoretic Dobrushin contraction — the finite DPI
  (`DobrushinReceive.lean`) generalized to arbitrary measurable state spaces, stated
  against mathlib's own objects: `MeasureTheory.Measure`, `ProbabilityTheory.Kernel`,
  and the pushforward `κ ∘ₘ μ` (= `Measure.bind`).

  Mathlib has no total-variation distance between measures and no data-processing
  inequality, so both are built here. `tvDist` is the ℝ≥0∞-valued sup of the truncated
  excess `μ A - ν A` over measurable `A` (for probability measures this is the classical
  TV distance, and it is symmetric — `tvDist_comm`). The DPI (`tvDist_comp_le`) is the
  same coupling/overlap argument as the finite case, in additive form: Hahn-decompose
  the pair, form the Jordan parts as genuine measures `ξ⁺ ξ⁻` with `μ + ξ⁻ = ν + ξ⁺`,
  and run the averaging bound `m·(κ∘ₘξ⁺)A ≤ m·((κ∘ₘξ⁻)A + η·m)` — no Fubini, only
  constant integrals and monotonicity, all subtraction-free until the last step.

  The reception: the instance lands in the *same* graded action as Lipschitz (`lipGA`,
  ℝ≥0 acting on ℝ≥0∞), with `X = ProbabilityMeasure α` and `dist = tvDist`. The generic
  `Bridge.comp` then yields the submultiplicative bound `η(K)·η(L)` on the composed
  pushforward (`comp_reconstructs_dobrushin_measure`), and the same law holds at kernel
  level through mathlib's own kernel composition `∘ₖ` (`tvDist_kernel_comp_le`).
-/
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic
import TransportKernel.LipschitzReceive   -- GradedAction/Bridge core + lipGA

open MeasureTheory ProbabilityTheory NNReal ENNReal Set

namespace TransportKernel

variable {α : Type*} {mα : MeasurableSpace α}

/-! ## Total-variation distance for measures (absent from mathlib) -/

/-- Total-variation distance in `ℝ≥0∞`: the supremum over measurable sets of the
    (truncated) excess `μ A - ν A`. For probability measures this is symmetric
    (`tvDist_comm`) and equals the classical TV distance. -/
noncomputable def tvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A

theorem le_tvDist {μ ν : Measure α} {A : Set α} (hA : MeasurableSet A) :
    μ A - ν A ≤ tvDist μ ν :=
  le_iSup₂ (f := fun A (_ : MeasurableSet A) => μ A - ν A) A hA

/-- The additive (subtraction-free) form of the defining bound. -/
theorem apply_le_add_tvDist {μ ν : Measure α} {A : Set α} (hA : MeasurableSet A) :
    μ A ≤ ν A + tvDist μ ν :=
  tsub_le_iff_left.mp (le_tvDist hA)

@[simp] theorem tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_le_one (μ ν : Measure α) [IsProbabilityMeasure μ] : tvDist μ ν ≤ 1 :=
  iSup₂_le fun _ _ => tsub_le_self.trans prob_le_one

private theorem tvDist_le_symm (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : tvDist μ ν ≤ tvDist ν μ := by
  refine iSup₂_le fun A hA => tsub_le_iff_left.mpr ?_
  -- pass to complements: `ν Aᶜ ≤ μ Aᶜ + tvDist ν μ`, then cancel additively
  have h1 : μ A + ν Aᶜ ≤ μ A + μ Aᶜ + tvDist ν μ := by
    calc μ A + ν Aᶜ ≤ μ A + (μ Aᶜ + tvDist ν μ) :=
          add_le_add_right (apply_le_add_tvDist hA.compl) _
      _ = μ A + μ Aᶜ + tvDist ν μ := by ring
  rw [measure_add_measure_compl hA, measure_univ,
      ← measure_univ (μ := ν), ← measure_add_measure_compl (μ := ν) hA] at h1
  have h2 : μ A + ν Aᶜ ≤ (ν A + tvDist ν μ) + ν Aᶜ := by
    calc μ A + ν Aᶜ ≤ ν A + ν Aᶜ + tvDist ν μ := h1
      _ = (ν A + tvDist ν μ) + ν Aᶜ := by ring
  exact (ENNReal.add_le_add_iff_right (measure_ne_top ν Aᶜ)).mp h2

/-- For probability measures the one-sided sup is symmetric — it *is* the TV distance. -/
theorem tvDist_comm (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = tvDist ν μ :=
  le_antisymm (tvDist_le_symm μ ν) (tvDist_le_symm ν μ)

/-! ## The data-processing inequality, measure-theoretic form -/

/-- **The Dobrushin data-processing inequality for Markov kernels on a measurable
    space.** If every pair of kernel measures is within TV `η`, the pushforward
    `κ ∘ₘ ·` contracts TV distance by `η`. The proof is the finite coupling argument in
    additive integral form: Hahn-decompose `(μ, ν)` by `s`, form the Jordan parts
    `ξ⁺ = (μ - ν)|_s` and `ξ⁻ = (ν - μ)|_{sᶜ}` as measures with common mass `m` and
    `μ + ξ⁻ = ν + ξ⁺`, then bound `m·(κ∘ₘξ⁺)A ≤ m·((κ∘ₘξ⁻)A + η·m)` by averaging the
    pointwise bound `κ x A ≤ κ y A + η` — constant integrals only, no Fubini. -/
theorem tvDist_comp_le (κ : Kernel α α) [IsMarkovKernel κ] {η : ℝ≥0∞}
    (hη : ∀ x y, tvDist (κ x) (κ y) ≤ η)
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ η * tvDist μ ν := by
  obtain ⟨s, hs, hsle, hsge⟩ := hahn_decomposition μ ν
  haveI : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.mpr (measure_ne_top ν s)
  haveI : IsFiniteMeasure (μ.restrict sᶜ) := isFiniteMeasure_restrict.mpr (measure_ne_top μ sᶜ)
  -- Jordan parts of `μ − ν`, as genuine measures
  set ξp : Measure α := μ.restrict s - ν.restrict s with hξp
  set ξm : Measure α := ν.restrict sᶜ - μ.restrict sᶜ with hξm
  have hres_le : ν.restrict s ≤ μ.restrict s := by
    refine Measure.le_iff.mpr fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact hsle _ (hA.inter hs) inter_subset_right
  have hres_le' : μ.restrict sᶜ ≤ ν.restrict sᶜ := by
    refine Measure.le_iff.mpr fun A hA => ?_
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact hsge _ (hA.inter hs.compl) inter_subset_right
  -- the additive Jordan identity (no truncated subtraction at measure level)
  have hJordan : μ + ξm = ν + ξp := by
    have h1 : ξp + ν.restrict s = μ.restrict s := Measure.sub_add_cancel_of_le hres_le
    have h2 : ξm + μ.restrict sᶜ = ν.restrict sᶜ := Measure.sub_add_cancel_of_le hres_le'
    calc μ + ξm = μ.restrict s + μ.restrict sᶜ + ξm := by
          rw [Measure.restrict_add_restrict_compl hs]
      _ = μ.restrict s + (ξm + μ.restrict sᶜ) := by abel
      _ = μ.restrict s + ν.restrict sᶜ := by rw [h2]
      _ = ξp + ν.restrict s + ν.restrict sᶜ := by rw [h1]
      _ = ν.restrict s + ν.restrict sᶜ + ξp := by abel
      _ = ν + ξp := by rw [Measure.restrict_add_restrict_compl hs]
  -- the common Jordan mass `m`
  set m : ℝ≥0∞ := ξp univ with hm
  have hmtop : m ≠ ∞ := by
    rw [hm]
    have h1 : ξp univ ≤ μ univ :=
      Measure.le_iff'.mp (Measure.sub_le.trans Measure.restrict_le_self) univ
    exact ((h1.trans_eq measure_univ).trans_lt one_lt_top).ne
  have hmass : ξm univ = m := by
    have h := congrArg (fun ρ : Measure α => ρ univ) hJordan
    simp only [Measure.add_apply, measure_univ] at h
    rw [hm]
    exact (ENNReal.add_right_inj one_ne_top).mp h
  have hm_le : m ≤ tvDist μ ν := by
    have h1 : ξp univ = μ s - ν s := by
      rw [hξp, Measure.sub_apply MeasurableSet.univ hres_le,
          Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    calc m = μ s - ν s := by rw [hm, h1]
      _ ≤ tvDist μ ν := le_tvDist hs
  -- the coupling/averaging bound on the pushed Jordan parts
  have key : ∀ A, MeasurableSet A → (κ ∘ₘ ξp) A ≤ (κ ∘ₘ ξm) A + η * m := by
    intro A hA
    rcases eq_or_ne m 0 with hm0 | hm0
    · have hz : ξp = 0 := Measure.measure_univ_eq_zero.mp (hm.symm.trans hm0)
      rw [hz]
      simp
    · -- pointwise Dobrushin bound between any two kernel measures
      have hpoint : ∀ x y, κ x A ≤ κ y A + η := fun x y =>
        tsub_le_iff_left.mp ((le_tvDist hA).trans (hη x y))
      -- for every `y`, the pushed positive part is at most `(κ y A + η) · m`
      have hint : ∀ y, (κ ∘ₘ ξp) A ≤ (κ y A + η) * m := by
        intro y
        rw [Measure.bind_apply hA κ.aemeasurable]
        calc ∫⁻ x, κ x A ∂ξp ≤ ∫⁻ _, κ y A + η ∂ξp := lintegral_mono fun x => hpoint x y
          _ = (κ y A + η) * m := by rw [lintegral_const, ← hm]
      -- average over `y ∂ξm` and cancel `m`
      have hstep : m * ((κ ∘ₘ ξp) A) ≤ m * ((κ ∘ₘ ξm) A + η * m) := by
        calc m * ((κ ∘ₘ ξp) A) = (κ ∘ₘ ξp) A * m := mul_comm _ _
          _ = ∫⁻ _, (κ ∘ₘ ξp) A ∂ξm := by rw [lintegral_const, hmass]
          _ ≤ ∫⁻ y, (κ y A + η) * m ∂ξm := lintegral_mono fun y => hint y
          _ = (∫⁻ y, κ y A + η ∂ξm) * m :=
              lintegral_mul_const _ ((κ.measurable_coe hA).add_const _)
          _ = ((κ ∘ₘ ξm) A + η * m) * m := by
              rw [lintegral_add_right _ measurable_const, lintegral_const, hmass,
                  Measure.bind_apply hA κ.aemeasurable]
          _ = m * ((κ ∘ₘ ξm) A + η * m) := mul_comm _ _
      exact (ENNReal.mul_le_mul_iff_right hm0 hmtop).mp hstep
  -- assemble: evaluate the pushed Jordan identity and cancel the finite part
  refine iSup₂_le fun A hA => tsub_le_iff_left.mpr ?_
  have hbind : (κ ∘ₘ μ) A + (κ ∘ₘ ξm) A = (κ ∘ₘ ν) A + (κ ∘ₘ ξp) A := by
    have h : κ ∘ₘ (μ + ξm) = κ ∘ₘ (ν + ξp) := by rw [hJordan]
    rw [Measure.comp_add, Measure.comp_add] at h
    exact congrArg (fun ρ : Measure α => ρ A) h
  have hfin : (κ ∘ₘ ξm) A ≠ ∞ := by
    have h1 : (κ ∘ₘ ξm) A ≤ (κ ∘ₘ ξm) univ := measure_mono (subset_univ A)
    rw [Measure.comp_apply_univ, hmass] at h1
    exact (h1.trans_lt hmtop.lt_top).ne
  have hchain : (κ ∘ₘ μ) A + (κ ∘ₘ ξm) A ≤ ((κ ∘ₘ ν) A + η * m) + (κ ∘ₘ ξm) A := by
    rw [hbind]
    calc (κ ∘ₘ ν) A + (κ ∘ₘ ξp) A
        ≤ (κ ∘ₘ ν) A + ((κ ∘ₘ ξm) A + η * m) := add_le_add_right (key A hA) _
      _ = ((κ ∘ₘ ν) A + η * m) + (κ ∘ₘ ξm) A := by ring
  have hημ : (κ ∘ₘ μ) A ≤ (κ ∘ₘ ν) A + η * m :=
    (ENNReal.add_le_add_iff_right hfin).mp hchain
  exact hημ.trans (add_le_add_right (mul_le_mul_right hm_le η) _)

/-- Dobrushin submultiplicativity through mathlib's own kernel composition `∘ₖ`:
    `η(K ∘ₖ L) ≤ η(K)·η(L)` — the certificate-level law, before any interface. -/
theorem tvDist_kernel_comp_le (K L : Kernel α α) [IsMarkovKernel K] [IsMarkovKernel L]
    {ηK ηL : ℝ≥0∞}
    (hK : ∀ x y, tvDist (K x) (K y) ≤ ηK) (hL : ∀ x y, tvDist (L x) (L y) ≤ ηL)
    (x y : α) : tvDist ((K ∘ₖ L) x) ((K ∘ₖ L) y) ≤ ηK * ηL := by
  rw [Kernel.comp_apply, Kernel.comp_apply]
  calc tvDist (K ∘ₘ (L x)) (K ∘ₘ (L y)) ≤ ηK * tvDist (L x) (L y) :=
        tvDist_comp_le K hK _ _
    _ ≤ ηK * ηL := mul_le_mul_right (hL x y) _

/-! ## The reception: a Markov kernel IS a certified bridge, in the SAME graded
    action as Lipschitz (`lipGA` — ℝ≥0 coefficients acting on ℝ≥0∞ distances) -/

variable {Ω : Type} [MeasurableSpace Ω]

/-- **A Markov kernel on a measurable space is a certified bridge.** Its Dobrushin
    coefficient `η` (any bound on pairwise TV of the kernel measures) is the
    certificate, `κ ∘ₘ ·` the map, the measure-theoretic DPI the contraction proof —
    and the graded action is `lipGA`, the same one mathlib's Lipschitz maps landed in. -/
noncomputable def Bridge.ofMarkovKernel (κ : Kernel Ω Ω) [IsMarkovKernel κ] (η : ℝ≥0)
    (hη : ∀ x y, tvDist (κ x) (κ y) ≤ (η : ℝ≥0∞)) :
    Bridge (ProbabilityMeasure Ω) ℝ≥0 ℝ≥0∞ lipGA
      (fun μ ν => tvDist (μ : Measure Ω) (ν : Measure Ω)) where
  map       := fun μ => ⟨κ ∘ₘ (μ : Measure Ω), inferInstance⟩
  cert      := η
  contracts := fun μ ν => tvDist_comp_le κ hη (μ : Measure Ω) (ν : Measure Ω)

/-- **Advanced composition is certificate accumulation, on continuous state spaces.**
    The generic `Bridge.comp` applied to two Markov-kernel bridges yields the
    submultiplicative Dobrushin bound `η(K)·η(L)` on the iterated pushforward — the
    measure-theoretic analogue of `comp_reconstructs_dobrushin`, with no
    kernel-specific proof. -/
theorem comp_reconstructs_dobrushin_measure (K L : Kernel Ω Ω)
    [IsMarkovKernel K] [IsMarkovKernel L] (ηK ηL : ℝ≥0)
    (hK : ∀ x y, tvDist (K x) (K y) ≤ (ηK : ℝ≥0∞))
    (hL : ∀ x y, tvDist (L x) (L y) ≤ (ηL : ℝ≥0∞))
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (K ∘ₘ (L ∘ₘ μ)) (K ∘ₘ (L ∘ₘ ν)) ≤ ((ηK * ηL : ℝ≥0) : ℝ≥0∞) * tvDist μ ν :=
  ((Bridge.ofMarkovKernel K ηK hK).comp (Bridge.ofMarkovKernel L ηL hL)).contracts
    ⟨μ, inferInstance⟩ ⟨ν, inferInstance⟩

end TransportKernel
