/-
  The discretization consistency lemma — the loop between the two Dobrushin
  developments, closed.

  `DobrushinReceive.lean` proves the DPI for finite distributions (`Dist S`, real-valued
  `tvd = ½∑|·|`); `DobrushinMeasureReceive.lean` proves it for mathlib measures
  (`tvDist`, the ℝ≥0∞-valued sup). Until now the two notions were proved equal in no
  theorem. This file supplies the bridge:

  - `Dist.toMeasure` — a finite distribution as a measure (sum of weighted Diracs),
    over any discrete measurable structure on `S`;
  - `tvDist_toMeasure` — **the consistency lemma**: `tvDist μ° ν° = ofReal (tvd μ ν)`,
    proved by showing the defining sup is attained on `{s | ν s ≤ μ s}`;
  - `Kernel.toMKernel`, `toMeasure_push` — a stochastic matrix as a mathlib Markov
    kernel, with the finite pushforward matching `κ ∘ₘ ·` under the embedding;
  - `dpi_via_measure` — the payoff: the finite DPI re-derived as a *corollary* of the
    measure-theoretic one, so the two developments provably agree where they overlap.
-/
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic
import TransportKernel.DobrushinReceive
import TransportKernel.DobrushinMeasureReceive

open MeasureTheory NNReal ENNReal Set
open scoped ProbabilityTheory

namespace TransportKernel

variable {S : Type} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-! ## A finite distribution as a measure -/

/-- A finite distribution as a measure: the sum of its weighted Dirac masses. -/
noncomputable def Dist.toMeasure (μ : Dist S) : Measure S :=
  ∑ s, ENNReal.ofReal (μ.p s) • Measure.dirac s

theorem Dist.toMeasure_apply (μ : Dist S) (A : Set S) :
    μ.toMeasure A = ∑ s, A.indicator (fun t => ENNReal.ofReal (μ.p t)) s := by
  rw [Dist.toMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  by_cases h : s ∈ A
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- The measure of a set is `ofReal` of the corresponding partial mass. -/
theorem Dist.toMeasure_apply' (μ : Dist S) (A : Set S) :
    μ.toMeasure A = ENNReal.ofReal (∑ s, A.indicator μ.p s) := by
  rw [μ.toMeasure_apply A,
      ENNReal.ofReal_sum_of_nonneg
        (fun s _ => Set.indicator_nonneg (fun t _ => μ.nonneg t) s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s ∈ A <;> simp [h]

instance (μ : Dist S) : IsProbabilityMeasure μ.toMeasure where
  measure_univ := by
    rw [μ.toMeasure_apply' univ]
    simp only [Set.indicator_univ]
    rw [μ.sum_one, ENNReal.ofReal_one]

/-! ## Real-side identities for `tvd` -/

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem tvd_nonneg (μ ν : Dist S) : 0 ≤ tvd μ ν :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => abs_nonneg _)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
/-- TV as the total positive part: `tvd μ ν = ∑ₛ max (μₛ − νₛ) 0` — via the exposed
    overlap identity `tvd_eq_one_sub_sum_min`. -/
theorem tvd_eq_sum_max (μ ν : Dist S) :
    tvd μ ν = ∑ s, max (μ.p s - ν.p s) 0 := by
  rw [tvd_eq_one_sub_sum_min]
  have h : ∀ s : S, max (μ.p s - ν.p s) 0 = μ.p s - min (μ.p s) (ν.p s) := by
    intro s
    rcases le_total (μ.p s) (ν.p s) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith), sub_self]
    · rw [min_eq_right h, max_eq_left (by linarith)]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, μ.sum_one]

/-! ## The consistency lemma -/

/-- **The discretization consistency lemma.** Under the Dirac embedding, the
    measure-theoretic TV distance (`ℝ≥0∞`-valued sup over measurable sets) equals the
    finite TV distance (`½∑|·|`). The sup is attained on `{s | ν s ≤ μ s}`. -/
theorem tvDist_toMeasure (μ ν : Dist S) :
    tvDist μ.toMeasure ν.toMeasure = ENNReal.ofReal (tvd μ ν) := by
  refine le_antisymm (iSup₂_le fun A _ => tsub_le_iff_left.mpr ?_) ?_
  · -- upper bound: `μ°A ≤ ν°A + ofReal (tvd μ ν)`, pointwise under the sums
    rw [μ.toMeasure_apply' A, ν.toMeasure_apply' A,
        ← ENNReal.ofReal_add
          (Finset.sum_nonneg fun s _ => Set.indicator_nonneg (fun t _ => ν.nonneg t) s)
          (tvd_nonneg μ ν)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [tvd_eq_sum_max, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    by_cases h : s ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      have := le_max_left (μ.p s - ν.p s) (0 : ℝ)
      linarith
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      have := le_max_right (μ.p s - ν.p s) (0 : ℝ)
      linarith
  · -- attainment on the positive set `D = {s | ν s ≤ μ s}`
    have heq : ENNReal.ofReal (tvd μ ν)
        = μ.toMeasure {s | ν.p s ≤ μ.p s} - ν.toMeasure {s | ν.p s ≤ μ.p s} := by
      rw [μ.toMeasure_apply' _, ν.toMeasure_apply' _,
          ← ENNReal.ofReal_sub _
            (Finset.sum_nonneg fun s _ => Set.indicator_nonneg (fun t _ => ν.nonneg t) s)]
      congr 1
      rw [tvd_eq_sum_max, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases h : s ∈ {s : S | ν.p s ≤ μ.p s}
      · have h' : ν.p s ≤ μ.p s := h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h, max_eq_left (by linarith)]
      · have h' : ¬ ν.p s ≤ μ.p s := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
            max_eq_right (by linarith), sub_zero]
    rw [heq]
    exact le_tvDist .of_discrete

/-! ## The kernel side: pushforward consistency -/

/-- A finite stochastic matrix as a mathlib Markov kernel: row `s` becomes the
    measure `(K.row s).toMeasure`; measurability is free on a discrete space. -/
noncomputable def Kernel.toMKernel (K : Kernel S) : ProbabilityTheory.Kernel S S where
  toFun := fun s => (K.row s).toMeasure
  measurable' := .of_discrete

@[simp] theorem Kernel.toMKernel_apply (K : Kernel S) (s : S) :
    K.toMKernel s = (K.row s).toMeasure := rfl

instance (K : Kernel S) : ProbabilityTheory.IsMarkovKernel K.toMKernel :=
  ⟨fun s => inferInstanceAs (IsProbabilityMeasure (K.row s).toMeasure)⟩

/-- **Pushforward consistency**: the finite pushforward `K.push` matches mathlib's
    `κ ∘ₘ ·` under the Dirac embedding. -/
theorem toMeasure_push (K : Kernel S) (μ : Dist S) :
    (K.push μ).toMeasure = K.toMKernel ∘ₘ μ.toMeasure := by
  ext A hA
  rw [Measure.bind_apply hA K.toMKernel.aemeasurable]
  simp_rw [Kernel.toMKernel_apply]
  -- the integral against a finite sum of weighted Diracs is a finite sum
  have hR : ∫⁻ s, (K.row s).toMeasure A ∂μ.toMeasure
      = ∑ s, ENNReal.ofReal (μ.p s) * (K.row s).toMeasure A := by
    rw [show μ.toMeasure = ∑ s, ENNReal.ofReal (μ.p s) • Measure.dirac s from rfl,
        lintegral_finsetSum_measure]
    exact Finset.sum_congr rfl fun s _ =>
      by rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [hR]
  -- both sides as `ofReal` of the same real double sum
  simp_rw [Dist.toMeasure_apply', ← ENNReal.ofReal_mul (μ.nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg
        (fun s _ => mul_nonneg (μ.nonneg s)
          (Finset.sum_nonneg fun t _ =>
            Set.indicator_nonneg (fun u _ => (K.row s).nonneg u) t))]
  congr 1
  have hind : ∀ t : S, A.indicator (K.push μ).p t = ∑ s, μ.p s * A.indicator (K.row s).p t := by
    intro t
    by_cases h : t ∈ A
    · simp [Set.indicator_of_mem h, Kernel.push, Kernel.row]
    · simp [Set.indicator_of_notMem h]
  simp_rw [hind]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-! ## The loop, closed -/

/-- **The finite DPI as a corollary of the measure-theoretic one.** Transport the row
    hypothesis through `tvDist_toMeasure`, apply `tvDist_comp_le` to the embedded
    measures, and pull the conclusion back along the same lemma. The two Dobrushin
    developments provably agree where they overlap. -/
theorem dpi_via_measure (K : Kernel S) {η : ℝ} (hη0 : 0 ≤ η)
    (hη : ∀ s s', tvd (K.row s) (K.row s') ≤ η) (μ ν : Dist S) :
    tvd (K.push μ) (K.push ν) ≤ η * tvd μ ν := by
  have h := tvDist_comp_le K.toMKernel (η := ENNReal.ofReal η)
    (fun x y => by
      rw [Kernel.toMKernel_apply, Kernel.toMKernel_apply, tvDist_toMeasure]
      exact ENNReal.ofReal_le_ofReal (hη x y))
    μ.toMeasure ν.toMeasure
  rw [← toMeasure_push, ← toMeasure_push, tvDist_toMeasure, tvDist_toMeasure,
      ← ENNReal.ofReal_mul hη0] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hη0 (tvd_nonneg μ ν))).mp h

end TransportKernel
