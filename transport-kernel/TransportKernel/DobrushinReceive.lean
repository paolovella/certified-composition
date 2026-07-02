/-
  Tier-3: the instance mathlib does NOT have — the Dobrushin / strong-data-processing
  contraction of total-variation distance under a Markov kernel, built from scratch.

  Lipschitz and Hölder were *received*: mathlib already proves the contraction, and the
  interface just plugs it in. The Dobrushin instance is the opposite — mathlib has no
  data-processing inequality, so the contraction (`dpi`) is proved here, over finite
  state spaces, and only then handed to the interface. This is the quantitative centre
  the whole transport line was built to host: `M = ℝ≥0` (Dobrushin coefficients) acts on
  `D = ℝ` (TV distances) by multiplication, and `Bridge.comp` reproduces the
  submultiplicative bound `η(K)·η(L)` — advanced composition, as certificate accumulation.
-/
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import TransportKernel.LipschitzReceive   -- reuse the GradedAction/Bridge core

open NNReal Finset

namespace TransportKernel

/-! ## The real instance: ℝ≥0 (coefficients) acting on ℝ (TV distances) -/

/-- Dobrushin coefficients in `ℝ≥0` scale total-variation distances in `ℝ` by
    (coerced) multiplication — the `M ≠ D` separation, TV distances living in `ℝ`
    where the signed differences that define them are computed. -/
noncomputable def dobrushinGA : GradedAction ℝ≥0 ℝ where
  mul      := (· * ·)
  le       := (· ≤ ·)
  act      := fun k d => (k : ℝ) * d
  le_trans := le_trans
  act_mul  := fun k₁ k₂ d => by push_cast; ring
  act_mono := by intro k d d' h; exact mul_le_mul_of_nonneg_left h k.2

/-! ## Finite distributions, kernels, pushforward -/

variable {S : Type} [Fintype S]

/-- A probability distribution on a finite type. -/
structure Dist (S : Type) [Fintype S] where
  p       : S → ℝ
  nonneg  : ∀ s, 0 ≤ p s
  sum_one : ∑ s, p s = 1

/-- Total-variation distance `½‖μ − ν‖₁`. -/
noncomputable def tvd (μ ν : Dist S) : ℝ := (1 / 2) * ∑ s, |μ.p s - ν.p s|

/-- A Markov kernel: a stochastic matrix on `S`. -/
structure Kernel (S : Type) [Fintype S] where
  K       : S → S → ℝ
  nonneg  : ∀ s t, 0 ≤ K s t
  row_one : ∀ s, ∑ t, K s t = 1

/-- The distribution `K s` is the `s`-th row of the kernel. -/
def Kernel.row (K : Kernel S) (s : S) : Dist S where
  p       := K.K s
  nonneg  := K.nonneg s
  sum_one := K.row_one s

/-- Pushforward of a distribution through a kernel: `(push K μ)(t) = ∑ₛ μ(s) K(s,t)`. -/
noncomputable def Kernel.push (K : Kernel S) (μ : Dist S) : Dist S where
  p := fun t => ∑ s, μ.p s * K.K s t
  nonneg := fun t => Finset.sum_nonneg (fun s _ => mul_nonneg (μ.nonneg s) (K.nonneg s t))
  sum_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, K.row_one, mul_one, μ.sum_one]

/-! ## Supporting inequalities for the data-processing proof -/

/-- `|x − y| = x + y − 2·min x y` on `ℝ`. -/
theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring

/-- Total variation as one minus the overlap mass: `tvd μ ν = 1 − ∑ₛ min(μₛ, νₛ)`. -/
theorem tvd_eq_one_sub_sum_min (μ ν : Dist S) :
    tvd μ ν = 1 - ∑ s, min (μ.p s) (ν.p s) := by
  unfold tvd
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      μ.sum_one, ν.sum_one]
  ring

/-- Overlap mass is at least `1 − η` when the two rows are within TV `η`. -/
theorem sum_min_ge_of_tvd_le {μ ν : Dist S} {η : ℝ} (h : tvd μ ν ≤ η) :
    (1 : ℝ) - η ≤ ∑ s, min (μ.p s) (ν.p s) := by
  rw [tvd_eq_one_sub_sum_min] at h; linarith

/-- Min is superadditive over finite sums: `∑ min(aᵢ,bᵢ) ≤ min(∑ aᵢ, ∑ bᵢ)`. -/
theorem sum_min_le_min_sum (a b : S → ℝ) :
    ∑ i, min (a i) (b i) ≤ min (∑ i, a i) (∑ i, b i) :=
  le_min (Finset.sum_le_sum fun _ _ => min_le_left _ _)
    (Finset.sum_le_sum fun _ _ => min_le_right _ _)

/-- Nonnegative scalars pass through `min`: `w·min a b = min (w·a) (w·b)` for `0 ≤ w`. -/
theorem mul_min_of_nonneg' {w a b : ℝ} (hw : 0 ≤ w) :
    w * min a b = min (w * a) (w * b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left (mul_le_mul_of_nonneg_left h hw)]
  · rw [min_eq_right h, min_eq_right (mul_le_mul_of_nonneg_left h hw)]

/-! ## The data-processing inequality — proved from scratch -/

/-- **The Dobrushin data-processing inequality.** If every pair of kernel rows is within
    total variation `η`, the pushforward contracts TV distance by `η`:
    `tvd (push μ) (push ν) ≤ η · tvd μ ν`. Mathlib has no DPI — this is the from-scratch
    quantitative core the whole transport interface exists to host. The proof is the
    coupling / overlap argument: split `μ − ν` into its Jordan parts of equal mass `m`,
    couple them by the outer product `dp ⊗ dm`, and bound the pushforward overlap below by
    `(1 − η)·m` using the superadditivity of `min` over the coupling. -/
theorem dpi (K : Kernel S) {η : ℝ} (hη : ∀ s s', tvd (K.row s) (K.row s') ≤ η)
    (μ ν : Dist S) :
    tvd (K.push μ) (K.push ν) ≤ η * tvd μ ν := by
  classical
  -- Jordan parts of the signed difference `μ − ν`
  set dp : S → ℝ := fun s => max (μ.p s - ν.p s) 0 with hdp
  set dm : S → ℝ := fun s => max (ν.p s - μ.p s) 0 with hdm
  have dpnn : ∀ s, 0 ≤ dp s := fun s => le_max_right _ _
  have dmnn : ∀ s, 0 ≤ dm s := fun s => le_max_right _ _
  have dsplit : ∀ s, μ.p s - ν.p s = dp s - dm s := by
    intro s; simp only [hdp, hdm]
    rcases le_total (μ.p s) (ν.p s) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have dabs : ∀ s, dp s + dm s = |μ.p s - ν.p s| := by
    intro s; simp only [hdp, hdm]
    rcases le_total (μ.p s) (ν.p s) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg (by linarith)]; ring
  -- equal Jordan masses `m`
  set m : ℝ := ∑ s, dp s with hm
  have mnn : 0 ≤ m := Finset.sum_nonneg (fun s _ => dpnn s)
  have hmm : ∑ s, dm s = m := by
    have h0 : ∑ s, (μ.p s - ν.p s) = 0 := by
      rw [Finset.sum_sub_distrib, μ.sum_one, ν.sum_one]; ring
    have h1 : ∑ s, (dp s - dm s) = 0 := by
      rw [← h0]; exact Finset.sum_congr rfl (fun s _ => (dsplit s).symm)
    rw [Finset.sum_sub_distrib] at h1; rw [hm]; linarith
  -- `tvd μ ν = m`
  have tvd_mn : tvd μ ν = m := by
    unfold tvd
    have e : ∑ s, |μ.p s - ν.p s| = ∑ s, (dp s + dm s) :=
      Finset.sum_congr rfl (fun s _ => (dabs s).symm)
    rw [e, Finset.sum_add_distrib, hmm, hm]; ring
  -- pushed Jordan parts `A`, `B`
  set A : S → ℝ := fun t => ∑ s, dp s * K.K s t with hA
  set B : S → ℝ := fun t => ∑ s, dm s * K.K s t with hB
  have Ann : ∀ t, 0 ≤ A t := fun t => Finset.sum_nonneg (fun s _ => mul_nonneg (dpnn s) (K.nonneg s t))
  have Bnn : ∀ t, 0 ≤ B t := fun t => Finset.sum_nonneg (fun s _ => mul_nonneg (dmnn s) (K.nonneg s t))
  have sumA : ∑ t, A t = m := by
    simp only [hA]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, K.row_one, mul_one]
    exact hm.symm
  have sumB : ∑ t, B t = m := by
    simp only [hB]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, K.row_one, mul_one]; exact hmm
  -- pushforward difference is `A − B`
  have pushdiff : ∀ t, (K.push μ).p t - (K.push ν).p t = A t - B t := by
    intro t
    show (∑ s, μ.p s * K.K s t) - (∑ s, ν.p s * K.K s t) = A t - B t
    simp only [hA, hB]; rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun s _ => by rw [← sub_mul, dsplit s, sub_mul])
  -- `tvd(push) = m − ∑ min(A,B)`
  have tvd_push : tvd (K.push μ) (K.push ν) = m - ∑ t, min (A t) (B t) := by
    unfold tvd
    have e : ∀ t, |(K.push μ).p t - (K.push ν).p t| = A t + B t - 2 * min (A t) (B t) :=
      fun t => by rw [pushdiff t, abs_sub_eq_add_sub_two_min]
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sumA, sumB]; ring
  -- overlap of any two rows is at least `1 − η`
  have hover : ∀ s s', (1 : ℝ) - η ≤ ∑ t, min (K.K s t) (K.K s' t) :=
    fun s s' => sum_min_ge_of_tvd_le (hη s s')
  -- the coupling factorisations
  have ha : ∀ t, ∑ q : S × S, (dp q.1 * dm q.2) * K.K q.1 t = m * A t := by
    intro t
    rw [Fintype.sum_prod_type]
    have e : ∀ s, ∑ s' : S, (dp s * dm s') * K.K s t = (dp s * K.K s t) * m := by
      intro s
      have : ∑ s' : S, (dp s * dm s') * K.K s t = (dp s * K.K s t) * ∑ s' : S, dm s' := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun s' _ => by ring)
      rw [this, hmm]
    simp_rw [e]; rw [← Finset.sum_mul, mul_comm]
  have hb : ∀ t, ∑ q : S × S, (dp q.1 * dm q.2) * K.K q.2 t = m * B t := by
    intro t
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have e : ∀ s', ∑ s : S, (dp s * dm s') * K.K s' t = (dm s' * K.K s' t) * m := by
      intro s'
      have : ∑ s : S, (dp s * dm s') * K.K s' t = (dm s' * K.K s' t) * ∑ s : S, dp s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun s _ => by ring)
      rw [this, ← hm]
    simp_rw [e]; rw [← Finset.sum_mul, mul_comm]
  -- superadditivity of `min` under the coupling, per target `t`
  have hmin : ∀ t, ∑ q : S × S, (dp q.1 * dm q.2) * min (K.K q.1 t) (K.K q.2 t)
      ≤ m * min (A t) (B t) := by
    intro t
    have e : ∀ q : S × S, (dp q.1 * dm q.2) * min (K.K q.1 t) (K.K q.2 t)
        = min ((dp q.1 * dm q.2) * K.K q.1 t) ((dp q.1 * dm q.2) * K.K q.2 t) :=
      fun q => mul_min_of_nonneg' (mul_nonneg (dpnn q.1) (dmnn q.2))
    simp_rw [e]
    calc ∑ q : S × S, min ((dp q.1 * dm q.2) * K.K q.1 t) ((dp q.1 * dm q.2) * K.K q.2 t)
        ≤ min (∑ q : S × S, (dp q.1 * dm q.2) * K.K q.1 t)
            (∑ q : S × S, (dp q.1 * dm q.2) * K.K q.2 t) := sum_min_le_min_sum _ _
      _ = min (m * A t) (m * B t) := by rw [ha t, hb t]
      _ = m * min (A t) (B t) := (mul_min_of_nonneg' mnn).symm
  -- total coupling mass is `m·m`
  have hww : ∑ q : S × S, dp q.1 * dm q.2 = m * m := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, hmm]
    rw [← Finset.sum_mul, ← hm]
  -- KEY: overlap of the pushed parts is at least `(1 − η)·m`
  have key : (1 - η) * m ≤ ∑ t, min (A t) (B t) := by
    have quad : (1 - η) * (m * m) ≤ m * ∑ t, min (A t) (B t) := by
      calc (1 - η) * (m * m)
          = ∑ q : S × S, (dp q.1 * dm q.2) * (1 - η) := by
            rw [← Finset.sum_mul, hww]; ring
        _ ≤ ∑ q : S × S, (dp q.1 * dm q.2) * (∑ t, min (K.K q.1 t) (K.K q.2 t)) := by
            apply Finset.sum_le_sum; intro q _
            exact mul_le_mul_of_nonneg_left (hover q.1 q.2) (mul_nonneg (dpnn q.1) (dmnn q.2))
        _ = ∑ q : S × S, ∑ t, (dp q.1 * dm q.2) * min (K.K q.1 t) (K.K q.2 t) := by
            simp_rw [Finset.mul_sum]
        _ = ∑ t, ∑ q : S × S, (dp q.1 * dm q.2) * min (K.K q.1 t) (K.K q.2 t) := Finset.sum_comm
        _ ≤ ∑ t, m * min (A t) (B t) := Finset.sum_le_sum (fun t _ => hmin t)
        _ = m * ∑ t, min (A t) (B t) := by rw [Finset.mul_sum]
    rcases lt_or_eq_of_le mnn with hpos | hzero
    · have h2 : ((1 - η) * m) * m ≤ (∑ t, min (A t) (B t)) * m := by
        rw [show ((1 - η) * m) * m = (1 - η) * (m * m) from by ring,
            show (∑ t, min (A t) (B t)) * m = m * ∑ t, min (A t) (B t) from by ring]
        exact quad
      exact le_of_mul_le_mul_right h2 hpos
    · rw [← hzero]; simp
      exact Finset.sum_nonneg (fun t _ => le_min (Ann t) (Bnn t))
  rw [tvd_push, tvd_mn]; linarith [key]

/-! ## The reception: a kernel IS a certified bridge, and composition accumulates -/

/-- Two distributions with equal mass functions are equal (the proof fields are
    propositional). -/
theorem Dist.ext' {μ ν : Dist S} (h : μ.p = ν.p) : μ = ν := by
  cases μ; cases ν; cases h; rfl

/-- **A Markov kernel is a certified bridge.** Its Dobrushin coefficient `η` (any bound on
    pairwise row TV) is the certificate, the pushforward is the map, and the DPI is the
    contraction proof — `ℝ≥0` acting on `ℝ` by multiplication. -/
noncomputable def Bridge.ofKernel (K : Kernel S) (η : ℝ≥0)
    (hη : ∀ s s', tvd (K.row s) (K.row s') ≤ (η : ℝ)) :
    Bridge (Dist S) ℝ≥0 ℝ dobrushinGA tvd where
  map       := K.push
  cert      := η
  contracts := fun μ ν => dpi K hη μ ν

/-- **Advanced composition is certificate accumulation.** The generic `Bridge.comp` applied
    to two kernel bridges yields the *submultiplicative* Dobrushin bound `η(K)·η(L)` on the
    composed pushforward — the interface reproduces advanced composition from its generic
    accumulation law, with no kernel-specific proof. -/
theorem comp_reconstructs_dobrushin (K L : Kernel S) (ηK ηL : ℝ≥0)
    (hK : ∀ s s', tvd (K.row s) (K.row s') ≤ (ηK : ℝ))
    (hL : ∀ s s', tvd (L.row s) (L.row s') ≤ (ηL : ℝ)) (μ ν : Dist S) :
    tvd (K.push (L.push μ)) (K.push (L.push ν)) ≤ (↑(ηK * ηL) : ℝ) * tvd μ ν :=
  ((Bridge.ofKernel K ηK hK).comp (Bridge.ofKernel L ηL hL)).contracts μ ν

/-- Kernel composition `L then K`: `(comp K L)(s,t) = ∑ᵤ L(s,u) K(u,t)`. -/
noncomputable def Kernel.comp (K L : Kernel S) : Kernel S where
  K       := fun s t => ∑ u, L.K s u * K.K u t
  nonneg  := fun s t => Finset.sum_nonneg (fun u _ => mul_nonneg (L.nonneg s u) (K.nonneg u t))
  row_one := fun s => by
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, K.row_one, mul_one]; exact L.row_one s

/-- A composed-kernel row is the pushforward of the corresponding `L`-row through `K`. -/
theorem Kernel.comp_row (K L : Kernel S) (s : S) :
    (K.comp L).row s = K.push (L.row s) :=
  Dist.ext' (by funext t; simp only [Kernel.row, Kernel.push, Kernel.comp])

/-- **Submultiplicativity of the Dobrushin coefficient** — the advanced-composition law at
    the level of certificates: `η(K∘L) ≤ η(K)·η(L)`. This is the DPI applied to the rows,
    and it is exactly the certificate the composed bridge carries. -/
theorem coeff_submul (K L : Kernel S) (ηK ηL : ℝ≥0)
    (hK : ∀ s s', tvd (K.row s) (K.row s') ≤ (ηK : ℝ))
    (hL : ∀ s s', tvd (L.row s) (L.row s') ≤ (ηL : ℝ)) (s s' : S) :
    tvd ((K.comp L).row s) ((K.comp L).row s') ≤ (↑(ηK * ηL) : ℝ) := by
  rw [K.comp_row, K.comp_row]
  calc tvd (K.push (L.row s)) (K.push (L.row s'))
      ≤ (ηK : ℝ) * tvd (L.row s) (L.row s') := dpi K hK _ _
    _ ≤ (ηK : ℝ) * (ηL : ℝ) := by
        apply mul_le_mul_of_nonneg_left (hL s s') ηK.2
    _ = (↑(ηK * ηL) : ℝ) := by push_cast; ring

end TransportKernel
