/-
  Tier 4 (Q3): diagonal consistency — the classical finite Dobrushin development embeds
  into the quantum one, and they provably agree where they overlap.

  `Dist.toMState` embeds a finite distribution as a diagonal density matrix;
  `trDistance_toMState` shows the quantum trace distance restricted to diagonals IS the
  classical total-variation distance `tvd` (via the Jordan trace-norm lemma and
  `cfc_diagonal`); `Kernel.toQChannel` embeds a stochastic matrix as a (diagonal-output)
  quantum channel; `toMState_push` shows the embedding intertwines the classical
  pushforward with the channel action; and `classical_contraction_via_quantum`
  re-derives the classical contraction `tvd (K.push μ) (K.push ν) ≤ tvd μ ν` as a
  corollary of the quantum DPI.

  With Tier 3c this completes the tower: the finite Dobrushin development embeds
  consistently into BOTH the measure-theoretic generalization and the quantum one, with
  all three machine-checked to agree. (The coefficient-refined classical DPI stays with
  its classical proof — the quantum corollary transports the η = 1 contraction; the
  pairwise-row-η refinement is classical-side information.)
-/
import TransportKernel.QuantumDobrushinReceive

namespace TransportKernel

open Matrix HermitianMat NNReal
open scoped ComplexOrder

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A finite classical distribution as a diagonal quantum state. -/
noncomputable def Dist.toMState (μ : Dist S) : MState S where
  M := HermitianMat.diagonal ℂ μ.p
  nonneg := by
    rw [HermitianMat.zero_le_iff, HermitianMat.diagonal_mat]
    exact Matrix.PosSemidef.diagonal
      (fun s => Complex.zero_le_real.mpr (μ.nonneg s))
  tr := by
    rw [HermitianMat.trace_diagonal]
    exact μ.sum_one

/-- The embedded states' difference is the diagonal of the pointwise difference. -/
private lemma toMState_sub_M (μ ν : Dist S) :
    μ.toMState.M - ν.toMState.M = HermitianMat.diagonal ℂ (fun s => μ.p s - ν.p s) := by
  ext1
  rw [HermitianMat.mat_sub]
  show (HermitianMat.diagonal ℂ μ.p).mat - (HermitianMat.diagonal ℂ ν.p).mat = _
  rw [HermitianMat.diagonal_mat, HermitianMat.diagonal_mat, HermitianMat.diagonal_mat]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.sub_apply]
  · simp [h, Matrix.sub_apply]

/-- **Trace distance restricted to diagonals is the classical TV distance.** The
    quantum and classical metrics provably agree on the embedded simplex. -/
theorem trDistance_toMState (μ ν : Dist S) :
    TrDistance μ.toMState ν.toMState = tvd μ ν := by
  have hm : μ.toMState.m - ν.toMState.m
      = (HermitianMat.diagonal ℂ (fun s => μ.p s - ν.p s)).mat := by
    show μ.toMState.M.mat - ν.toMState.M.mat = _
    rw [← HermitianMat.mat_sub, toMState_sub_M]
  unfold TrDistance
  rw [show μ.toMState.m - ν.toMState.m
        = (HermitianMat.diagonal ℂ (fun s => μ.p s - ν.p s)).mat from hm,
      traceNorm_eq_trace_posPart_add_trace_negPart,
      posPart_eq_cfc_max, negPart_eq_cfc_min,
      HermitianMat.cfc_diagonal, HermitianMat.cfc_diagonal,
      HermitianMat.trace_diagonal, HermitianMat.trace_diagonal]
  unfold tvd
  rw [← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => (abs_eq_sup_add_sup _).symm

/-- A classical channel as a quantum channel: measure in the computational basis, push
    the outcome through `K`, output the resulting diagonal state. Positive and
    trace-preserving (in fact CPTP, but PTP is all the quantum tier needs). -/
noncomputable def Kernel.toQChannel (K : Kernel S) : PTPMap S S ℂ where
  toLinearMap := {
    toFun := fun X => Matrix.diagonal (fun t => ∑ s, (K.K s t : ℂ) * X s s)
    map_add' := by
      intro X Y
      ext i j
      by_cases h : i = j
      · subst h
        rw [Matrix.add_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
            Matrix.diagonal_apply_eq, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Matrix.add_apply]
        ring
      · rw [Matrix.add_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
            Matrix.diagonal_apply_ne _ h, add_zero]
    map_smul' := by
      intro c X
      dsimp only [RingHom.id_apply]
      rw [← Matrix.diagonal_smul]
      congr 1
      funext t
      rw [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul]
      ring
  }
  pos := by
    intro X hX
    exact Matrix.PosSemidef.diagonal (fun t =>
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (Complex.zero_le_real.mpr (K.nonneg s t)) hX.diag_nonneg)
  TP := by
    intro X
    show Matrix.trace (Matrix.diagonal fun t => ∑ s, (K.K s t : ℂ) * X s s)
        = Matrix.trace X
    calc Matrix.trace (Matrix.diagonal fun t => ∑ s, (K.K s t : ℂ) * X s s)
        = ∑ t, ∑ s, (K.K s t : ℂ) * X s s := Matrix.trace_diagonal _
      _ = ∑ s, ∑ t, (K.K s t : ℂ) * X s s := Finset.sum_comm
      _ = ∑ s, (∑ t, (K.K s t : ℂ)) * X s s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ s, X s s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have h1 : (∑ t, (K.K s t : ℂ)) = 1 := by exact_mod_cast K.row_one s
          rw [h1, one_mul]
      _ = Matrix.trace X := by simp [Matrix.trace, Matrix.diag]

/-- **The embedding intertwines**: classical pushforward = quantum channel action on
    the embedded state. -/
theorem toMState_push (K : Kernel S) (μ : Dist S) :
    (K.push μ).toMState = K.toQChannel μ.toMState := by
  apply MState.ext
  ext1
  show (HermitianMat.diagonal ℂ (K.push μ).p).mat
      = K.toQChannel.map μ.toMState.m
  rw [HermitianMat.diagonal_mat]
  show _ = Matrix.diagonal (fun t => ∑ s, (K.K s t : ℂ) * μ.toMState.m s s)
  congr 1
  funext t
  show ((K.push μ).p t : ℂ) = _
  have hdiag : ∀ s, μ.toMState.m s s = (μ.p s : ℂ) := by
    intro s
    show (HermitianMat.diagonal ℂ μ.p).mat s s = _
    rw [HermitianMat.diagonal_mat]
    simp
  simp_rw [hdiag]
  show ((∑ s, μ.p s * K.K s t : ℝ) : ℂ) = ∑ s, (K.K s t : ℂ) * (μ.p s : ℂ)
  push_cast
  congr 1
  funext s
  ring

/-- **The classical contraction as a corollary of the quantum DPI** — the tower closes:
    the finite Dobrushin development embeds consistently into both the measure-theoretic
    generalization (Tier 3c) and the quantum one, all machine-checked to agree. -/
theorem classical_contraction_via_quantum (K : Kernel S) (μ ν : Dist S) :
    tvd (K.push μ) (K.push ν) ≤ tvd μ ν := by
  rw [← trDistance_toMState, ← trDistance_toMState, toMState_push, toMState_push]
  exact trDistance_apply_le K.toQChannel μ.toMState ν.toMState

end TransportKernel
