/-
  Tier 4 (Q1+Q2): the quantum data-processing inequality — trace-distance contraction
  under positive trace-preserving maps — built against Physlib, and received into the
  SAME graded action as the finite classical case (`dobrushinGA`).

  Physlib (leanprover-community; ex Lean-QuantumInfo) has `TrDistance` with basic
  properties but no contractivity and no Dobrushin coefficient (see
  `NOTES-quantum-tier4.md`): the mathlib-had-no-DPI situation, one level up. So the
  contraction is proved here, from scratch, and handed to the interface.

  The proof is the Jordan-decomposition argument (Ruskai): for Hermitian `X` with
  `X = X⁺ − X⁻`, positivity gives `‖Λ(X)‖₁ ≤ tr Λ(X⁺) + tr Λ(X⁻)`, and trace
  preservation closes to `tr X⁺ + tr X⁻ = ‖X‖₁`. Note the hypotheses: **positivity and
  trace preservation only — complete positivity is not needed** (the honest minimal
  hypothesis; CPTP is a corollary since Physlib's `CPTPMap` refines `PTPMap`).

  Reception: a quantum-Dobrushin-bounded channel is a certified bridge in `dobrushinGA`
  — the graded action of the finite classical tier — and the generic `Bridge.comp`
  yields the submultiplicative bound on composed channels
  (`comp_reconstructs_quantum_dobrushin`). Finite kernels, measure kernels, and quantum
  channels: one composition law.
-/
import QuantumInfo.States.Mixed.TraceDistance
import QuantumInfo.Channels.Bundled
import TransportKernel.DobrushinReceive

namespace TransportKernel

open Matrix HermitianMat NNReal
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `|x| = (x ⊔ 0) + (-x ⊔ 0)` — the scalar shadow of the Jordan decomposition. -/
lemma abs_eq_sup_add_sup (x : ℝ) : |x| = (x ⊔ 0) + (-x ⊔ 0) := by
  rcases le_total x 0 with h | h
  · rw [abs_of_nonpos h, sup_eq_right.mpr h, sup_eq_left.mpr (by linarith), zero_add]
  · rw [abs_of_nonneg h, sup_eq_left.mpr h, sup_eq_right.mpr (by linarith), add_zero]

/-- **Jordan form of the trace norm**: `‖A‖₁ = tr A⁺ + tr A⁻` for Hermitian `A`.
    Physlib has the eigenvalue characterization and the cfc trace formula; this is the
    glue between them. -/
theorem traceNorm_eq_trace_posPart_add_trace_negPart (A : HermitianMat d ℂ) :
    A.mat.traceNorm = (A⁺).trace + (A⁻).trace := by
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues A.H,
      posPart_eq_cfc_max, negPart_eq_cfc_min, trace_cfc_eq, trace_cfc_eq,
      ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => abs_eq_sup_add_sup _

omit [DecidableEq d] in
/-- A positive-semidefinite matrix's trace norm is the real part of its trace. -/
private lemma traceNorm_eq_re_trace_of_posSemidef {Y : Matrix d d ℂ} (hY : Y.PosSemidef) :
    Y.traceNorm = RCLike.re Y.trace := by
  have h := hY.traceNorm_eq_trace
  rw [← h]
  simp

/-- **The quantum data-processing inequality, at positive trace-preserving generality
    (Q1).** A positive trace-preserving matrix map contracts the trace norm of Hermitian
    matrices. Complete positivity is NOT assumed — positivity and trace preservation
    suffice (Ruskai). Physlib has no trace-distance contractivity; this is the
    from-scratch quantitative core of the quantum tier. -/
theorem traceNorm_map_le (M : MatrixMap d d ℂ)
    (hpos : M.IsPositive) (htp : M.IsTracePreserving) (A : HermitianMat d ℂ) :
    (M A.mat).traceNorm ≤ A.mat.traceNorm := by
  have hd : A.mat = (A⁺).mat - (A⁻).mat := by
    rw [← HermitianMat.mat_sub, HermitianMat.posPart_add_negPart]
  have hp : (M (A⁺).mat).PosSemidef := hpos (HermitianMat.zero_le_iff.mp (posPart_nonneg A))
  have hn : (M (A⁻).mat).PosSemidef := hpos (HermitianMat.zero_le_iff.mp (negPart_nonneg A))
  calc (M A.mat).traceNorm
      = (M (A⁺).mat + -(M (A⁻).mat)).traceNorm := by
        rw [hd, map_sub, sub_eq_add_neg]
    _ ≤ (M (A⁺).mat).traceNorm + (-(M (A⁻).mat)).traceNorm := traceNorm_add_le _ _
    _ = (M (A⁺).mat).traceNorm + (M (A⁻).mat).traceNorm := by rw [Matrix.traceNorm_neg]
    _ = RCLike.re (M (A⁺).mat).trace + RCLike.re (M (A⁻).mat).trace := by
        rw [traceNorm_eq_re_trace_of_posSemidef hp, traceNorm_eq_re_trace_of_posSemidef hn]
    _ = RCLike.re (A⁺).mat.trace + RCLike.re (A⁻).mat.trace := by
        rw [htp.apply_trace, htp.apply_trace]
    _ = (A⁺).trace + (A⁻).trace := by
        rw [← HermitianMat.trace_eq_re_trace, ← HermitianMat.trace_eq_re_trace]
    _ = A.mat.traceNorm := (traceNorm_eq_trace_posPart_add_trace_negPart A).symm

/-- **Trace-distance contraction for channels.** Any positive trace-preserving map on
    states contracts trace distance: `T(Λρ, Λσ) ≤ T(ρ, σ)`. CPTP is a special case. -/
theorem trDistance_apply_le (Λ : PTPMap d d ℂ) (ρ σ : MState d) :
    TrDistance (Λ ρ) (Λ σ) ≤ TrDistance ρ σ := by
  have hm : (Λ ρ).m - (Λ σ).m = Λ.map (ρ.m - σ.m) := by
    show (Λ ρ).M.mat - (Λ σ).M.mat = Λ.map (ρ.M.mat - σ.M.mat)
    rw [map_sub]
    rfl
  have hH : ((ρ.M - σ.M) : HermitianMat d ℂ).mat = ρ.m - σ.m := HermitianMat.mat_sub _ _
  unfold TrDistance
  rw [hm, ← hH]
  have := traceNorm_map_le Λ.map Λ.pos Λ.TP (ρ.M - σ.M)
  rw [hH] at this ⊢
  linarith

/-- A **quantum Dobrushin bound**: `η` bounds the channel's trace-distance contraction
    ratio. The DPI says `1` is always a bound; genuinely smaller `η` is the quantum
    analogue of the classical Dobrushin coefficient. -/
def QDobrushinBound (η : ℝ) (Λ : PTPMap d d ℂ) : Prop :=
  ∀ ρ σ : MState d, TrDistance (Λ ρ) (Λ σ) ≤ η * TrDistance ρ σ

/-- The DPI as a Dobrushin bound: every channel has coefficient at most `1`. -/
theorem qDobrushinBound_one (Λ : PTPMap d d ℂ) : QDobrushinBound 1 Λ := by
  intro ρ σ
  rw [one_mul]
  exact trDistance_apply_le Λ ρ σ

variable {q : Type} [Fintype q] [DecidableEq q]

/-- **The reception (Q2): a Dobrushin-bounded quantum channel is a certified bridge**,
    in the SAME graded action as the finite classical tier (`dobrushinGA` — `ℝ≥0`
    coefficients acting on real distances): the map is the channel action on states, the
    certificate its coefficient, the DPI its contraction proof. -/
noncomputable def Bridge.ofPTPChannel (Λ : PTPMap q q ℂ) (η : ℝ≥0)
    (hη : QDobrushinBound (η : ℝ) Λ) :
    Bridge (MState q) ℝ≥0 ℝ dobrushinGA TrDistance where
  map       := fun ρ => Λ ρ
  cert      := η
  contracts := hη

/-- **Advanced composition is certificate accumulation — quantum.** The generic
    `Bridge.comp` applied to two channel bridges yields the submultiplicative Dobrushin
    bound `η(K)·η(L)` on the composed channel action. With Tiers 3 and 3b, finite
    kernels, measure-theoretic kernels, and quantum channels now compose under the SAME
    generic law. -/
theorem comp_reconstructs_quantum_dobrushin (K L : PTPMap q q ℂ) (ηK ηL : ℝ≥0)
    (hK : QDobrushinBound (ηK : ℝ) K) (hL : QDobrushinBound (ηL : ℝ) L)
    (ρ σ : MState q) :
    TrDistance (K (L ρ)) (K (L σ)) ≤ (↑(ηK * ηL) : ℝ) * TrDistance ρ σ :=
  ((Bridge.ofPTPChannel K ηK hK).comp (Bridge.ofPTPChannel L ηL hL)).contracts ρ σ

end TransportKernel
