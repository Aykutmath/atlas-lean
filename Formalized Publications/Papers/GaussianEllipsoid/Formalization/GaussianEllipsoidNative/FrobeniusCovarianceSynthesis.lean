import CovarianceSynthesis
import FrobeniusCoordinates

noncomputable section
open scoped BigOperators Matrix
open GaussianEllipsoid
namespace GaussianTensorTrace

/-- Bilinear synthesis with the actual Frobenius matrix codomain. -/
def tensorFrobeniusSynthesis {n h : ℕ} (a b : Fin n → Fin h → ℝ) (d : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] FrobeniusMatrix h h :=
  (frobeniusEquivEuclidean h h).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scaledSynthesisCLM (tensorColumns a b) d)

/-- This is exactly the matrix-valued sum d^(-1/2) sum_i y_i a_i b_i^T. -/
theorem tensorFrobeniusSynthesis_apply {n h : ℕ} (a b : Fin n → Fin h → ℝ) (d : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (r s : Fin h) :
    frobeniusToMatrix (tensorFrobeniusSynthesis a b d y) r s =
      (Real.sqrt d)⁻¹ * ∑ i, y i * (a i r * b i s) := by
  change (scaledSynthesisCLM (tensorColumns a b) d y) (r,s) = _
  exact scaledSynthesisCLM_apply _ _ _ _

theorem tensorFrobeniusSynthesis_norm {n h : ℕ} (a b : Fin n → Fin h → ℝ) (d : ℝ) :
    ‖tensorFrobeniusSynthesis a b d‖ = ‖scaledSynthesisCLM (tensorColumns a b) d‖ := by
  have hp (y : EuclideanSpace ℝ (Fin n)) :
      ‖tensorFrobeniusSynthesis a b d y‖ = ‖scaledSynthesisCLM (tensorColumns a b) d y‖ := by
    exact (frobeniusEquivEuclidean h h).symm.norm_map _
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    rw [hp]
    exact (scaledSynthesisCLM (tensorColumns a b) d).le_opNorm y
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    rw [← hp]
    exact (tensorFrobeniusSynthesis a b d).le_opNorm y

/-- The required norm identity is for the Frobenius codomain and the Euclidean
coefficient domain, with the literal tensor covariance on the right. -/
theorem tensorFrobeniusSynthesis_norm_sq {n h : ℕ} (a b : Fin n → Fin h → ℝ)
    (d : ℝ) (hd : 0 ≤ d) :
    ‖tensorFrobeniusSynthesis a b d‖^2 =
      ‖matrixCLM (∑ i, Matrix.vecMulVec (fun r : Fin h × Fin h => a i r.1 * b i r.2)
        (fun r : Fin h × Fin h => a i r.1 * b i r.2))‖ / d := by
  rw [tensorFrobeniusSynthesis_norm, scaledSynthesisCLM_norm_sq _ _ hd,
    covariance_eq_sum_outer]
  rfl

#print axioms tensorFrobeniusSynthesis_apply
#print axioms tensorFrobeniusSynthesis_norm
#print axioms tensorFrobeniusSynthesis_norm_sq
end GaussianTensorTrace
