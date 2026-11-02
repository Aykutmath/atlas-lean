import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace UCEscape

/-- Coordinates along any orthonormal frame are again exactly standard
Gaussian. The ambient dimension may exceed the frame dimension. -/
theorem stdGaussian_adjoint_isometry (n r : ℕ)
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).map U.toContinuousLinearMap.adjoint =
      stdGaussian (EuclideanSpace ℝ (Fin r)) := by
  let L := U.toContinuousLinearMap.adjoint
  haveI : IsGaussian ((stdGaussian (EuclideanSpace ℝ (Fin n))).map L) := isGaussian_map L
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, integral_id_stdGaussian, map_zero]
  · ext x y
    rw [covarianceBilin_map (IsGaussian.memLp_id _ 2 (by norm_num)),
      covarianceBilin_stdGaussian, covarianceBilin_stdGaussian]
    simp only [L, ContinuousLinearMap.adjoint_adjoint, innerSL_apply_apply]
    exact U.inner_map_map x y

#print axioms stdGaussian_adjoint_isometry
end UCEscape
