import MatrixWhitening
import GaussianCoisometry

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Exact actual Gaussian law of a rectangular full-row-rank matrix:
whitening reduces it to the invertible covariance square root in the target. -/
theorem euclideanGaussian_matrix_map_eq_covarianceRoot (A : Matrix ι κ ℝ)
    (hA : (covariance A).det ≠ 0) :
    (euclideanGaussianLaw κ).map (matrixCLM A) =
      (euclideanGaussianLaw ι).map (matrixCLM (covarianceRoot A)) := by
  have hQ := euclideanGaussianLaw_map_coisometry (matrixCLM (whitenedMatrix A))
    (whitenedMatrix_coisometry A hA)
  have hfactor : (fun x => matrixCLM A x) =
      matrixCLM (covarianceRoot A) ∘ matrixCLM (whitenedMatrix A) := by
    funext x
    calc matrixCLM A x = matrixCLM (covarianceRoot A * whitenedMatrix A) x := by
            rw [covarianceRoot_mul_whitened A hA]
         _ = matrixCLM (covarianceRoot A) (matrixCLM (whitenedMatrix A) x) := by
            rw [matrixCLM_mul]
            rfl
  change Measure.map (fun x => matrixCLM A x) _ = _
  rw [hfactor, ← Measure.map_map (matrixCLM (covarianceRoot A)).continuous.measurable
    (matrixCLM (whitenedMatrix A)).continuous.measurable, hQ]

/-- Extended inverse square root of the genuine rectangular covariance determinant. -/
def covarianceInverseJacobian (A : Matrix ι κ ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt (covariance A).det))⁻¹

/-- The requested rectangular Gaussian-image small-ball bound, for actual iid
Gaussians and closed balls. Singular covariance correctly gives infinity. -/
theorem euclideanGaussian_rectangular_closedBall_le {k : ℕ}
    (hcard : Fintype.card ι = 2 * k) (hk : 0 < k) (A : Matrix ι κ ℝ)
    (c : EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R) :
    (euclideanGaussianLaw κ) (matrixCLM A ⁻¹' closedBall c R) ≤
      covarianceInverseJacobian A *
        ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  by_cases hA : (covariance A).det = 0
  · have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hC : ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) ≠ 0 := by
      apply ENNReal.ofReal_ne_zero_iff.mpr
      positivity
    simp only [covarianceInverseJacobian, hA, Real.sqrt_zero, ENNReal.ofReal_zero,
      ENNReal.inv_zero, ENNReal.top_mul hC]
    exact le_top
  · have hlaw := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) => μ (closedBall c R))
      (euclideanGaussian_matrix_map_eq_covarianceRoot A hA)
    rw [Measure.map_apply (matrixCLM A).continuous.measurable measurableSet_closedBall,
      Measure.map_apply (matrixCLM (covarianceRoot A)).continuous.measurable measurableSet_closedBall] at hlaw
    rw [hlaw]
    have h := euclideanGaussian_linear_closedBall_le_extended hcard hk
      (matrixCLM (covarianceRoot A)).toLinearMap c hR
    rw [covarianceRoot_inverseJacobian] at h
    exact h

/-- Conditional/random-center version expressed directly as a product law.
All matrix randomness is in the first factor; the driver Gaussian is independent. -/
theorem joint_euclideanGaussian_rectangular_closedBall_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {k : ℕ} (hcard : Fintype.card ι = 2 * k) (hk : 0 < k)
    (A : Ω → Matrix ι κ ℝ) (c : Ω → EuclideanSpace ℝ ι)
    {R : ℝ} (hR : 0 < R)
    (hjoint : Measurable (fun p : Ω × EuclideanSpace ℝ κ => matrixCLM (A p.1) p.2 - c p.1)) :
    (μ.prod (euclideanGaussianLaw κ))
        {p | ‖matrixCLM (A p.1) p.2 - c p.1‖ ≤ R} ≤
      (∫⁻ ω, covarianceInverseJacobian (A ω) ∂μ) *
        ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  letI : IsProbabilityMeasure (euclideanGaussianLaw κ) := by
    unfold euclideanGaussianLaw
    exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 (κ → ℝ)).measurable.aemeasurable
  have hS : MeasurableSet {p : Ω × EuclideanSpace ℝ κ |
      ‖matrixCLM (A p.1) p.2 - c p.1‖ ≤ R} := hjoint.norm measurableSet_Iic
  rw [Measure.prod_apply hS]
  calc _ ≤ ∫⁻ ω, covarianceInverseJacobian (A ω) *
      ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) ∂μ := by
        apply lintegral_mono
        intro ω
        dsimp only
        have heq : Prod.mk ω ⁻¹' {p : Ω × EuclideanSpace ℝ κ |
            ‖matrixCLM (A p.1) p.2 - c p.1‖ ≤ R} =
            matrixCLM (A ω) ⁻¹' closedBall (c ω) R := by
          ext x
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_closedBall, dist_eq_norm]
        rw [heq]
        exact euclideanGaussian_rectangular_closedBall_le hcard hk (A ω) (c ω) hR
    _ = _ := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.euclideanGaussian_rectangular_closedBall_le
#print axioms GaussianEllipsoid.SmallBall.joint_euclideanGaussian_rectangular_closedBall_le
