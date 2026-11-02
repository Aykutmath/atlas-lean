import GaussianRectangularSmallBall

/-! New reconstructed helper. The all-dimensional volume estimate follows
from Gaussian normalization, not an even-dimensional factorial identity. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Module
open GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.SmallBall
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Gaussian peak times the volume of its dimension-normalized ball. -/
theorem reconstructed_gaussian_peak_volume_normalized
    (hd : 0 < Fintype.card ι) :
    ENNReal.ofReal (gaussianDensityConstant ι) *
      volume (closedBall (0 : EuclideanSpace ℝ ι) (Real.sqrt (Fintype.card ι : ℝ))) ≤
      ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)/2)) := by
  letI : IsProbabilityMeasure (euclideanGaussianLaw ι) := by
    unfold euclideanGaussianLaw
    exact Measure.isProbabilityMeasure_map
      (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable
  let S := closedBall (0 : EuclideanSpace ℝ ι) (Real.sqrt (Fintype.card ι : ℝ))
  have hS : MeasurableSet S := measurableSet_closedBall
  have hlower : ENNReal.ofReal (gaussianDensityConstant ι *
        Real.exp (-((Fintype.card ι : ℝ)/2))) * volume S ≤ 1 := by
    calc
      _ = ∫⁻ x in S, ENNReal.ofReal (gaussianDensityConstant ι *
          Real.exp (-((Fintype.card ι : ℝ)/2))) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in S, ENNReal.ofReal (gaussianDensityConstant ι *
          Real.exp (-(1/2:ℝ)*‖x‖^2)) := by
        apply setLIntegral_mono' hS
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by unfold gaussianDensityConstant; positivity)
        apply Real.exp_le_exp.mpr
        have hx' : ‖x‖ ≤ Real.sqrt (Fintype.card ι : ℝ) := by
          simpa only [S, mem_closedBall, dist_zero_right] using hx
        have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ) ≤ Fintype.card ι)
        nlinarith [norm_nonneg x]
      _ = euclideanGaussianLaw ι S := by
        rw [euclideanGaussianLaw_eq_withDensity, withDensity_apply _ hS]
      _ ≤ 1 := prob_le_one
  have hmul := mul_le_mul_right hlower (ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ)/2)))
  rw [mul_one, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hmul
  have heq : Real.exp ((Fintype.card ι : ℝ)/2) *
      (gaussianDensityConstant ι * Real.exp (-((Fintype.card ι : ℝ)/2))) =
      gaussianDensityConstant ι := by
    rw [mul_left_comm, ← Real.exp_add]
    simp
  rw [heq] at hmul
  exact hmul

/-- Arbitrary-dimensional peak-volume bound obtained by scaling the normalized
ball; in particular there is no parity restriction. -/
theorem reconstructed_gaussian_peak_volume (hd : 0 < Fintype.card ι)
    (c : EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R) :
    ENNReal.ofReal (gaussianDensityConstant ι) * volume (closedBall c R) ≤
      ENNReal.ofReal ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
        Real.exp ((Fintype.card ι : ℝ)/2)) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp hd
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have h := mul_le_mul_left (reconstructed_gaussian_peak_volume_normalized (ι := ι) hd)
    (ENNReal.ofReal ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι)))
  rw [← ENNReal.ofReal_mul (by positivity)] at h
  rw [EuclideanSpace.volume_closedBall] at h ⊢
  have hrad : R^(Fintype.card ι) =
      (R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
        (Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) := by
    rw [← mul_pow, div_mul_cancel₀ _ hs.ne']
  rw [← ENNReal.ofReal_pow hR.le, hrad, ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_pow hs.le] at h
  convert h using 1 <;> ac_rfl

/-- All-dimensional Gaussian linear-image small ball with extended Jacobian. -/
theorem reconstructed_euclideanGaussian_linear_closedBall
    (hd : 0 < Fintype.card ι)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (c : EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R) :
    euclideanGaussianLaw ι (T ⁻¹' closedBall c R) ≤
      inverseJacobian T * ENNReal.ofReal
        ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
          Real.exp ((Fintype.card ι : ℝ)/2)) := by
  by_cases hT : LinearMap.det T = 0
  · have hC : ENNReal.ofReal
        ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
          Real.exp ((Fintype.card ι : ℝ)/2)) ≠ 0 := by
      apply ENNReal.ofReal_ne_zero_iff.mpr
      have hdR : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr hd
      positivity
    simp only [inverseJacobian, hT, abs_zero, ENNReal.ofReal_zero,
      ENNReal.inv_zero, ENNReal.top_mul hC]
    exact le_top
  · rw [euclideanGaussianLaw_eq_withDensity]
    have h := withDensity_linear_preimage_le
      (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal
        (gaussianDensityConstant ι * Real.exp (-(1/2:ℝ)*‖x‖^2)))
      (ENNReal.ofReal (gaussianDensityConstant ι)) gaussian_radial_density_le
      T hT (closedBall c R)
    have hj : ENNReal.ofReal |(LinearMap.det T)⁻¹| = inverseJacobian T := by
      rw [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.mpr hT)]
      rfl
    rw [hj] at h
    calc
      _ ≤ ENNReal.ofReal (gaussianDensityConstant ι) * inverseJacobian T *
          volume (closedBall c R) := h
      _ = inverseJacobian T * (ENNReal.ofReal (gaussianDensityConstant ι) *
          volume (closedBall c R)) := by ac_rfl
      _ ≤ _ := mul_le_mul_right (reconstructed_gaussian_peak_volume hd c hR) _

/-- The whitening argument applies unchanged in odd as well as even dimension. -/
theorem reconstructed_euclideanGaussian_rectangular_closedBall
    (hd : 0 < Fintype.card ι) (A : Matrix ι κ ℝ)
    (c : EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R) :
    euclideanGaussianLaw κ (matrixCLM A ⁻¹' closedBall c R) ≤
      covarianceInverseJacobian A * ENNReal.ofReal
        ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
          Real.exp ((Fintype.card ι : ℝ)/2)) := by
  by_cases hA : (covariance A).det = 0
  · have hC : ENNReal.ofReal
        ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
          Real.exp ((Fintype.card ι : ℝ)/2)) ≠ 0 := by
      apply ENNReal.ofReal_ne_zero_iff.mpr
      have hdR : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr hd
      positivity
    simp only [covarianceInverseJacobian, hA, Real.sqrt_zero, ENNReal.ofReal_zero,
      ENNReal.inv_zero, ENNReal.top_mul hC]
    exact le_top
  · have hlaw := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) => μ (closedBall c R))
      (euclideanGaussian_matrix_map_eq_covarianceRoot A hA)
    rw [Measure.map_apply (matrixCLM A).continuous.measurable measurableSet_closedBall,
      Measure.map_apply (matrixCLM (covarianceRoot A)).continuous.measurable
        measurableSet_closedBall] at hlaw
    rw [hlaw]
    have h := reconstructed_euclideanGaussian_linear_closedBall hd
      (matrixCLM (covarianceRoot A)).toLinearMap c hR
    rw [covarianceRoot_inverseJacobian] at h
    exact h

theorem joint_euclideanGaussian_rectangular_closedBall_le_all_dimensions
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (hd : 0 < Fintype.card ι) (A : Ω → Matrix ι κ ℝ)
    (c : Ω → EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R)
    (hjoint : Measurable (fun p : Ω × EuclideanSpace ℝ κ => matrixCLM (A p.1) p.2-c p.1)) :
    (μ.prod (euclideanGaussianLaw κ)) {p | ‖matrixCLM (A p.1) p.2-c p.1‖ ≤ R} ≤
      (∫⁻ ω, covarianceInverseJacobian (A ω) ∂μ) * ENNReal.ofReal
        ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
          Real.exp ((Fintype.card ι : ℝ)/2)) := by
  letI : IsProbabilityMeasure (euclideanGaussianLaw κ) := by
    unfold euclideanGaussianLaw
    exact Measure.isProbabilityMeasure_map
      (MeasurableEquiv.toLp 2 (κ → ℝ)).measurable.aemeasurable
  have hS : MeasurableSet {p : Ω × EuclideanSpace ℝ κ |
      ‖matrixCLM (A p.1) p.2-c p.1‖ ≤ R} := hjoint.norm measurableSet_Iic
  rw [Measure.prod_apply hS]
  calc
    _ ≤ ∫⁻ ω, covarianceInverseJacobian (A ω) * ENNReal.ofReal
        ((R/Real.sqrt (Fintype.card ι : ℝ))^(Fintype.card ι) *
          Real.exp ((Fintype.card ι : ℝ)/2)) ∂μ := by
      apply lintegral_mono
      intro ω
      dsimp only
      have heq : Prod.mk ω ⁻¹' {p : Ω × EuclideanSpace ℝ κ |
          ‖matrixCLM (A p.1) p.2-c p.1‖ ≤ R} =
          matrixCLM (A ω) ⁻¹' closedBall (c ω) R := by
        ext x
        simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_closedBall, dist_eq_norm]
      rw [heq]
      exact reconstructed_euclideanGaussian_rectangular_closedBall hd (A ω) (c ω) hR
    _ = _ := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.joint_euclideanGaussian_rectangular_closedBall_le_all_dimensions
