import GaussianRadialDensity
import RadialGammaLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianTensorMoments
open scoped ENNReal
namespace GaussianMixedNormHelpers

instance euclideanGaussianLaw_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (euclideanGaussianLaw ι) := by
  unfold euclideanGaussianLaw
  exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable

theorem gaussianDensityConstant_pos (ι : Type*) [Fintype ι] :
    0 < gaussianDensityConstant ι := by
  unfold gaussianDensityConstant
  exact pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))) _

/-- Normalization is proved from the actual iid Gaussian probability law. -/
theorem gaussianDensityConstant_mul_radialGaussianMass (ι : Type*) [Fintype ι] :
    gaussianDensityConstant ι *
      radialGaussianMass (volume : Measure (EuclideanSpace ℝ ι)) (1 / 2) = 1 := by
  have h : (∫ x : EuclideanSpace ℝ ι, (1 : ℝ) ∂euclideanGaussianLaw ι) = 1 := by simp
  rw [euclideanGaussianLaw_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      (by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (gaussianDensityConstant ι * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2))))
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at h
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (gaussianDensityConstant_pos ι).le
    (Real.exp_nonneg _)), smul_eq_mul, mul_one] at h
  rw [integral_const_mul] at h
  exact h

/-- Exact measure identity between iid Euclidean Gaussian and normalized radial density. -/
theorem euclideanGaussianLaw_eq_radialGaussianLaw (ι : Type*) [Fintype ι] [Nonempty ι] :
    euclideanGaussianLaw ι =
      radialGaussianLaw (volume : Measure (EuclideanSpace ℝ ι)) (1 / 2) := by
  have hpos := radialGaussianMass_pos (volume : Measure (EuclideanSpace ℝ ι))
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hC : gaussianDensityConstant ι =
      (radialGaussianMass (volume : Measure (EuclideanSpace ℝ ι)) (1 / 2))⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff (ne_of_gt hpos)).2 (gaussianDensityConstant_mul_radialGaussianMass ι)
  rw [euclideanGaussianLaw_eq_withDensity, radialGaussianLaw, hC]

/-- Squared norm of an actual standard Gaussian vector has its exact Gamma law. -/
theorem euclideanGaussianLaw_map_norm_sq (ι : Type*) [Fintype ι] [Nonempty ι] :
    (euclideanGaussianLaw ι).map (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2) =
      gammaMeasure ((Fintype.card ι : ℝ) / 2) (1 / 2) := by
  rw [euclideanGaussianLaw_eq_radialGaussianLaw,
    radialGaussianLaw_map_norm_sq _ (show (0 : ℝ) < 1 / 2 by norm_num),
    finrank_euclideanSpace]

/-- Exact negative norm moment for actual iid standard Gaussian coordinates. -/
theorem euclideanGaussianLaw_negative_moment (ι : Type*) [Fintype ι] [Nonempty ι]
    (s : ℕ) (hs : 2 * s < Fintype.card ι) :
    (∫ x : EuclideanSpace ℝ ι, ‖x‖ ^ (-(2 * (s : ℝ))) ∂euclideanGaussianLaw ι) =
      (1 / 2 : ℝ) ^ s * (Real.Gamma ((Fintype.card ι : ℝ) / 2 - s) /
        Real.Gamma ((Fintype.card ι : ℝ) / 2)) := by
  rw [euclideanGaussianLaw_eq_radialGaussianLaw]
  simpa only [finrank_euclideanSpace] using
    radialGaussianLaw_negative_moment (volume : Measure (EuclideanSpace ℝ ι))
      (show (0 : ℝ) < 1 / 2 by norm_num) s (by simpa only [finrank_euclideanSpace] using hs)

end GaussianMixedNormHelpers
