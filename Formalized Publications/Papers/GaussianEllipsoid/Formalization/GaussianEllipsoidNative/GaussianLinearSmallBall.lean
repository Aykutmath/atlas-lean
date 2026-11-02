import DensitySmallBall
import GaussianRadialDensity

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Module
open GaussianMixedNormHelpers
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall

variable {ι : Type*} [Fintype ι]

/-- In even dimension the actual Gaussian density constant is an integer power. -/
theorem gaussianDensityConstant_even {k : ℕ} (hk : Fintype.card ι = 2 * k) :
    gaussianDensityConstant ι = (1 / (2 * Real.pi)) ^ k := by
  unfold gaussianDensityConstant
  rw [hk, pow_mul]
  have hs : (Real.sqrt (2 * Real.pi))⁻¹ ^ 2 = (2 * Real.pi)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [hs]
  simp only [one_div]

/-- The actual standard Gaussian density is bounded by its value at the origin. -/
theorem gaussian_radial_density_le (x : EuclideanSpace ℝ ι) :
    ENNReal.ofReal (gaussianDensityConstant ι * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)) ≤
      ENNReal.ofReal (gaussianDensityConstant ι) := by
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [sq_nonneg ‖x‖]
  have hC : 0 ≤ gaussianDensityConstant ι := by unfold gaussianDensityConstant; positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC

/-- A genuine Gaussian linear-image small-ball theorem: the Gaussian law is
not replaced by an assumed density or a small-ball predicate. -/
theorem euclideanGaussian_linear_closedBall_le {k : ℕ}
    (hcard : Fintype.card ι = 2 * k) (hk : 0 < k)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hT : LinearMap.det T ≠ 0) (c : EuclideanSpace ℝ ι)
    {R : ℝ} (hR : 0 ≤ R) :
    euclideanGaussianLaw ι (T ⁻¹' closedBall c R) ≤
      ENNReal.ofReal |(LinearMap.det T)⁻¹| *
        ENNReal.ofReal ((R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  have hι : 0 < Fintype.card ι := by omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hι
  have hdim : finrank ℝ (EuclideanSpace ℝ ι) = 2 * k := by simpa using hcard
  rw [euclideanGaussianLaw_eq_withDensity]
  have h := withDensity_linear_closedBall_le_of_dim_even hdim
    (fun x : EuclideanSpace ℝ ι => ENNReal.ofReal
      (gaussianDensityConstant ι * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2)))
    (ENNReal.ofReal (gaussianDensityConstant ι)) gaussian_radial_density_le T hT c R
  rw [gaussianDensityConstant_even hcard] at h
  have hc := gaussian_density_ball_coefficient_ennreal_le (ell := 1) hk (by positivity) hR
    (ENNReal.ofReal |(LinearMap.det T)⁻¹|)
  simpa only [gaussianDensityConstant_even hcard] using h.trans (by simpa only [one_mul] using hc)

/-- Gaussian linear-image small balls at the dimension-normalized radius. -/
theorem euclideanGaussian_linear_normalized_closedBall_le {k : ℕ}
    (hcard : Fintype.card ι = 2 * k) (hk : 0 < k)
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hT : LinearMap.det T ≠ 0) (c : EuclideanSpace ℝ ι)
    {t : ℝ} (ht : 0 ≤ t) :
    euclideanGaussianLaw ι (T ⁻¹' closedBall c (t * Real.sqrt (2 * (k : ℝ)))) ≤
      ENNReal.ofReal |(LinearMap.det T)⁻¹| *
        ENNReal.ofReal ((Real.sqrt (Real.exp 1) * t) ^ (2 * k)) := by
  have h := euclideanGaussian_linear_closedBall_le hcard hk T hT c
    (R := t * Real.sqrt (2 * (k : ℝ))) (by positivity)
  have he := gaussian_normalized_radius_coefficient (ell := 1) hk (by positivity) t
  simp only [div_one, one_mul] at he
  rw [he] at h
  exact h

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.euclideanGaussian_linear_closedBall_le
#print axioms GaussianEllipsoid.SmallBall.euclideanGaussian_linear_normalized_closedBall_le
