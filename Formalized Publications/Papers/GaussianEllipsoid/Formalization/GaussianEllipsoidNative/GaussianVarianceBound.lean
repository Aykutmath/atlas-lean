import GaussianDiscreteVariance
import GaussianSlopeLimit

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers Filter
open scoped BigOperators InnerProductSpace Topology
namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

/-- Actual finite-dimensional Gaussian variance control for every 1-Lipschitz
observable, proved by stationary discrete rotations and Rademacher's theorem. -/
theorem lipschitz_gaussian_variance_le {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    variance f (euclideanGaussianLaw ι) ≤ Real.pi^2/8 := by
  have ht := (slope_sq_limit hf).const_mul ((Real.pi/2)^2)
  have hfinite (n : ℕ) :
      (∫ z : E ι × E ι, (f z.2-f z.1)^2 ∂γ₂ ι) ≤
        (Real.pi/2)^2 * ∫ z, ((f (first (angleStep n) z)-f z.1)/(angleStep n))^2 ∂γ₂ ι := by
    simpa only [first_pi_div_two, angleStep, Nat.cast_add, Nat.cast_one] using
      finite_slope_bound hf (Real.pi/2) (by positivity) (n+1) (by omega)
  have hlimit := ge_of_tendsto ht (Eventually.of_forall hfinite)
  rw [pair_difference_eq_twice_variance hf] at hlimit
  have hb := mul_le_mul_of_nonneg_left (integral_tangent_sq_le_one hf)
    (sq_nonneg (Real.pi/2))
  change 2*variance f (euclideanGaussianLaw ι) ≤ _ at hlimit
  nlinarith

/-- In particular, bounded-gradient C¹ observables satisfy the same actual
Gaussian dimension-free bound. Only differentiability is needed. -/
theorem differentiable_gaussian_variance_le {f : E ι → ℝ}
    (hf : Differentiable ℝ f) (hg : ∀ x, ‖fderiv ℝ f x‖ ≤ 1) :
    variance f (euclideanGaussianLaw ι) ≤ Real.pi^2/8 := by
  apply lipschitz_gaussian_variance_le
  exact lipschitzWith_of_nnnorm_fderiv_le hf (fun x => by
    exact_mod_cast hg x)

/-- A nonnegative Gaussian support function with known second moment has
mean at least the square root of that moment minus an absolute constant. -/
theorem mean_lower_of_second_moment {f : E ι → ℝ} (hf : LipschitzWith 1 f)
    (hpos : ∀ x, 0 ≤ f x) {m : ℝ}
    (hm : (∫ x, (f x)^2 ∂euclideanGaussianLaw ι) = m) :
    Real.sqrt (m-Real.pi^2/8) ≤ ∫ x, f x ∂euclideanGaussianLaw ι := by
  have hv := lipschitz_gaussian_variance_le hf
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
    (lipschitz_sq_integrable hf))] at hv
  simp only [Pi.pow_apply] at hv
  rw [hm] at hv
  have hmean : 0 ≤ ∫ x, f x ∂euclideanGaussianLaw ι := integral_nonneg hpos
  exact (Real.sqrt_le_iff).mpr ⟨hmean, by linarith⟩

#print axioms lipschitz_gaussian_variance_le
#print axioms differentiable_gaussian_variance_le
#print axioms mean_lower_of_second_moment
end GaussianVariance
