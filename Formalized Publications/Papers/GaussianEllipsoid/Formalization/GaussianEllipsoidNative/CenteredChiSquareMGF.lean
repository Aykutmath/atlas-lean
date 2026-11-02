import GaussianQuadraticMGF
import GaussianProductMoments
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaussianEllipsoidCandidate

/-- Exact centered chi-square MGF under the actual scalar Gaussian law. -/
theorem gaussian_centered_square_integral (a : ℝ) (ha : a < 1/2) :
    (∫ x : ℝ, Real.exp (a * (x^2-1)) ∂gaussianReal 0 1) =
      Real.exp (-a) * (Real.sqrt (1-2*a))⁻¹ := by
  have he (x : ℝ) : Real.exp (a*(x^2-1)) = Real.exp (-a) * Real.exp (a*x^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul, gaussian_exp_square_integral a ha]

theorem gaussian_centered_square_integrable (a : ℝ) (ha : a < 1/2) :
    Integrable (fun x : ℝ => Real.exp (a * (x^2-1))) (gaussianReal 0 1) := by
  have he : (fun x : ℝ => Real.exp (a*(x^2-1))) =
      fun x => Real.exp (-a) * Real.exp (a*x^2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (gaussian_exp_square_integrable a ha).const_mul _

/-- Elementary centered chi-square log-MGF bound on a fixed two-sided radius. -/
theorem centered_square_mgf_factor_le (a : ℝ) (ha : |a| ≤ 1/4) :
    Real.exp (-a) * (Real.sqrt (1-2*a))⁻¹ ≤ Real.exp (4*a^2) := by
  have ha' := abs_le.mp ha
  have hb : 0 < 1-2*a := by linarith
  have hs : 0 < Real.sqrt (1-2*a) := Real.sqrt_pos.mpr hb
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hb)
  rw [Real.log_inv] at hl
  have hfrac : ((1-2*a)⁻¹ - 1)/2 - a ≤ 4*a^2 := by
    have he : ((1-2*a)⁻¹ - 1)/2 - a = 2*a^2/(1-2*a) := by
      field_simp
      ring
    rw [he]
    apply (div_le_iff₀ hb).2
    have hh : 0 ≤ 1-4*a := by linarith
    nlinarith [mul_nonneg (sq_nonneg a) hh]
  rw [← Real.exp_log (inv_pos.mpr hs), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_inv, Real.log_sqrt hb.le]
  linarith

/-- Actual Gaussian centered-square exponential estimate, with all
integrability and Gaussian distribution facts internal. -/
theorem gaussian_centered_square_mgf_le (a : ℝ) (ha : |a| ≤ 1/4) :
    (∫ x : ℝ, Real.exp (a * (x^2-1)) ∂gaussianReal 0 1) ≤ Real.exp (4*a^2) := by
  rw [gaussian_centered_square_integral a (lt_of_le_of_lt (le_trans (le_abs_self a) ha) (by norm_num))]
  exact centered_square_mgf_factor_le a ha

/-- The finite independent centered-square exponential is integrable on its
exact coordinatewise radius. -/
theorem gaussian_weighted_centered_squares_integrable {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1/2) :
    Integrable (fun x : ι → ℝ => Real.exp (∑ i, a i * ((x i)^2-1)))
      (GaussianTensorMoments.gaussianProductLaw ι) := by
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod_dep (μ := fun _ => gaussianReal 0 1)
    (fun i => gaussian_centered_square_integrable (a i) (ha i))

/-- Exact finite product MGF of a weighted centered diagonal Gaussian quadratic. -/
theorem gaussian_weighted_centered_squares_integral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1/2) :
    (∫ x : ι → ℝ, Real.exp (∑ i, a i * ((x i)^2-1))
      ∂GaussianTensorMoments.gaussianProductLaw ι) =
      ∏ i, Real.exp (-a i) * (Real.sqrt (1-2*a i))⁻¹ := by
  simp_rw [Real.exp_sum]
  rw [GaussianTensorMoments.gaussianProductLaw_integral_prod (fun i (x : ℝ) => Real.exp (a i * (x^2-1)))]
  exact Finset.prod_congr rfl (fun i _ => gaussian_centered_square_integral (a i) (ha i))

/-- Actual independent diagonal Gaussian quadratic MGF bound. -/
theorem gaussian_weighted_centered_squares_mgf_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, |a i| ≤ 1/4) :
    (∫ x : ι → ℝ, Real.exp (∑ i, a i * ((x i)^2-1))
      ∂GaussianTensorMoments.gaussianProductLaw ι) ≤
      Real.exp (4 * ∑ i, (a i)^2) := by
  rw [gaussian_weighted_centered_squares_integral a
    (fun i => lt_of_le_of_lt (le_trans (le_abs_self _) (ha i)) (by norm_num))]
  calc
    _ ≤ ∏ i, Real.exp (4*(a i)^2) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact centered_square_mgf_factor_le (a i) (ha i)
    _ = _ := by rw [← Real.exp_sum, Finset.mul_sum]

#print axioms gaussian_centered_square_integral
#print axioms gaussian_centered_square_integrable
#print axioms centered_square_mgf_factor_le
#print axioms gaussian_centered_square_mgf_le
#print axioms gaussian_weighted_centered_squares_integrable
#print axioms gaussian_weighted_centered_squares_integral
#print axioms gaussian_weighted_centered_squares_mgf_le
end GaussianEllipsoidCandidate
