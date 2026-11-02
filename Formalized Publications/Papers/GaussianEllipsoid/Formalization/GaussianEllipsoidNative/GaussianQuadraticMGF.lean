import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace GaussianEllipsoidCandidate

/-- Exact exponential-square integral for an actual standard Gaussian law. -/
theorem gaussian_exp_square_integral (a : ℝ) (ha : a < 1 / 2) :
    (∫ x : ℝ, Real.exp (a * x^2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * a))⁻¹ := by
  have hδ : 0 < (1 / 2 : ℝ) - a := by linarith
  have hD : 0 < 1 - 2 * a := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  calc
    (∫ x : ℝ, Real.exp (a * x^2) ∂gaussianReal 0 1)
        = ∫ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(x^2) / 2) * Real.exp (a * x^2) := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-((1 / 2 : ℝ) - a) * x^2) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / ((1 / 2 : ℝ) - a)) := by
      rw [integral_gaussian]
    _ = (Real.sqrt (1 - 2 * a))⁻¹ := by
      apply (sq_eq_sq₀ (by positivity) (by positivity)).1
      rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi),
        Real.sq_sqrt (by positivity : 0 ≤ Real.pi / ((1 / 2 : ℝ) - a)),
        inv_pow, Real.sq_sqrt hD.le]
      field_simp [ne_of_gt hπ, ne_of_gt hδ, ne_of_gt hD]
      <;> ring

/-- Integrability is proved from the exact positive Gaussian integral. -/
theorem gaussian_exp_square_integrable (a : ℝ) (ha : a < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (a * x^2)) (gaussianReal 0 1) := by
  apply mgf_pos_iff.mp
  change 0 < ∫ x : ℝ, Real.exp (a * x^2) ∂gaussianReal 0 1
  rw [gaussian_exp_square_integral a ha]
  have hD : 0 < 1 - 2 * a := by linarith
  exact inv_pos.mpr (Real.sqrt_pos.mpr hD)

/-- The nonnegative integral form can feed kernel iteration without an
extra Bochner-integrability premise. -/
theorem gaussian_exp_square_lintegral (a : ℝ) (ha : a < 1 / 2) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (a * x^2)) ∂gaussianReal 0 1) =
      ENNReal.ofReal ((Real.sqrt (1 - 2 * a))⁻¹) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_exp_square_integrable a ha)
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
  rw [gaussian_exp_square_integral a ha]

#print axioms gaussian_exp_square_integral
#print axioms gaussian_exp_square_integrable
#print axioms gaussian_exp_square_lintegral

end GaussianEllipsoidCandidate
