import GaussianProductMGF
import GaussianProductLinearForms
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real GaussianTensorMoments
open scoped ENNReal NNReal

namespace GaussianEllipsoidCandidate

/-- Exact diagonal quadratic exponential integral under the actual iid
Gaussian vector law, by finite-product Fubini. -/
theorem gaussian_vector_quadratic_integral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1 / 2) :
    (∫ x : ι → ℝ, Real.exp (∑ i, a i * (x i)^2) ∂gaussianProductLaw ι) =
      ∏ i, (Real.sqrt (1 - 2 * a i))⁻¹ := by
  classical
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) := inferInstanceAs (SigmaFinite (gaussianReal 0 1))
  calc
    (∫ x : ι → ℝ, Real.exp (∑ i, a i * (x i)^2) ∂gaussianProductLaw ι)
        = ∫ x : ι → ℝ, ∏ i, Real.exp (a i * (x i)^2) ∂gaussianProductLaw ι := by
      congr 1
      funext x
      exact Real.exp_sum _ _
    _ = ∏ i, ∫ x : ℝ, Real.exp (a i * x^2) ∂gaussianReal 0 1 := by
      simpa only [gaussianProductLaw, volume_pi] using
        integral_fintype_prod_eq_prod (μ := fun _ => gaussianReal 0 1) (fun i (x : ℝ) => Real.exp (a i * x^2))
    _ = ∏ i, (Real.sqrt (1 - 2 * a i))⁻¹ :=
      Finset.prod_congr rfl fun i _ => gaussian_exp_square_integral (a i) (ha i)

/-- Integrability of a diagonal Gaussian quadratic exponential is derived
from its exact strictly positive product integral. -/
theorem gaussian_vector_quadratic_integrable {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1 / 2) :
    Integrable (fun x : ι → ℝ => Real.exp (∑ i, a i * (x i)^2)) (gaussianProductLaw ι) := by
  have hpos : 0 < mgf (fun x : ι → ℝ => ∑ i, a i * (x i)^2) (gaussianProductLaw ι) 1 := by
    simp only [mgf, one_mul]
    rw [gaussian_vector_quadratic_integral a ha]
    apply Finset.prod_pos
    intro i _
    have hd : 0 < 1 - 2 * a i := by linarith [ha i]
    exact inv_pos.mpr (Real.sqrt_pos.mpr hd)
  simpa only [one_mul] using mgf_pos_iff.mp hpos

/-- The diagonal quadratic formula in nonnegative-integral form. -/
theorem gaussian_vector_quadratic_lintegral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1 / 2) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (Real.exp (∑ i, a i * (x i)^2)) ∂gaussianProductLaw ι) =
      ENNReal.ofReal (∏ i, (Real.sqrt (1 - 2 * a i))⁻¹) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_vector_quadratic_integrable a ha)
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _), gaussian_vector_quadratic_integral a ha]

/-- Uniform finite-radius quadratic bound, with the exact trace-type exponent. -/
theorem gaussian_vector_quadratic_integral_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ 1 / 4) :
    (∫ x : ι → ℝ, Real.exp (∑ i, a i * (x i)^2) ∂gaussianProductLaw ι) ≤
      Real.exp (2 * ∑ i, a i) := by
  classical
  rw [gaussian_vector_quadratic_integral a (fun i => by linarith [ha i])]
  calc
    ∏ i, (Real.sqrt (1 - 2 * a i))⁻¹ ≤ ∏ i, Real.exp (2 * a i) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact inv_sqrt_one_sub_le_exp (2 * a i) (by linarith [ha0 i]) (by linarith [ha i])
    _ = Real.exp (2 * ∑ i, a i) := by rw [← Real.exp_sum, ← Finset.mul_sum]

/-- Exact Gaussian linear MGF for arbitrary coefficients, without a norm-one
normalization or a separate Gaussian-law identification hypothesis. -/
theorem gaussian_vector_linear_integral {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (t : ℝ) :
    (∫ x : ι → ℝ, Real.exp (t * ∑ i, w i * x i) ∂gaussianProductLaw ι) =
      Real.exp ((t^2 / 2) * ∑ i, (w i)^2) := by
  classical
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) := inferInstanceAs (SigmaFinite (gaussianReal 0 1))
  calc
    (∫ x : ι → ℝ, Real.exp (t * ∑ i, w i * x i) ∂gaussianProductLaw ι)
        = ∫ x : ι → ℝ, ∏ i, Real.exp ((t * w i) * x i) ∂gaussianProductLaw ι := by
      congr 1
      funext x
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    _ = ∏ i, ∫ x : ℝ, Real.exp ((t * w i) * x) ∂gaussianReal 0 1 := by
      simpa only [gaussianProductLaw, volume_pi] using
        integral_fintype_prod_eq_prod (μ := fun _ => gaussianReal 0 1) (fun i (x : ℝ) => Real.exp ((t*w i)*x))
    _ = ∏ i, Real.exp ((t*w i)^2 / 2) :=
      Finset.prod_congr rfl fun i _ => gaussian_exp_linear_integral (t*w i)
    _ = Real.exp ((t^2 / 2) * ∑ i, (w i)^2) := by
      rw [← Real.exp_sum, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Integrability of the arbitrary Gaussian linear exponential. -/
theorem gaussian_vector_linear_integrable {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (t : ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (t * ∑ i, w i*x i)) (gaussianProductLaw ι) := by
  apply (mgf_pos_iff (X := fun x : ι → ℝ => ∑ i, w i*x i) (t := t)).mp
  change 0 < ∫ x : ι → ℝ, Real.exp (t * ∑ i, w i*x i) ∂gaussianProductLaw ι
  rw [gaussian_vector_linear_integral]
  exact Real.exp_pos _

/-- Gaussian linear MGF in the nonnegative form used for conditional Fubini. -/
theorem gaussian_vector_linear_lintegral {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (t : ℝ) :
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (Real.exp (t * ∑ i, w i*x i)) ∂gaussianProductLaw ι) =
      ENNReal.ofReal (Real.exp ((t^2 / 2) * ∑ i, (w i)^2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_vector_linear_integrable w t)
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _), gaussian_vector_linear_integral w t]

#print axioms gaussian_vector_quadratic_integral
#print axioms gaussian_vector_quadratic_integrable
#print axioms gaussian_vector_quadratic_lintegral
#print axioms gaussian_vector_quadratic_integral_le
#print axioms gaussian_vector_linear_integral
#print axioms gaussian_vector_linear_integrable
#print axioms gaussian_vector_linear_lintegral

end GaussianEllipsoidCandidate
