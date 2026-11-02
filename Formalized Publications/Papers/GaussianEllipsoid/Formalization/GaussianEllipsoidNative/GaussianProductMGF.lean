import GaussianQuadraticMGF
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace GaussianEllipsoidCandidate

/-- Standard normal linear exponential integral. -/
theorem gaussian_exp_linear_integral (s : ℝ) :
    (∫ x : ℝ, Real.exp (s * x) ∂gaussianReal 0 1) = Real.exp (s^2 / 2) := by
  have hh := mgf_gaussianReal (p := gaussianReal 0 1) (X := fun x : ℝ => x)
    (μ := 0) (v := 1) (by simpa using Measure.map_id (gaussianReal 0 1)) s
  simpa [mgf] using hh

/-- Nonnegative integral form of the standard normal linear MGF. -/
theorem gaussian_exp_linear_lintegral (s : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (s * x)) ∂gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (s^2 / 2)) := by
  have hi : Integrable (fun x : ℝ => Real.exp (s*x)) (gaussianReal 0 1) := by
    apply mgf_pos_iff.mp
    change 0 < ∫ x : ℝ, Real.exp (s*x) ∂gaussianReal 0 1
    rw [gaussian_exp_linear_integral]
    exact Real.exp_pos _
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _), gaussian_exp_linear_integral]

noncomputable def gaussianPairLaw : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

instance gaussianPairLaw_probability : IsProbabilityMeasure gaussianPairLaw := by
  unfold gaussianPairLaw
  infer_instance

/-- Exact MGF of the product of two independent standard normals, obtained
by nonnegative Fubini and the exponential-square integral. -/
theorem gaussian_pair_exp_lintegral (t : ℝ) (ht : t^2 < 1) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (t * (p.1 * p.2))) ∂gaussianPairLaw) =
      ENNReal.ofReal ((Real.sqrt (1 - t^2))⁻¹) := by
  unfold gaussianPairLaw
  rw [lintegral_prod _ (by fun_prop)]
  calc
    (∫⁻ x : ℝ, ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (t * (x*y)))
        ∂gaussianReal 0 1 ∂gaussianReal 0 1)
        = ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp ((t*x)^2 / 2)) ∂gaussianReal 0 1 := by
      apply lintegral_congr
      intro x
      simpa only [mul_assoc] using gaussian_exp_linear_lintegral (t*x)
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp ((t^2 / 2) * x^2)) ∂gaussianReal 0 1 := by
      apply lintegral_congr
      intro x
      congr 2
      ring
    _ = ENNReal.ofReal ((Real.sqrt (1 - t^2))⁻¹) := by
      rw [gaussian_exp_square_lintegral (t^2 / 2) (by linarith)]
      have heq : 1 - 2 * (t^2 / 2) = 1 - t^2 := by ring
      rw [heq]

/-- Integrability of the Gaussian product exponential on its exact finite radius. -/
theorem gaussian_pair_exp_integrable (t : ℝ) (ht : t^2 < 1) :
    Integrable (fun p : ℝ × ℝ => Real.exp (t * (p.1 * p.2))) gaussianPairLaw := by
  have hm : Measurable (fun p : ℝ × ℝ => Real.exp (t * (p.1 * p.2))) := by fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.exp_nonneg _)).2
  rw [gaussian_pair_exp_lintegral t ht]
  exact ENNReal.ofReal_lt_top

/-- Real MGF of an actual Gaussian product. -/
theorem gaussian_pair_mgf (t : ℝ) (ht : t^2 < 1) :
    mgf (fun p : ℝ × ℝ => p.1 * p.2) gaussianPairLaw t =
      (Real.sqrt (1 - t^2))⁻¹ := by
  unfold mgf
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun p => Real.exp_nonneg _)
    (gaussian_pair_exp_integrable t ht).aestronglyMeasurable,
    gaussian_pair_exp_lintegral t ht, ENNReal.toReal_ofReal (by positivity)]

/-- The elementary finite-radius replacement for the logarithmic determinant
estimate: (1-z)^(-1/2)<=exp(z) for 0<=z<=1/2. -/
theorem inv_sqrt_one_sub_le_exp (z : ℝ) (hz : 0 ≤ z) (hzhi : z ≤ 1 / 2) :
    (Real.sqrt (1-z))⁻¹ ≤ Real.exp z := by
  have hden : 0 < 1-z := by linarith
  have hfrac : (1-z)⁻¹ ≤ 1+2*z := by
    rw [← one_div]
    rw [div_le_iff₀ hden]
    have hh : 0 ≤ z * (1-2*z) := mul_nonneg hz (by linarith)
    nlinarith
  have hexp : 1 + 2*z ≤ Real.exp (2*z) := by
    simpa [add_comm] using Real.add_one_le_exp (2*z)
  apply (sq_le_sq₀ (by positivity) (Real.exp_nonneg z)).1
  rw [inv_pow, Real.sq_sqrt hden.le]
  have heq : (Real.exp z)^2 = Real.exp (2*z) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact hfrac.trans hexp

/-- The exact scalar Gaussian-product finite-radius MGF estimate. -/
theorem gaussian_pair_mgf_le (t : ℝ) (ht : t^2 ≤ 1 / 2) :
    mgf (fun p : ℝ × ℝ => p.1 * p.2) gaussianPairLaw t ≤ Real.exp (t^2) := by
  rw [gaussian_pair_mgf t (by linarith)]
  exact inv_sqrt_one_sub_le_exp (t^2) (sq_nonneg t) ht

#print axioms gaussian_exp_linear_integral
#print axioms gaussian_exp_linear_lintegral
#print axioms gaussian_pair_exp_lintegral
#print axioms gaussian_pair_exp_integrable
#print axioms gaussian_pair_mgf
#print axioms inv_sqrt_one_sub_le_exp
#print axioms gaussian_pair_mgf_le

end GaussianEllipsoidCandidate
