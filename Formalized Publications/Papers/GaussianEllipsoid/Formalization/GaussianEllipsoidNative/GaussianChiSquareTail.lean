import GaussianFiniteMGF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real GaussianTensorMoments
open scoped ENNReal NNReal

namespace GaussianEllipsoidCandidate

/-- Convert a squared exponential comparison to an inverse-square-root one. -/
theorem inv_sqrt_le_exp_of_sq (a b : ℝ) (ha : 0 ≤ a)
    (h : a⁻¹ ≤ Real.exp (2*b)) : (Real.sqrt a)⁻¹ ≤ Real.exp b := by
  apply (sq_le_sq₀ (by positivity) (Real.exp_nonneg b)).1
  rw [inv_pow, Real.sq_sqrt ha, pow_two, ← Real.exp_add]
  simpa only [two_mul] using h

/-- Numerical upper-tail exponential factor; only log(x)<=x-1 is used. -/
theorem chi_square_plus_factor :
    (Real.sqrt (1 - 2 * (1 / 32 : ℝ)))⁻¹ ≤ Real.exp (1 / 30) := by
  apply inv_sqrt_le_exp_of_sq _ _ (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16 / 15)
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 16 / 15)] at hh
  norm_num at hh ⊢
  exact hh

/-- Numerical lower-tail exponential factor from the same elementary log inequality. -/
theorem chi_square_minus_factor :
    (Real.sqrt (1 - 2 * (-1 / 32 : ℝ)))⁻¹ ≤ Real.exp (-1 / 34) := by
  apply inv_sqrt_le_exp_of_sq _ _ (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16 / 17)
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 16 / 17)] at hh
  norm_num at hh ⊢
  exact hh

/-- Exact chi-square MGF under the actual finite Gaussian product law. -/
theorem gaussian_square_sum_mgf {ι : Type*} [Fintype ι] (t : ℝ) (ht : t < 1 / 2) :
    mgf (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) t =
      (Real.sqrt (1 - 2*t))⁻¹ ^ Fintype.card ι := by
  unfold mgf
  simp_rw [Finset.mul_sum]
  rw [gaussian_vector_quadratic_integral (fun _ : ι => t) (fun _ => ht)]
  simp

/-- Integrability on the entire exact chi-square exponential radius. -/
theorem gaussian_square_sum_exp_integrable {ι : Type*} [Fintype ι]
    (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ι → ℝ => Real.exp (t * ∑ i, (x i)^2)) (gaussianProductLaw ι) := by
  simpa only [Finset.mul_sum] using
    gaussian_vector_quadratic_integrable (fun _ : ι => t) (fun _ => ht)

/-- The fixed positive Chernoff parameter used for sparse singular-value nets. -/
theorem gaussian_square_sum_mgf_plus {ι : Type*} [Fintype ι] :
    mgf (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) (1 / 32) ≤
      Real.exp ((Fintype.card ι : ℝ) / 30) := by
  rw [gaussian_square_sum_mgf (1 / 32) (by norm_num)]
  calc
    (Real.sqrt (1 - 2 * (1 / 32 : ℝ)))⁻¹ ^ Fintype.card ι
        ≤ (Real.exp (1 / 30)) ^ Fintype.card ι :=
      pow_le_pow_left₀ (by positivity) chi_square_plus_factor _
    _ = Real.exp ((Fintype.card ι : ℝ) / 30) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The fixed negative Chernoff parameter used for sparse singular-value nets. -/
theorem gaussian_square_sum_mgf_minus {ι : Type*} [Fintype ι] :
    mgf (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) (-1 / 32) ≤
      Real.exp (-(Fintype.card ι : ℝ) / 34) := by
  rw [gaussian_square_sum_mgf (-1 / 32) (by norm_num)]
  calc
    (Real.sqrt (1 - 2 * (-1 / 32 : ℝ)))⁻¹ ^ Fintype.card ι
        ≤ (Real.exp (-1 / 34)) ^ Fintype.card ι :=
      pow_le_pow_left₀ (by positivity) chi_square_minus_factor _
    _ = Real.exp (-(Fintype.card ι : ℝ) / 34) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Actual chi-square upper deviation at relative error 1/4. -/
theorem gaussian_square_sum_upper {ι : Type*} [Fintype ι] :
    (gaussianProductLaw ι).real {x : ι → ℝ | (5 / 4 : ℝ) * Fintype.card ι ≤ ∑ i, (x i)^2} ≤
      Real.exp (-(Fintype.card ι : ℝ) / 256) := by
  have hh := measure_ge_le_exp_mul_mgf (μ := gaussianProductLaw ι)
    (X := fun x : ι → ℝ => ∑ i, (x i)^2) ((5/4 : ℝ)*Fintype.card ι)
    (t := 1 / 32) (by norm_num) (gaussian_square_sum_exp_integrable (1/32) (by norm_num))
  apply hh.trans
  calc
    Real.exp (-(1/32 : ℝ) * ((5/4 : ℝ)*Fintype.card ι)) *
        mgf (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) (1/32)
        ≤ Real.exp (-(1/32 : ℝ) * ((5/4 : ℝ)*Fintype.card ι)) *
          Real.exp ((Fintype.card ι : ℝ)/30) :=
      mul_le_mul_of_nonneg_left gaussian_square_sum_mgf_plus (Real.exp_nonneg _)
    _ ≤ Real.exp (-(Fintype.card ι : ℝ)/256) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      nlinarith

/-- Actual chi-square lower deviation at relative error 1/4. -/
theorem gaussian_square_sum_lower {ι : Type*} [Fintype ι] :
    (gaussianProductLaw ι).real {x : ι → ℝ | (∑ i, (x i)^2) ≤ (3 / 4 : ℝ) * Fintype.card ι} ≤
      Real.exp (-(Fintype.card ι : ℝ) / 256) := by
  have hh := measure_le_le_exp_mul_mgf (μ := gaussianProductLaw ι)
    (X := fun x : ι → ℝ => ∑ i, (x i)^2) ((3/4 : ℝ)*Fintype.card ι)
    (t := -1 / 32) (by norm_num) (gaussian_square_sum_exp_integrable (-1/32) (by norm_num))
  apply hh.trans
  calc
    Real.exp (-(-1/32 : ℝ) * ((3/4 : ℝ)*Fintype.card ι)) *
        mgf (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) (-1/32)
        ≤ Real.exp (-(-1/32 : ℝ) * ((3/4 : ℝ)*Fintype.card ι)) *
          Real.exp (-(Fintype.card ι : ℝ)/34) :=
      mul_le_mul_of_nonneg_left gaussian_square_sum_mgf_minus (Real.exp_nonneg _)
    _ ≤ Real.exp (-(Fintype.card ι : ℝ)/256) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      nlinarith

/-- The two-sided chi-square tail required for an elementary sphere-net proof.
No Davidson-Szarek or Gaussian singular-value bound is used. -/
theorem gaussian_square_sum_two_sided {ι : Type*} [Fintype ι] :
    (gaussianProductLaw ι).real {x : ι → ℝ |
      (Fintype.card ι : ℝ) / 4 ≤ |(∑ i, (x i)^2) - Fintype.card ι|} ≤
      2 * Real.exp (-(Fintype.card ι : ℝ)/256) := by
  have heq : {x : ι → ℝ | (Fintype.card ι : ℝ)/4 ≤ |(∑ i, (x i)^2) - Fintype.card ι|} =
      {x : ι → ℝ | (5/4 : ℝ)*Fintype.card ι ≤ ∑ i, (x i)^2} ∪
      {x : ι → ℝ | (∑ i, (x i)^2) ≤ (3/4 : ℝ)*Fintype.card ι} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
  rw [heq]
  exact (measureReal_union_le _ _).trans (by
    simpa only [two_mul] using add_le_add (gaussian_square_sum_upper (ι := ι))
      (gaussian_square_sum_lower (ι := ι)))

#print axioms inv_sqrt_le_exp_of_sq
#print axioms chi_square_plus_factor
#print axioms chi_square_minus_factor
#print axioms gaussian_square_sum_mgf
#print axioms gaussian_square_sum_exp_integrable
#print axioms gaussian_square_sum_mgf_plus
#print axioms gaussian_square_sum_mgf_minus
#print axioms gaussian_square_sum_upper
#print axioms gaussian_square_sum_lower
#print axioms gaussian_square_sum_two_sided

end GaussianEllipsoidCandidate
