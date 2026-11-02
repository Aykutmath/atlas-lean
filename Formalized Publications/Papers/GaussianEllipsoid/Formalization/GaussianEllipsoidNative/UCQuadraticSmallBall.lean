import UCQuadraticMGF
import UCProductConcentration
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open scoped BigOperators
namespace GaussianEllipsoid.UCQuadraticSmallBall

def row {d : ℕ} (A : Square d) (x : Vector d) : ℝ :=
  (quadratic A x - Matrix.trace A) / Real.sqrt 2

def clip (t : ℝ) : ℝ := min 1 |t|

theorem clip_nonneg (t : ℝ) : 0 ≤ clip t := le_min zero_le_one (abs_nonneg t)
theorem clip_le_one (t : ℝ) : clip t ≤ 1 := min_le_left _ _
theorem clip_le_abs (t : ℝ) : clip t ≤ |t| := min_le_right _ _
theorem measurable_clip : Measurable clip := measurable_const.min measurable_id.abs

theorem row_eval {d : ℕ} (A : Square d) (x : Vector d) :
    row A x = MvPolynomial.eval x ((1 / Real.sqrt 2) • centeredQuadratic A) := by
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_centeredQuadratic, row, quadratic_eq_sum, Finset.mul_sum]
  congr 1
  simp only [mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, one_mul]

theorem measurable_row {d : ℕ} (A : Square d) : Measurable (row A) := by
  unfold row
  simp only [quadratic_eq_sum, Finset.mul_sum]
  fun_prop

theorem row_integrable_pow {d : ℕ} (A : Square d) (k : ℕ) :
    Integrable (fun x => row A x ^ k) (gaussianVectorLaw d) := by
  simpa only [MvPolynomial.eval_pow, ← row_eval, gaussianVectorLaw, gaussianProductLaw] using
    gaussianProductLaw_integrable_polynomial (((1 / Real.sqrt 2) • centeredQuadratic A)^k)

theorem row_mean {d : ℕ} (A : Square d) :
    (∫ x, row A x ∂gaussianVectorLaw d) = 0 := by
  have he : expectation ((1 / Real.sqrt 2) • centeredQuadratic A) = 0 := by
    rw [map_smul, expectation_centeredQuadratic, smul_zero]
  simpa only [expectation, LinearMap.coe_mk, AddHom.coe_mk,
    ← row_eval, gaussianProductLaw, gaussianVectorLaw] using he

theorem row_second_moment {d : ℕ} (A : Square d) (hA : A.transpose = A)
    (hF : frobeniusNorm A = 1) :
    (∫ x, row A x ^ 2 ∂gaussianVectorLaw d) = 1 := by
  have h := expectation_centeredQuadratic_covariance_symmetric A A hA
  have hsum : (∑ i, ∑ j, A i j * A i j) = 1 := by
    simpa only [← pow_two, ← frobeniusNorm_sq, hF, one_pow] using (frobeniusNorm_sq A).symm
  rw [hsum] at h
  have he : ((1 / Real.sqrt 2) • centeredQuadratic A)^2 =
      (1 / 2 : ℝ) • (centeredQuadratic A * centeredQuadratic A) := by
    simp only [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow]
    congr 1
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    · norm_num
    · rw [pow_two]
  have hev : (∫ x, row A x ^ 2 ∂gaussianVectorLaw d) =
      expectation (((1 / Real.sqrt 2) • centeredQuadratic A)^2) := by
    simp only [expectation, LinearMap.coe_mk, AddHom.coe_mk,
      MvPolynomial.eval_pow, ← row_eval, gaussianProductLaw, gaussianVectorLaw]
  rw [hev, he, map_smul, h]
  norm_num

theorem fourth_le_exp (t : ℝ) : t^4 ≤ 98304 * Real.exp (|t|/8) := by
  have h := Real.pow_div_factorial_le_exp (|t|/8) (by positivity) 4
  norm_num [div_pow, show |t|^4=t^4 from (Even.pow_abs (by decide : Even 4) t)] at h
  linarith

theorem row_fourth_moment {d : ℕ} (hd : 0 < d) (A : Square d)
    (hA : A.transpose = A) (hF : frobeniusNorm A ≤ 1) :
    (∫ x, row A x^4 ∂gaussianVectorLaw d) ≤ 600000 := by
  have hi := UCQuadraticMGF.quadratic_exp_abs hd A hA hF
  have h := integral_mono (row_integrable_pow A 4) (hi.1.const_mul 98304)
    (fun x => fourth_le_exp (row A x))
  rw [integral_const_mul] at h
  have h' : (∫ x, Real.exp (|row A x|/8) ∂gaussianVectorLaw d) ≤ 2*Real.exp 1 := hi.2
  nlinarith [Real.exp_one_lt_three]

theorem sub_fourth_le (u v : ℝ) : (u-v)^4 ≤ 8*(u^4+v^4) := by
  have h : (u-v)^2 ≤ 2*(u^2+v^2) := by nlinarith [sq_nonneg (u+v)]
  have hh := pow_le_pow_left₀ (sq_nonneg (u-v)) h 2
  nlinarith [sq_nonneg (u^2-v^2)]

theorem paired_integrable_second {d : ℕ} (A : Square d) :
    Integrable (fun z : Vector d × Vector d => (row A z.1-row A z.2)^2)
      ((gaussianVectorLaw d).prod (gaussianVectorLaw d)) := by
  have h1 : Integrable (row A) (gaussianVectorLaw d) := by
    simpa using row_integrable_pow A 1
  have h2 := row_integrable_pow A 2
  apply (((h2.comp_fst _).sub ((h1.mul_prod h1).const_mul 2)).add (h2.comp_snd _)).congr
  exact ae_of_all _ fun z => by simp only [Pi.add_apply, Pi.sub_apply]; ring

theorem paired_second_moment {d : ℕ} (A : Square d) (hA : A.transpose = A)
    (hF : frobeniusNorm A = 1) :
    (∫ z : Vector d × Vector d, (row A z.1-row A z.2)^2
      ∂(gaussianVectorLaw d).prod (gaussianVectorLaw d)) = 2 := by
  have h1 : Integrable (row A) (gaussianVectorLaw d) := by
    simpa using row_integrable_pow A 1
  have h2 := row_integrable_pow A 2
  have he : (fun z : Vector d × Vector d => (row A z.1-row A z.2)^2) =
      fun z => row A z.1^2 - 2*(row A z.1*row A z.2)+row A z.2^2 := by
    funext z; ring
  rw [he]
  have hiSub : Integrable (fun z : Vector d × Vector d => row A z.1^2 -
      2*(row A z.1*row A z.2)) ((gaussianVectorLaw d).prod (gaussianVectorLaw d)) :=
    (h2.comp_fst _).sub ((h1.mul_prod h1).const_mul 2)
  rw [integral_add hiSub (h2.comp_snd _),
    integral_sub (h2.comp_fst _) ((h1.mul_prod h1).const_mul 2), integral_const_mul,
    integral_prod_mul]

  rw [integral_fun_fst (fun x => row A x^2), integral_fun_snd (fun x => row A x^2)]
  simp only [probReal_univ, one_smul, row_mean, row_second_moment A hA hF]
  norm_num

theorem paired_integrable_fourth {d : ℕ} (A : Square d) :
    Integrable (fun z : Vector d × Vector d => (row A z.1-row A z.2)^4)
      ((gaussianVectorLaw d).prod (gaussianVectorLaw d)) := by
  apply (((row_integrable_pow A 4).comp_fst _).add
    ((row_integrable_pow A 4).comp_snd _)).const_mul 8 |>.mono'
      (((measurable_row A).comp measurable_fst).sub
        ((measurable_row A).comp measurable_snd) |>.pow_const 4).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.add_apply, Function.comp_apply,
      abs_pow, Even.pow_abs (by decide : Even 4)] using
      sub_fourth_le (row A z.1) (row A z.2)

theorem paired_fourth_moment {d : ℕ} (hd : 0 < d) (A : Square d)
    (hA : A.transpose = A) (hF : frobeniusNorm A ≤ 1) :
    (∫ z : Vector d × Vector d, (row A z.1-row A z.2)^4
      ∂(gaussianVectorLaw d).prod (gaussianVectorLaw d)) ≤ 10000000 := by
  have h4 := row_integrable_pow A 4
  have h := integral_mono (paired_integrable_fourth A)
    (((h4.comp_fst _).add (h4.comp_snd _)).const_mul 8)
    (fun z => sub_fourth_le (row A z.1) (row A z.2))
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add (h4.comp_fst _) (h4.comp_snd _)] at h
  rw [integral_fun_fst (fun x => row A x^4), integral_fun_snd (fun x => row A x^4)] at h
  simp only [probReal_univ, one_smul] at h
  have hu := row_fourth_moment hd A hA hF
  linarith

theorem squared_le_clip_fourth (t : ℝ) :
    t^2 ≤ 10000000*clip t + t^4/10000000 := by
  by_cases h : |t| ≤ 1
  · rw [clip, min_eq_right h]
    have hs : t^2 ≤ |t| := by nlinarith [sq_abs t, abs_nonneg t]
    have hp : 0 ≤ t^4 := by positivity
    nlinarith [abs_nonneg t]
  · rw [clip, min_eq_left (le_of_not_ge h)]
    nlinarith [sq_nonneg (t^2-5000000)]

/-- Universal paired-row small-ball mass. Both Gaussian moments and their
integrability are proved for the actual project row, with no rank dependence. -/
theorem paired_clip_mean {d : ℕ} (hd : 0 < d) (A : Square d)
    (hA : A.transpose = A) (hF : frobeniusNorm A = 1) :
    (1/10000000:ℝ) ≤
      ∫ z : Vector d × Vector d, clip (row A z.1-row A z.2)
        ∂(gaussianVectorLaw d).prod (gaussianVectorLaw d) := by
  have hm : Measurable (fun z : Vector d × Vector d => clip (row A z.1-row A z.2)) :=
    measurable_clip.comp (((measurable_row A).comp measurable_fst).sub
      ((measurable_row A).comp measurable_snd))
  have hi := UCProductConcentration.integrable_of_abs_bound
    (μ := (gaussianVectorLaw d).prod (gaussianVectorLaw d)) hm
    (fun z => show |clip (row A z.1-row A z.2)| ≤ 1 by
      rw [abs_of_nonneg (clip_nonneg _)]; exact clip_le_one _)
  have h := integral_mono (paired_integrable_second A)
    ((hi.const_mul 10000000).add ((paired_integrable_fourth A).div_const 10000000))
    (fun z => squared_le_clip_fourth (row A z.1-row A z.2))
  simp only [Pi.add_apply] at h
  rw [integral_add (hi.const_mul _) ((paired_integrable_fourth A).div_const _),
    integral_const_mul, integral_div, paired_second_moment A hA hF] at h
  have h4 := paired_fourth_moment hd A hA hF.le
  linarith

#print axioms paired_clip_mean
end GaussianEllipsoid.UCQuadraticSmallBall
