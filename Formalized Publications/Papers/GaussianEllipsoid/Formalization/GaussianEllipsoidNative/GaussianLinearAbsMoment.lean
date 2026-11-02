import Mathlib.MeasureTheory.Order.Group.Lattice
import GaussianFiniteMGF
import FiniteProductMoment
import BMGaussianEquivalent

noncomputable section
open MeasureTheory ProbabilityTheory Real GaussianTensorMoments GaussianEllipsoidCandidate
open BMQuadraticStein BMGaussianEquivalent
open scoped BigOperators ENNReal
namespace BMGOEUniform

/-- Actual finite Gaussian linear measurement. -/
def linearObservable {ι : Type*} [Fintype ι] (w : ι → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ i, w i*z i

lemma exp_abs_le_exp_add_exp_neg (x : ℝ) : exp |x| ≤ exp x + exp (-x) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (exp_nonneg _)
  · rw [abs_of_nonpos hx]
    exact le_add_of_nonneg_left (exp_nonneg _)

/-- Exponential absolute integrability and a concrete bound under the actual
independent Gaussian coordinate law. -/
theorem gaussian_linear_exp_abs {ι : Type*} (w : ι → ℝ) [Fintype ι]
    (hw : (∑ i, (w i)^2) ≤ 2) :
    Integrable (fun z => exp |linearObservable w z|) (gaussianProductLaw ι) ∧
    (∫ z, exp |linearObservable w z| ∂gaussianProductLaw ι) ≤ 2*exp 1 := by
  have hIp := gaussian_vector_linear_integrable w 1
  have hIn := gaussian_vector_linear_integrable w (-1)
  simp only [one_mul] at hIp
  simp only [neg_one_mul] at hIn
  change Integrable (fun z => exp (linearObservable w z)) (gaussianProductLaw ι) at hIp
  change Integrable (fun z => exp (-linearObservable w z)) (gaussianProductLaw ι) at hIn
  have hm : Measurable (linearObservable w) := by unfold linearObservable; fun_prop
  have hIbound : Integrable (fun z => exp (linearObservable w z) + exp (-linearObservable w z))
      (gaussianProductLaw ι) := hIp.add hIn
  have hi : Integrable (fun z => exp |linearObservable w z|) (gaussianProductLaw ι) := by
    apply hIbound.mono' hm.abs.exp.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_abs_le_exp_add_exp_neg _)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z, exp (linearObservable w z) + exp (-linearObservable w z) ∂gaussianProductLaw ι :=
      integral_mono hi hIbound (fun _ => exp_abs_le_exp_add_exp_neg _)
    _ = exp ((1^2/2)*(∑ i, (w i)^2)) + exp (((-1)^2/2)*(∑ i, (w i)^2)) := by
      rw [integral_add hIp hIn]
      congr 1
      · simpa only [one_mul, linearObservable] using gaussian_vector_linear_integral w 1
      · simpa only [neg_one_mul, linearObservable] using gaussian_vector_linear_integral w (-1)
    _ ≤ 2*exp 1 := by
      have hh : exp ((1:ℝ)/2 * ∑ i, (w i)^2) ≤ exp 1 :=
        exp_le_exp.mpr (by linarith)
      norm_num only [one_pow, neg_one_sq] at ⊢
      linarith

/-- Every absolute scalar moment is factorially bounded. These moments are
proved from the Gaussian integral, rather than supplied as hypotheses. -/
theorem gaussian_linear_abs_factorial_moment {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : (∑ i, (w i)^2) ≤ 2) (k : ℕ) :
    Integrable (fun z => |linearObservable w z|^k) (gaussianProductLaw ι) ∧
    (∫ z, |linearObservable w z|^k ∂gaussianProductLaw ι) ≤
      (k.factorial:ℝ)*(2*exp 1)^k := by
  by_cases hk : k=0
  · subst k; simp
  have he := gaussian_linear_exp_abs w hw
  have hp (z : ι → ℝ) : |linearObservable w z|^k ≤
      (k.factorial:ℝ)*exp |linearObservable w z| := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<k.factorial)).mp
      (Real.pow_div_factorial_le_exp |linearObservable w z| (abs_nonneg _) k)
    simpa only [mul_comm] using h
  have hm : Measurable (linearObservable w) := by unfold linearObservable; fun_prop
  have hi : Integrable (fun z => |linearObservable w z|^k) (gaussianProductLaw ι) := by
    apply (he.1.const_mul (k.factorial:ℝ)).mono' (hm.abs.pow_const k).aestronglyMeasurable
    exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hp z)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z, (k.factorial:ℝ)*exp |linearObservable w z| ∂gaussianProductLaw ι :=
      integral_mono hi (he.1.const_mul _) hp
    _ = (k.factorial:ℝ)*(∫ z, exp |linearObservable w z| ∂gaussianProductLaw ι) := integral_const_mul _ _
    _ ≤ (k.factorial:ℝ)*(2*exp 1) := mul_le_mul_of_nonneg_left he.2 (by positivity)
    _ ≤ (k.factorial:ℝ)*(2*exp 1)^k := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hbase : 1 ≤ 2*exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      simpa only [pow_one] using pow_le_pow_right₀ hbase (Nat.one_le_iff_ne_zero.mpr hk)

/-- Exact squared coefficient energy of the full-entry GOE realization. -/
theorem gaussianCoefficients_sq_sum {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    (∑ k, (gaussianCoefficients A k)^2) = 2/(d:ℝ)*frobeniusSq A := by
  rw [← (finProdFinEquiv : Fin d × Fin d ≃ Fin (d*d)).sum_comp
    (fun k => (gaussianCoefficients A k)^2)]
  simp only [gaussianCoefficients, Equiv.symm_apply_apply, Fintype.sum_prod_type, mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ 2/(d:ℝ)), frobeniusSq, Finset.mul_sum]

theorem gaussianCoefficients_sq_sum_le {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : spectralNorm A ≤ 1) :
    (∑ k, (gaussianCoefficients A k)^2) ≤ 2 := by
  rw [gaussianCoefficients_sq_sum]
  have hf := frobeniusSq_le_card_spectralNorm_sq A
  simp only [Fintype.card_fin] at hf
  have hn : spectralNorm A^2 ≤ 1 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) hA 2).trans_eq (by norm_num)
  have hh : frobeniusSq A ≤ (d:ℝ) := by
    exact hf.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring))
  calc
    _ ≤ 2/(d:ℝ)*(d:ℝ) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 2 := by field_simp

/-- Literal GOE trace measurement equals the finite Gaussian linear form. -/
theorem goe_trace_eq_linear {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (z : Fin (d*d) → ℝ) :
    Matrix.trace (symmetrizedGaussianMatrix d z*A) = linearObservable (gaussianCoefficients A) z := by
  rw [trace_symmetrizedGaussianMatrix_mul A hA]
  simp [linearObservable, BMAffineSmooth.linearPolynomial]

/-- Actual GOE fixed-matrix absolute factorial moments. -/
theorem goe_trace_factorial_moment {d : ℕ} (hd : 0 < d)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A) (hN : spectralNorm A ≤ 1) (k : ℕ) :
    Integrable (fun z => |Matrix.trace (symmetrizedGaussianMatrix d z*A)|^k)
      (gaussianProductLaw (Fin (d*d))) ∧
    (∫ z, |Matrix.trace (symmetrizedGaussianMatrix d z*A)|^k ∂gaussianProductLaw (Fin (d*d))) ≤
      (k.factorial:ℝ)*(2*exp 1)^k := by
  simp_rw [goe_trace_eq_linear A hA]
  exact gaussian_linear_abs_factorial_moment _ (gaussianCoefficients_sq_sum_le hd A hN) k

#print axioms gaussian_linear_exp_abs
#print axioms gaussian_linear_abs_factorial_moment
#print axioms gaussianCoefficients_sq_sum_le
#print axioms goe_trace_factorial_moment
end BMGOEUniform
