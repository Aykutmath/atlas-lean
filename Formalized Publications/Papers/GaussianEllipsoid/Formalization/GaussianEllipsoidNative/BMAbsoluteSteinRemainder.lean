import BMGibbsPriorDomination

open MeasureTheory GaussianTensorMoments BMQuadraticStein BMSmoothQuadraticComposition BMSmoothSteinBounds
open scoped BoundedContinuousFunction
namespace BMFiniteGibbsTest

/-- Absolute, rather than squared, Stein remainder control. This form can
be summed against prior masses without a state-count loss. -/
theorem normalizedKernelFluctuation_abs_bounded_test_le
    (d : ℕ) (hd : 0 < d) (A B : Matrix (Fin d) (Fin d) ℝ)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    |boundedExpectation f (normalizedKernelFluctuation d A B)| ≤
      Real.sqrt (8/(d:ℝ))*spectralNorm A*spectralNorm B*‖f‖ := by
  have hA : 0 ≤ spectralNorm A := by unfold spectralNorm; positivity
  have hB : 0 ≤ spectralNorm B := by unfold spectralNorm; positivity
  have hR : 0 ≤ Real.sqrt (8/(d:ℝ))*spectralNorm A*spectralNorm B*‖f‖ := by positivity
  apply (sq_le_sq₀ (abs_nonneg _) hR).1
  rw [sq_abs]
  calc
    _ ≤ (8/(d:ℝ)*spectralNorm A^2*spectralNorm B^2)*‖f‖^2 :=
      normalizedKernelFluctuation_bounded_test_sq_le d hd A B f
    _ = _ := by
      simp only [mul_pow]
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8/(d:ℝ))]

/-- Uniform spectral-cap specialization used in finite-prior Gibbs bounds. -/
theorem normalizedKernelFluctuation_abs_le_of_spectral_le
    (d : ℕ) (hd : 0 < d) (A B : Matrix (Fin d) (Fin d) ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hA : spectralNorm A ≤ K) (hB : spectralNorm B ≤ K)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    |boundedExpectation f (normalizedKernelFluctuation d A B)| ≤
      (Real.sqrt (8/(d:ℝ))*K^2)*‖f‖ := by
  have hAn : 0 ≤ spectralNorm A := by unfold spectralNorm; positivity
  have hBn : 0 ≤ spectralNorm B := by unfold spectralNorm; positivity
  apply (normalizedKernelFluctuation_abs_bounded_test_le d hd A B f).trans
  have hp := mul_le_mul hA hB hBn hK
  have hm := mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg (8/(d:ℝ)))
  have hh := mul_le_mul_of_nonneg_right hm (norm_nonneg f)
  simpa only [mul_assoc, pow_two] using hh

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Diagonal and pair Hessian contractions against actual quadratic Stein
remainders, with a constant independent of the number of Gibbs states. -/
theorem prior_weighted_stein_remainder_sum_le
    (d : ℕ) (hd : 0 < d) (D : Data κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) {K C₁ C₂ : ℝ}
    (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (f : κ → ((Fin d → ℝ) →ᵇ ℝ))
    (g : κ → κ → ((Fin d → ℝ) →ᵇ ℝ))
    (hf : ∀ a, ‖f a‖ ≤ C₁*D.weight a)
    (hg : ∀ a b, ‖g a b‖ ≤ C₂*(D.weight a*D.weight b)) :
    |(∑ a, boundedExpectation (f a) (normalizedKernelFluctuation d (A a) (A a))) -
      ∑ a, ∑ b, boundedExpectation (g a b) (normalizedKernelFluctuation d (A a) (A b))| ≤
      (Real.sqrt (8/(d:ℝ))*K^2)*(C₁+C₂) := by
  let R := Real.sqrt (8/(d:ℝ))*K^2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hdiag : |∑ a, boundedExpectation (f a) (normalizedKernelFluctuation d (A a) (A a))| ≤ R*C₁ := by
    calc
      _ ≤ ∑ a, |boundedExpectation (f a) (normalizedKernelFluctuation d (A a) (A a))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, R*(C₁*D.weight a) := by
        apply Finset.sum_le_sum
        intro a _
        exact (normalizedKernelFluctuation_abs_le_of_spectral_le d hd (A a) (A a)
          hK (hA a) (hA a) (f a)).trans (mul_le_mul_of_nonneg_left (hf a) hR)
      _ = R*C₁ := by simp only [← Finset.mul_sum, D.weight_sum, mul_one]
  have hpair : |∑ a, ∑ b, boundedExpectation (g a b)
      (normalizedKernelFluctuation d (A a) (A b))| ≤ R*C₂ := by
    calc
      _ ≤ ∑ a, |∑ b, boundedExpectation (g a b)
          (normalizedKernelFluctuation d (A a) (A b))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, R*(C₂*(D.weight a*D.weight b)) := by
        apply Finset.sum_le_sum
        intro a _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro b _
        exact (normalizedKernelFluctuation_abs_le_of_spectral_le d hd (A a) (A b)
          hK (hA a) (hA b) (g a b)).trans (mul_le_mul_of_nonneg_left (hg a b) hR)
      _ = R*C₂ := by simp only [← Finset.mul_sum, D.weight_sum, mul_one]
  exact (abs_sub _ _).trans (by dsimp [R] at hdiag hpair; nlinarith)

#print axioms normalizedKernelFluctuation_abs_bounded_test_le
#print axioms normalizedKernelFluctuation_abs_le_of_spectral_le
#print axioms prior_weighted_stein_remainder_sum_le
end BMFiniteGibbsTest
