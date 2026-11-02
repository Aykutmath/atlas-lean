import BMSmoothQuadraticComposition

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace BMSmoothSteinBounds

/-- The elementary discriminant argument underlying Cauchy–Schwarz. -/
theorem sq_le_mul_of_quadratic_nonneg {a b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t, 0 ≤ a - 2*t*b + t^2*c) : b^2 ≤ a*c := by
  by_cases hc0 : c = 0
  · by_cases hb0 : b = 0
    · simp [hb0, hc0]
    · have hh := h ((a+1)/(2*b))
      have he : a - 2*((a+1)/(2*b))*b + ((a+1)/(2*b))^2*c = -1 := by
        rw [hc0]
        field_simp [hb0]
        <;> ring
      rw [he] at hh
      norm_num at hh
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hh := mul_nonneg (h (b/c)) hc
    have he : (a-2*(b/c)*b+(b/c)^2*c)*c = a*c-b^2 := by
      field_simp [hc0]
      <;> ring
    rw [he] at hh
    linarith

/-- The actual Gaussian L² pairing with a bounded continuous test is controlled
without any polynomial assumption on the test. -/
theorem boundedExpectation_sq_le {d : ℕ} (P : MvPolynomial (Fin d) ℝ)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    (boundedExpectation f P)^2 ≤ expectation (P^2) * ‖f‖^2 := by
  let μ := gaussianProductLaw (Fin d)
  have hp : Integrable (fun x => (eval x P)^2) μ := by
    have h := gaussianProductLaw_integrable_polynomial (P^2)
    convert h using 1
    funext x
    exact (map_pow (eval x) P 2).symm
  have hpf : Integrable (fun x => eval x P*f x) μ := integrable_poly_bounded f P
  have hf2 : Integrable (fun x => (f x)^2) μ := by
    simpa only [map_one, one_mul, pow_two, BoundedContinuousFunction.mul_apply] using
      integrable_poly_bounded (f*f) (1 : MvPolynomial (Fin d) ℝ)
  have hquad (t : ℝ) : 0 ≤ (∫ x, (eval x P)^2 ∂μ) -
      2*t*(∫ x, eval x P*f x ∂μ) + t^2*(∫ x, (f x)^2 ∂μ) := by
    have hn : 0 ≤ ∫ x, (eval x P-t*f x)^2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have he (x : Fin d → ℝ) : (eval x P-t*f x)^2 =
        (eval x P)^2 - 2*t*(eval x P*f x) + t^2*(f x)^2 := by ring
    simp_rw [he] at hn
    have hi1 : Integrable (fun x => (eval x P)^2 - 2*t*(eval x P*f x)) μ :=
      hp.sub (hpf.const_mul (2*t))
    rw [integral_add hi1 (hf2.const_mul (t^2)),
      integral_sub hp (hpf.const_mul (2*t)), integral_const_mul, integral_const_mul] at hn
    exact hn
  have hcs := sq_le_mul_of_quadratic_nonneg
    (integral_nonneg (μ := μ) (fun x => sq_nonneg (f x))) hquad
  have hfb : (∫ x, (f x)^2 ∂μ) ≤ ‖f‖^2 := by
    calc
      _ ≤ ∫ _ : Fin d → ℝ, ‖f‖^2 ∂μ := integral_mono hf2 (integrable_const _) (fun x => by
        simpa only [Real.norm_eq_abs, sq_abs] using
          pow_le_pow_left₀ (norm_nonneg (f x)) (f.norm_coe_le_norm x) 2)
      _ = _ := by simp [μ]
  have hpp : (∫ x, (eval x P)^2 ∂μ) = expectation (P^2) := by
    simp only [expectation, LinearMap.coe_mk, AddHom.coe_mk, eval_pow, μ]
  change (∫ x, eval x P*f x ∂μ)^2 ≤ _
  rw [hpp] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hfb (expectation_sq_nonneg P))

/-- The centered normalized quadratic Stein kernel has a uniform smooth-test
bound of order d⁻¹/², expressed without square roots. -/
theorem normalizedKernelFluctuation_bounded_test_sq_le
    (d : ℕ) (hd : 0 < d) (A B : Matrix (Fin d) (Fin d) ℝ)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    (boundedExpectation f (normalizedKernelFluctuation d A B))^2 ≤
      (8 / (d : ℝ) * spectralNorm A^2 * spectralNorm B^2) * ‖f‖^2 := by
  exact (boundedExpectation_sq_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (normalizedKernelFluctuation_second_moment_le_spectral d hd A B) (sq_nonneg _))

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Fully nonpolynomial finite-dimensional Stein discrepancy bound. Every
integrability and Gaussian identity is proved; only the C¹ bounded test class
and the input matrices are parameters. -/
theorem smooth_normalized_vector_discrepancy_sq_le
    (d : ℕ) (hd : 0 < d) (F : SmoothTest κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a) (a : κ) :
    (boundedExpectation (composedTest F (fun b => normalizedQuadratic d (A b)))
        (normalizedQuadratic d (A a)) -
      ∑ b, (2 / (d : ℝ) * Matrix.trace (A a*A b)) *
        boundedExpectation (composedGradient F (fun b => normalizedQuadratic d (A b)) b) 1)^2 ≤
      (Fintype.card κ : ℝ) * ∑ b,
        (8 / (d : ℝ) * spectralNorm (A a)^2 * spectralNorm (A b)^2) * ‖F.gradient b‖^2 := by
  rw [boundedExpectation_normalized_vector_stein F A hA a,
    Finset.sum_add_distrib, add_sub_cancel_left]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : κ => (1 : ℝ))
    (fun b => boundedExpectation (composedGradient F (fun b => normalizedQuadratic d (A b)) b)
      (normalizedKernelFluctuation d (A a) (A b)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  refine hcs.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity))
  calc
    _ ≤ (8 / (d : ℝ) * spectralNorm (A a)^2 * spectralNorm (A b)^2) *
        ‖composedGradient F (fun b => normalizedQuadratic d (A b)) b‖^2 :=
      normalizedKernelFluctuation_bounded_test_sq_le d hd (A a) (A b) _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (BoundedContinuousFunction.norm_compContinuous_le _ _) 2)
      (by positivity)

#print axioms boundedExpectation_sq_le
#print axioms smooth_normalized_vector_discrepancy_sq_le
end BMSmoothSteinBounds
