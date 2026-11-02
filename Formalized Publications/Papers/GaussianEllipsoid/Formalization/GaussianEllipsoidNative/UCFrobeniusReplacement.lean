import BMRowSteinCancellation
import UCFrobeniusStein
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMRowInterpolation BMRowSteinCancellation
open MvPolynomial GaussianEllipsoid.UCFrobeniusStein
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCFrobeniusReplacement
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {d m : ℕ}

def firstSlice (y : Fin m → ℝ) : C((Fin d → ℝ), SamplePair d m) where
  toFun x := (x,y)
  continuous_toFun := continuous_id.prodMk continuous_const

/-- The actual independent-pair integral has the same centered-kernel bound as
its first Gaussian factor. The Hessian coefficient can depend on both factors. -/
theorem mixed_kernel_pair_abs_le
    (H : κ → SmoothTest κ) (t : ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (B : κ → Fin m → ℝ)
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (hAB : ∀ a b, 8/(d:ℝ)^2 * frobeniusSq (A a*A b) ≤ R₀^2)
    (a b : κ) :
    |∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
      mixedHessian H t (fun b => normalizedQuadratic d (A b))
        (fun b => linearPolynomial (B b)) a b z ∂law d m| ≤
      R₀*‖(H a).gradient b‖ := by
  let q := fun b => normalizedQuadratic d (A b)
  let g := fun b => linearPolynomial (B b)
  let R := normalizedKernelFluctuation d (A a) (A b)
  let f := mixedHessian H t q g a b
  have hi := integrable_fst_poly_mul R f
  have hp (y : Fin m → ℝ) :
      |∫ x, eval x R * f (x,y) ∂gaussianProductLaw (Fin d)| ≤
        R₀*‖(H a).gradient b‖ := by
    change |boundedExpectation (f.compContinuous (firstSlice y)) R| ≤ _
    apply (kernel_bounded_test_abs_le d (A a) (A b) hR₀ (hAB a b) (f.compContinuous (firstSlice y))).trans
    apply mul_le_mul_of_nonneg_left _ hR₀
    exact (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
      (BoundedContinuousFunction.norm_compContinuous_le _ _)
  change |∫ z, eval z.1 R*f z ∂law d m| ≤ _
  simp only [law]
  rw [integral_prod_symm _ hi]
  have h := norm_integral_le_of_norm_le_const (μ := gaussianProductLaw (Fin m))
    (Filter.Eventually.of_forall fun y => (show
      ‖∫ x, eval x R*f (x,y) ∂gaussianProductLaw (Fin d)‖ ≤
        R₀*‖(H a).gradient b‖ from hp y))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- Summing absolute Stein remainders costs only the sum of Hessian coefficient
norms, not the number of states times a maximum. -/
theorem mixed_kernel_sum_abs_le
    (H : κ → SmoothTest κ) (t : ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (B : κ → Fin m → ℝ)
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (hAB : ∀ a b, 8/(d:ℝ)^2 * frobeniusSq (A a*A b) ≤ R₀^2) :
    |∑ a, ∑ b, ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
      mixedHessian H t (fun b => normalizedQuadratic d (A b))
        (fun b => linearPolynomial (B b)) a b z ∂law d m| ≤
      R₀ * ∑ a, ∑ b, ‖(H a).gradient b‖ := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a, ∑ b, R₀*‖(H a).gradient b‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum fun b _ => mixed_kernel_pair_abs_le H t A B R₀ hR₀ hAB a b
    _ = _ := by simp only [← Finset.mul_sum]

/-- Endpoints of the interpolation are the original quadratic measurements and
the actual covariance-matched Gaussian linear forms. -/
theorem expected_mixedValue_zero (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    (∫ z, mixedValue F 0 q g z ∂law d m) =
      ∫ x, F.value (polynomialFamily q x) ∂gaussianProductLaw (Fin d) := by
  simpa only [law, mixedValue, BoundedContinuousFunction.compContinuous_apply,
    mixMap, ContinuousMap.coe_mk, Real.cos_zero, Real.sin_zero, one_smul, zero_smul,
    add_zero, probReal_univ, one_smul] using
    (integral_fun_fst (μ := gaussianProductLaw (Fin d)) (ν := gaussianProductLaw (Fin m))
      (fun x => F.value (polynomialFamily q x)))

theorem expected_mixedValue_pi_div_two (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    (∫ z, mixedValue F (Real.pi/2) q g z ∂law d m) =
      ∫ x, F.value (polynomialFamily g x) ∂gaussianProductLaw (Fin m) := by
  simpa only [law, mixedValue, BoundedContinuousFunction.compContinuous_apply,
    mixMap, ContinuousMap.coe_mk, Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_smul, zero_smul, zero_add, probReal_univ, one_smul] using
    (integral_fun_snd (μ := gaussianProductLaw (Fin d)) (ν := gaussianProductLaw (Fin m))
      (fun x => F.value (polynomialFamily g x)))

/-- Actual one-row expectation replacement for bounded C² tests. Covariance
matching is an explicit deterministic coefficient identity. No Gaussian comparison,
universality, smooth Stein, or integration interchange is assumed. -/
theorem one_row_smooth_replacement
    (F : SmoothTest κ) (H : κ → SmoothTest κ)
    (hH : ∀ a, (H a).value = F.gradient a)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hAsym : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2 / (d : ℝ) * Matrix.trace (A a*A b))
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀)
    (hAB : ∀ a b, 8/(d:ℝ)^2 * frobeniusSq (A a*A b) ≤ R₀^2) :
    |(∫ x, F.value (polynomialFamily (fun a => normalizedQuadratic d (A a)) x)
          ∂gaussianProductLaw (Fin d)) -
      ∫ z, F.value (polynomialFamily (fun a => linearPolynomial (B a)) z)
          ∂gaussianProductLaw (Fin m)| ≤
      (Real.pi/2) * R₀ * ∑ a, ∑ b, ‖(H a).gradient b‖ := by
  let q := fun b => normalizedQuadratic d (A b)
  let g := fun b => linearPolynomial (B b)
  let E := fun t => ∫ z, mixedValue F t q g z ∂law d m
  let E' := fun t => -Real.sin t*Real.cos t * ∑ a, ∑ b,
    ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b))*mixedHessian H t q g a b z ∂law d m
  let C := R₀ * ∑ a, ∑ b, ‖(H a).gradient b‖
  have hdE (t : ℝ) : HasDerivAt E (E' t) t :=
    hasDerivAt_expected_value_stein_remainder F H hH t A hAsym B hCov
  have hbound (t : ℝ) : ‖E' t‖ ≤ C := by
    have hsum := mixed_kernel_sum_abs_le H t A B R₀ hR₀ hAB
    have htrig : |(-Real.sin t)*Real.cos t| ≤ 1 := by
      rw [abs_mul, abs_neg]
      exact (mul_le_mul (Real.abs_sin_le_one t) (Real.abs_cos_le_one t)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
    change ‖(-Real.sin t*Real.cos t) * _‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul htrig hsum (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ)) (x := 0) (y := Real.pi/2)
    (fun t _ => (hdE t).hasDerivWithinAt) (fun t _ => hbound t)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  have hpi : 0 ≤ Real.pi/2 := by positivity
  change ‖E (Real.pi/2)-E 0‖ ≤ C * ‖Real.pi/2-0‖ at hm
  dsimp only [E] at hm
  rw [expected_mixedValue_pi_div_two, expected_mixedValue_zero,
    Real.norm_eq_abs, sub_zero, Real.norm_eq_abs, abs_of_nonneg hpi] at hm
  rw [abs_sub_comm]
  exact hm.trans_eq (by dsimp [C]; ring)

#print axioms mixed_kernel_pair_abs_le
#print axioms one_row_smooth_replacement
end GaussianEllipsoid.UCFrobeniusReplacement
