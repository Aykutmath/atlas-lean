import BMRowInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMRowInterpolation MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace BMRowSteinCancellation
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {d m : ℕ}

/-- Condition on the independent Gaussian comparison row and apply the actual
quadratic Stein identity. -/
theorem quadratic_product_stein (F : SmoothTest κ) (t : ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ) (a : κ) :
    (∫ z, eval z.1 (normalizedQuadratic d (A a)) * mixedValue F t
      (fun b => normalizedQuadratic d (A b)) (fun b => linearPolynomial (B b)) z ∂law d m) =
    Real.cos t * ∑ b, ((2 / (d : ℝ) * Matrix.trace (A a*A b)) *
      (∫ z, mixedGradient F t (fun b => normalizedQuadratic d (A b))
        (fun b => linearPolynomial (B b)) b z ∂law d m) +
      ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
        mixedGradient F t (fun b => normalizedQuadratic d (A b))
          (fun b => linearPolynomial (B b)) b z ∂law d m) := by
  let q := fun b => normalizedQuadratic d (A b)
  let g := fun b => linearPolynomial (B b)
  let C := fun b => 2 / (d : ℝ) * Matrix.trace (A a*A b)
  let R := fun b => normalizedKernelFluctuation d (A a) (A b)
  have hi := integrable_fst_poly_mul (q a) (mixedValue F t q g)
  have hh (b : κ) := integrable_bounded (mixedGradient F t q g b)
  have hr (b : κ) := integrable_fst_poly_mul (R b) (mixedGradient F t q g b)
  have hp (y : Fin m → ℝ) :
      (∫ x, eval x (q a) * mixedValue F t q g (x,y) ∂gaussianProductLaw (Fin d)) =
      Real.cos t * ∑ b, (C b *
        (∫ x, mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin d)) +
        ∫ x, eval x (R b)*mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin d)) := by
    have h := quadratic_affine_stein F A hA a (Real.cos t)
      (Real.sin t • polynomialFamily g y)
    simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
      composedTest, composedGradient, BoundedContinuousFunction.compContinuous_apply,
      mixedValue, mixedGradient, mixMap, polynomialFamily, ContinuousMap.coe_mk,
      eval_affinePolynomials, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, one_mul,
      q, g, C, R] using! h
  change (∫ z, eval z.1 (q a)*mixedValue F t q g z ∂law d m) =
    Real.cos t * ∑ b, (C b * (∫ z, mixedGradient F t q g b z ∂law d m) +
      ∫ z, eval z.1 (R b)*mixedGradient F t q g b z ∂law d m)
  simp only [law]
  rw [integral_prod_symm _ hi]
  simp_rw [hp]
  rw [integral_const_mul]
  have ho (b : κ) : Integrable (fun y : Fin m → ℝ =>
      C b * (∫ x, mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin d)) +
      ∫ x, eval x (R b)*mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin d))
        (gaussianProductLaw (Fin m)) :=
    ((hh b).integral_prod_right.const_mul (C b)).add (hr b).integral_prod_right
  rw [integral_finset_sum Finset.univ (fun b _ => ho b)]
  apply congrArg (fun x : ℝ => Real.cos t*x)
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_add ((hh b).integral_prod_right.const_mul (C b)) (hr b).integral_prod_right,
    integral_const_mul, ← integral_prod_symm _ (hh b), ← integral_prod_symm _ (hr b)]

/-- The independent linear Gaussian comparison row gives the exact matching
covariance term, with no quadratic remainder. -/
theorem linear_product_stein (F : SmoothTest κ) (t : ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (B : κ → Fin m → ℝ) (a : κ) :
    (∫ z, eval z.2 (linearPolynomial (B a)) * mixedValue F t
      (fun b => normalizedQuadratic d (A b)) (fun b => linearPolynomial (B b)) z ∂law d m) =
    Real.sin t * ∑ b, (∑ i, B a i*B b i) *
      (∫ z, mixedGradient F t (fun b => normalizedQuadratic d (A b))
        (fun b => linearPolynomial (B b)) b z ∂law d m) := by
  let q := fun b => normalizedQuadratic d (A b)
  let g := fun b => linearPolynomial (B b)
  let C := fun b => ∑ i, B a i*B b i
  have hi := integrable_snd_poly_mul (g a) (mixedValue F t q g)
  have hh (b : κ) := integrable_bounded (mixedGradient F t q g b)
  have hp (x : Fin d → ℝ) :
      (∫ y, eval y (g a) * mixedValue F t q g (x,y) ∂gaussianProductLaw (Fin m)) =
      Real.sin t * ∑ b, C b *
        (∫ y, mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin m)) := by
    have h := linear_affine_stein F B a (Real.sin t) (Real.cos t • polynomialFamily q x)
    have hswap (y : Fin m → ℝ) :
        (fun b => Real.sin t*eval y (g b) + Real.cos t*eval x (q b)) =
        (fun b => Real.cos t*eval x (q b) + Real.sin t*eval y (g b)) := by funext b; ring
    simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
      composedTest, composedGradient, BoundedContinuousFunction.compContinuous_apply,
      mixedValue, mixedGradient, mixMap, polynomialFamily, ContinuousMap.coe_mk,
      eval_affinePolynomials, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, one_mul,
      hswap, q, g, C] using! h
  change (∫ z, eval z.2 (g a)*mixedValue F t q g z ∂law d m) =
    Real.sin t * ∑ b, C b * (∫ z, mixedGradient F t q g b z ∂law d m)
  simp only [law]
  rw [integral_prod _ hi]
  simp_rw [hp]
  rw [integral_const_mul]
  rw [integral_finset_sum _ (fun b _ => (hh b).integral_prod_left.const_mul (C b))]
  apply congrArg (fun x : ℝ => Real.sin t*x)
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_const_mul, ← integral_prod _ (hh b)]

/-- Exact cancellation of the matching Gaussian covariance in the expected
interpolation derivative. The only surviving term is the literal centered
quadratic Stein-kernel fluctuation against the Hessian. -/
theorem expected_velocity_eq_stein_remainder
    (F : SmoothTest κ) (H : κ → SmoothTest κ)
    (hH : ∀ a, (H a).value = F.gradient a) (t : ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2 / (d : ℝ) * Matrix.trace (A a*A b)) :
    (∫ z, velocity F t (fun b => normalizedQuadratic d (A b))
      (fun b => linearPolynomial (B b)) z ∂law d m) =
      -Real.sin t*Real.cos t * ∑ a, ∑ b,
        ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
          mixedHessian H t (fun b => normalizedQuadratic d (A b))
            (fun b => linearPolynomial (B b)) a b z ∂law d m := by
  let q := fun b => normalizedQuadratic d (A b)
  let g := fun b => linearPolynomial (B b)
  have hv (a : κ) : mixedGradient F t q g a = mixedValue (H a) t q g := by
    ext z
    change F.gradient a (mixMap t q g z) = (H a).value (mixMap t q g z)
    rw [hH]
  have hterm (a : κ) :
      (∫ z, mixedGradient F t q g a z *
          (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) ∂law d m) =
        -Real.sin t*Real.cos t * ∑ b,
          ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
            mixedHessian H t q g a b z ∂law d m := by
    rw [hv]
    have hiQ := integrable_fst_poly_mul (q a) (mixedValue (H a) t q g)
    have hiG := integrable_snd_poly_mul (g a) (mixedValue (H a) t q g)
    have he (z : SamplePair d m) : mixedValue (H a) t q g z *
        (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) =
        -Real.sin t * (eval z.1 (q a)*mixedValue (H a) t q g z) +
        Real.cos t * (eval z.2 (g a)*mixedValue (H a) t q g z) := by ring
    simp_rw [he]
    rw [integral_add (hiQ.const_mul (-Real.sin t)) (hiG.const_mul (Real.cos t)),
      integral_const_mul, integral_const_mul,
      quadratic_product_stein (H a) t A hA B a, linear_product_stein (H a) t A B a]
    simp_rw [hCov, Finset.sum_add_distrib]
    change _ = -Real.sin t*Real.cos t * ∑ b,
      ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
        mixedGradient (H a) t q g b z ∂law d m
    ring
  change (∫ z, ∑ a, mixedGradient F t q g a z *
      (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) ∂law d m) = _
  have hti (a : κ) : Integrable (fun z => mixedGradient F t q g a z *
      (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a))) (law d m) := by
    have hq := (integrable_fst_poly_mul (q a) (mixedGradient F t q g a)).const_mul (-Real.sin t)
    have hg := (integrable_snd_poly_mul (g a) (mixedGradient F t q g a)).const_mul (Real.cos t)
    convert! hq.add hg using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  rw [integral_finset_sum _ (fun a _ => hti a)]
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- The complete actual-law derivative formula for finite-prior row replacement. -/
theorem hasDerivAt_expected_value_stein_remainder
    (F : SmoothTest κ) (H : κ → SmoothTest κ)
    (hH : ∀ a, (H a).value = F.gradient a) (t : ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2 / (d : ℝ) * Matrix.trace (A a*A b)) :
    HasDerivAt (fun u => ∫ z, mixedValue F u
        (fun b => normalizedQuadratic d (A b)) (fun b => linearPolynomial (B b)) z ∂law d m)
      (-Real.sin t*Real.cos t * ∑ a, ∑ b,
        ∫ z, eval z.1 (normalizedKernelFluctuation d (A a) (A b)) *
          mixedHessian H t (fun b => normalizedQuadratic d (A b))
            (fun b => linearPolynomial (B b)) a b z ∂law d m) t := by
  rw [← expected_velocity_eq_stein_remainder F H hH t A hA B hCov]
  exact hasDerivAt_expected_mixedValue F t _ _

#print axioms hasDerivAt_expected_value_stein_remainder
#print axioms quadratic_product_stein
#print axioms linear_product_stein
end BMRowSteinCancellation
