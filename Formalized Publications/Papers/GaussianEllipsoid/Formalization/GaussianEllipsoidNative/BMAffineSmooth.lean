import BMSmoothQuadraticComposition

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace BMAffineSmooth
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def affineMap (c : ℝ) (v : κ → ℝ) : C((κ → ℝ), (κ → ℝ)) where
  toFun y := c • y + v
  continuous_toFun := (continuous_id.const_smul c).add continuous_const

/-- Scaling and translating a bounded C¹ test preserves the exact test class. -/
def affineTest (F : SmoothTest κ) (c : ℝ) (v : κ → ℝ) : SmoothTest κ where
  value := F.value.compContinuous (affineMap c v)
  gradient b := c • (F.gradient b).compContinuous (affineMap c v)
  hasFDeriv y := by
    have hi := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul c).add_const v
    have h := (F.hasFDeriv (c • y + v)).comp y hi
    convert! h using 1
    ext z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.id_apply, BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.compContinuous_apply, affineMap, ContinuousMap.coe_mk,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro b hb
    ring

variable {d : ℕ}

/-- Nonpolynomial coordinate Stein identity after polynomial substitution. -/
theorem boundedExpectation_coordinate (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (i : Fin d) :
    boundedExpectation (composedTest F q) (X i) =
      ∑ b, boundedExpectation (composedGradient F q b) (pderiv i (q b)) := by
  have hf := integrable_poly_bounded (composedTest F q) (1 : MvPolynomial (Fin d) ℝ)
  have hxf := integrable_poly_bounded (composedTest F q) (X i)
  have hg (b : κ) := integrable_poly_bounded (composedGradient F q b) (pderiv i (q b))
  have hi := integrable_finset_sum Finset.univ (fun b _ => hg b)
  have h := BMGaussianSmoothStein.gaussianProductLaw_smooth_stein
    (composedTest F q) (fun x => ∑ b, eval x (pderiv i (q b))*composedGradient F q b x) i
    (fun x => hasDerivAt_composedTest F q x i) (by simpa using hf)
    (by simpa using hxf) hi
  simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
    eval_X, integral_finset_sum _ (fun b _ => hg b)] using h

/-- Gaussian linear projections with arbitrary deterministic coefficients. -/
def linearPolynomial (v : Fin d → ℝ) : MvPolynomial (Fin d) ℝ := ∑ i, v i • X i

theorem pderiv_linearPolynomial (v : Fin d → ℝ) (i : Fin d) :
    pderiv i (linearPolynomial v) = C (v i) := by
  simp only [linearPolynomial, map_sum, Derivation.map_smul, pderiv_X,
    Pi.single_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp [MvPolynomial.smul_eq_C_mul]

/-- Exact Gaussian vector Stein identity, with the covariance computed from the
actual linear-form coefficients, not supplied as a probabilistic premise. -/
theorem boundedExpectation_linear_vector_stein (F : SmoothTest κ)
    (B : κ → Fin d → ℝ) (a : κ) :
    boundedExpectation (composedTest F (fun b => linearPolynomial (B b)))
        (linearPolynomial (B a)) =
      ∑ b, (∑ i, B a i*B b i) *
        boundedExpectation (composedGradient F (fun b => linearPolynomial (B b)) b) 1 := by
  simp only [linearPolynomial, map_sum, map_smul, smul_eq_mul]
  simp_rw [boundedExpectation_coordinate]
  change (∑ i, B a i * ∑ b,
      boundedExpectation (composedGradient F (fun b => linearPolynomial (B b)) b)
        (pderiv i (linearPolynomial (B b)))) = _
  simp_rw [pderiv_linearPolynomial]
  have hc (r : ℝ) : (C r : MvPolynomial (Fin d) ℝ) = r • 1 := by
    simp [MvPolynomial.smul_eq_C_mul]
  simp_rw [hc, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [linearPolynomial]
  ring

/-- Affine transformations of polynomial observable families. -/
def affinePolynomials (c : ℝ) (v : κ → ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (b : κ) : MvPolynomial (Fin d) ℝ :=
  c • q b + C (v b)

@[simp] theorem eval_affinePolynomials (c : ℝ) (v : κ → ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) (b : κ) :
    eval x (affinePolynomials c v q b) = c * eval x (q b) + v b := by
  simp [affinePolynomials, MvPolynomial.smul_eq_C_mul]

theorem composedTest_affineTest (F : SmoothTest κ) (c : ℝ) (v : κ → ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) :
    composedTest (affineTest F c v) q = composedTest F (affinePolynomials c v q) := by
  ext x
  change F.value (c • polynomialFamily q x + v) = F.value (polynomialFamily (affinePolynomials c v q) x)
  congr 1
  ext b
  simp [polynomialFamily]

theorem composedGradient_affineTest (F : SmoothTest κ) (c : ℝ) (v : κ → ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (b : κ) :
    composedGradient (affineTest F c v) q b = c • composedGradient F (affinePolynomials c v q) b := by
  ext x
  change c * F.gradient b (c • polynomialFamily q x + v) =
    c * F.gradient b (polynomialFamily (affinePolynomials c v q) x)
  congr 2
  ext j
  simp [polynomialFamily]

theorem boundedExpectation_smul (f : (Fin d → ℝ) →ᵇ ℝ) (c : ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    boundedExpectation (c • f) P = c * boundedExpectation f P := by
  change (∫ x, eval x P * (c * f x) ∂gaussianProductLaw (Fin d)) =
    c * ∫ x, eval x P*f x ∂gaussianProductLaw (Fin d)
  simp_rw [show ∀ x, eval x P*(c*f x) = c*(eval x P*f x) by intro x; ring]
  exact integral_const_mul _ _

/-- Actual-law quadratic Stein identity with arbitrary affine shifts, as needed
when conditioning on the independent Gaussian row in a replacement interpolation. -/
theorem quadratic_affine_stein (F : SmoothTest κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a)
    (a : κ) (c : ℝ) (v : κ → ℝ) :
    boundedExpectation (composedTest F (affinePolynomials c v (fun b => normalizedQuadratic d (A b))))
        (normalizedQuadratic d (A a)) =
      c * ∑ b, ((2 / (d : ℝ) * Matrix.trace (A a*A b)) *
          boundedExpectation (composedGradient F
            (affinePolynomials c v (fun b => normalizedQuadratic d (A b))) b) 1 +
        boundedExpectation (composedGradient F
          (affinePolynomials c v (fun b => normalizedQuadratic d (A b))) b)
          (normalizedKernelFluctuation d (A a) (A b))) := by
  have h := boundedExpectation_normalized_vector_stein (affineTest F c v) A hA a
  simp_rw [composedTest_affineTest, composedGradient_affineTest, boundedExpectation_smul] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Actual-law linear Gaussian Stein identity with arbitrary affine shifts. -/
theorem linear_affine_stein (F : SmoothTest κ) (B : κ → Fin d → ℝ)
    (a : κ) (c : ℝ) (v : κ → ℝ) :
    boundedExpectation (composedTest F (affinePolynomials c v (fun b => linearPolynomial (B b))))
        (linearPolynomial (B a)) =
      c * ∑ b, (∑ i, B a i*B b i) *
        boundedExpectation (composedGradient F
          (affinePolynomials c v (fun b => linearPolynomial (B b))) b) 1 := by
  have h := boundedExpectation_linear_vector_stein (affineTest F c v) B a
  simp_rw [composedTest_affineTest, composedGradient_affineTest, boundedExpectation_smul] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

#print axioms affineTest
#print axioms boundedExpectation_linear_vector_stein
end BMAffineSmooth
