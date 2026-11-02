import BMGaussianSmoothStein
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace BMSmoothQuadraticComposition
variable {d : ℕ}

/-- Analytic coordinate derivative agrees with the formal polynomial derivative. -/
theorem hasDerivAt_eval_update (P : MvPolynomial (Fin d) ℝ)
    (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t => eval (Function.update x i t) P) (eval x (pderiv i P)) (x i) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (x i) c
  | add P Q hP hQ => simpa using! hP.add hQ
  | mul_X P j hP =>
    have hX := BMGaussianSmoothStein.hasDerivAt_update_coordinate x i j
    have h := hP.mul hX
    simpa only [eval_mul, eval_X, Function.update_eq_self, pderiv_mul,
      pderiv_X, Pi.single_apply, apply_ite (eval x), map_one, map_zero,
      map_add, eq_comm] using! h

/-- A bounded measurable factor times any Gaussian polynomial is integrable. -/
theorem integrable_polynomial_mul_bounded
    (P : MvPolynomial (Fin d) ℝ) (f : (Fin d → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f (gaussianProductLaw (Fin d)))
    (hbound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable (fun x => eval x P * f x) (gaussianProductLaw (Fin d)) := by
  obtain ⟨C, hC⟩ := hbound
  simpa only [mul_comm] using (gaussianProductLaw_integrable_polynomial P).bdd_mul hf
    (Filter.Eventually.of_forall hC)

/-- Gaussian expectations of polynomial-times-bounded factors, as a linear
functional in the polynomial coefficient. -/
def weightedExpectation (f : (Fin d → ℝ) → ℝ)
    (hf : AEStronglyMeasurable f (gaussianProductLaw (Fin d)))
    (hbound : ∃ C, ∀ x, ‖f x‖ ≤ C) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ x, eval x P * f x ∂gaussianProductLaw (Fin d)
  map_add' P Q := by
    simp only [eval_add, add_mul]
    exact integral_add (integrable_polynomial_mul_bounded P f hf hbound)
      (integrable_polynomial_mul_bounded Q f hf hbound)
  map_smul' c P := by
    simp only [MvPolynomial.smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _

/-- Continuity of actual multivariate polynomial evaluation. -/
theorem polynomial_continuous_eval (P : MvPolynomial (Fin d) ℝ) :
    Continuous (fun x : Fin d → ℝ => eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using continuous_const (y := c)
  | add P Q hP hQ => simpa using! hP.add hQ
  | mul_X P j hP => simpa using! hP.mul (continuous_apply j)

/-- A bounded test function and its bounded continuous coordinate derivatives. -/
structure SmoothTest (κ : Type*) [Fintype κ] where
  value : (κ → ℝ) →ᵇ ℝ
  gradient : κ → ((κ → ℝ) →ᵇ ℝ)
  hasFDeriv : ∀ y, HasFDerivAt (𝕜 := ℝ) (fun y => value y)
    (∑ b, (gradient b y) • (ContinuousLinearMap.proj b : (κ → ℝ) →L[ℝ] ℝ)) y

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Simultaneous polynomial observables form a genuine continuous map. -/
def polynomialFamily (q : κ → MvPolynomial (Fin d) ℝ) :
    C((Fin d → ℝ), (κ → ℝ)) where
  toFun x b := eval x (q b)
  continuous_toFun := continuous_pi fun b => polynomial_continuous_eval (q b)

/-- Bounded smooth tests remain bounded after arbitrary polynomial substitution. -/
def composedTest (F : SmoothTest κ) (q : κ → MvPolynomial (Fin d) ℝ) :
    (Fin d → ℝ) →ᵇ ℝ := F.value.compContinuous (polynomialFamily q)

def composedGradient (F : SmoothTest κ) (q : κ → MvPolynomial (Fin d) ℝ) (b : κ) :
    (Fin d → ℝ) →ᵇ ℝ := (F.gradient b).compContinuous (polynomialFamily q)

/-- Gaussian integration weighted by an actual bounded continuous function. -/
def boundedExpectation (f : (Fin d → ℝ) →ᵇ ℝ) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ :=
  weightedExpectation f f.continuous.aestronglyMeasurable ⟨‖f‖, f.norm_coe_le_norm⟩

theorem integrable_poly_bounded (f : (Fin d → ℝ) →ᵇ ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    Integrable (fun x => eval x P * f x) (gaussianProductLaw (Fin d)) :=
  integrable_polynomial_mul_bounded P f f.continuous.aestronglyMeasurable
    ⟨‖f‖, f.norm_coe_le_norm⟩

/-- Analytic chain rule with all test coordinates retained. -/
theorem hasDerivAt_composedTest (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (x : Fin d → ℝ) (i : Fin d) :
    HasDerivAt (fun t => composedTest F q (Function.update x i t))
      (∑ b, eval x (pderiv i (q b)) * composedGradient F q b x) (x i) := by
  have hq : HasDerivAt (fun t => polynomialFamily q (Function.update x i t))
      (fun b => eval x (pderiv i (q b))) (x i) :=
    hasDerivAt_pi.mpr fun b => hasDerivAt_eval_update (q b) x i
  have hh := (F.hasFDeriv (polynomialFamily q x)).comp_hasDerivAt_of_eq (x i)
    hq (by simp only [Function.update_eq_self])
  simpa only [Function.comp_def, composedTest, composedGradient,
    BoundedContinuousFunction.compContinuous_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mul_comm] using hh

/-- Exact nonpolynomial quadratic Stein contraction, coefficientwise. -/
theorem boundedExpectation_centered_pair (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (i j : Fin d) :
    boundedExpectation (composedTest F q) (X i*X j - if i = j then 1 else 0) =
      ∑ b, boundedExpectation (composedGradient F q b) (X j*pderiv i (q b)) := by
  have hf := integrable_poly_bounded (composedTest F q) (1 : MvPolynomial (Fin d) ℝ)
  have hjf := integrable_poly_bounded (composedTest F q) (X j)
  have hijf := integrable_poly_bounded (composedTest F q) (X i*X j)
  have hgrad (b : κ) := integrable_poly_bounded (composedGradient F q b) (X j*pderiv i (q b))
  have hsum : Integrable (fun x => x j * ∑ b,
      eval x (pderiv i (q b))*composedGradient F q b x) (gaussianProductLaw (Fin d)) := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    exact integrable_finset_sum _ (fun b _ => by simpa using hgrad b)
  have h := BMGaussianSmoothStein.gaussianProductLaw_centered_pair_smooth_stein
    (composedTest F q)
    (fun x => ∑ b, eval x (pderiv i (q b))*composedGradient F q b x) i j
    (fun x => hasDerivAt_composedTest F q x i)
    (by simpa using hf) (by simpa using hjf) (by simpa [mul_assoc] using hijf) hsum
  simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
    eval_sub, eval_mul, eval_X, apply_ite (eval _), map_one, map_zero,
    Finset.mul_sum, ← mul_assoc,
    integral_finset_sum _ (fun b _ => by simpa using hgrad b)] using h

/-- Exact quadratic-form Stein contraction for a bounded C¹ test of any
finite family of polynomial observables. All integrability is discharged. -/
theorem boundedExpectation_centeredQuadratic (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    boundedExpectation (composedTest F q) (centeredQuadratic A) =
      ∑ b, boundedExpectation (composedGradient F q b)
        (∑ i, ∑ j, A i j • (X j*pderiv i (q b))) := by
  simp only [centeredQuadratic, map_sum, map_smul, smul_eq_mul,
    boundedExpectation_centered_pair, Finset.mul_sum]
  exact sum_three_rotate (fun i j b => A i j *
    boundedExpectation (composedGradient F q b) (X j*pderiv i (q b)))

/-- The smooth finite-dimensional identity in covariance-plus-remainder form. -/
theorem boundedExpectation_vector_stein (F : SmoothTest κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (a : κ) :
    boundedExpectation (composedTest F (fun b => centeredQuadratic (A b)))
        (centeredQuadratic (A a)) =
      ∑ b, (Matrix.trace (kernelMatrix (A a) (A b)) *
          boundedExpectation (composedGradient F (fun b => centeredQuadratic (A b)) b) 1 +
        boundedExpectation (composedGradient F (fun b => centeredQuadratic (A b)) b)
          (centeredQuadratic (kernelMatrix (A a) (A b)))) := by
  rw [boundedExpectation_centeredQuadratic]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← rawQuadratic_kernelMatrix, rawQuadratic_eq_centered_add_trace, map_add]
  have hc : C (Matrix.trace (kernelMatrix (A a) (A b))) =
      Matrix.trace (kernelMatrix (A a) (A b)) • (1 : MvPolynomial (Fin d) ℝ) := by
    simp [MvPolynomial.smul_eq_C_mul]
  rw [hc, map_smul, smul_eq_mul]
  ring

/-- The normalized Gaussian quadratic vector admits the exact smooth Stein
identity, with covariance 2 tr(AB)/d and the literal centered quadratic remainder. -/
theorem boundedExpectation_normalized_vector_stein (F : SmoothTest κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hA : ∀ a, (A a).transpose = A a) (a : κ) :
    boundedExpectation (composedTest F (fun b => normalizedQuadratic d (A b)))
        (normalizedQuadratic d (A a)) =
      ∑ b, ((2 / (d : ℝ) * Matrix.trace (A a*A b)) *
          boundedExpectation (composedGradient F (fun b => normalizedQuadratic d (A b)) b) 1 +
        boundedExpectation (composedGradient F (fun b => normalizedQuadratic d (A b)) b)
          (normalizedKernelFluctuation d (A a) (A b))) := by
  have hs : 2 * ((Real.sqrt (d : ℝ))⁻¹)^2 = 2 / (d : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    rfl
  have h := boundedExpectation_vector_stein F
    (fun b => (Real.sqrt (d : ℝ))⁻¹ • A b) a
  simpa only [kernelMatrix_symmetric_smul _ _ _ (hA _) (hA _), hs,
    Matrix.trace_smul, centeredQuadratic_smul, smul_eq_mul,
    normalizedQuadratic, normalizedKernelFluctuation] using h

#print axioms boundedExpectation_centeredQuadratic
#print axioms boundedExpectation_normalized_vector_stein
end BMSmoothQuadraticComposition
