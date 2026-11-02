import BMSmoothQuadraticComposition
import GaussianEllipsoid.Gibbs

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMGaussianSmoothStein MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace PaperCavityThird

/-- Two genuine Gaussian integrations by parts, for a general twice differentiable
coordinate test. These are integrability conditions, not Stein hypotheses. -/
theorem centered_pair_second {d : ℕ}
    (f fi fij : (Fin d → ℝ) → ℝ) (i j : Fin d)
    (hi : ∀ x, HasDerivAt (fun t => f (Function.update x i t)) (fi x) (x i))
    (hij : ∀ x, HasDerivAt (fun t => fi (Function.update x j t)) (fij x) (x j))
    (hf : Integrable f (gaussianProductLaw (Fin d)))
    (hjf : Integrable (fun x => x j * f x) (gaussianProductLaw (Fin d)))
    (hijf : Integrable (fun x => x i * (x j * f x)) (gaussianProductLaw (Fin d)))
    (hfi : Integrable fi (gaussianProductLaw (Fin d)))
    (hjfi : Integrable (fun x => x j * fi x) (gaussianProductLaw (Fin d)))
    (hfij : Integrable fij (gaussianProductLaw (Fin d))) :
    (∫ x, (x i * x j - if i = j then 1 else 0) * f x ∂gaussianProductLaw (Fin d)) =
      ∫ x, fij x ∂gaussianProductLaw (Fin d) := by
  rw [gaussianProductLaw_centered_pair_smooth_stein f fi i j hi hf hjf hijf hjfi]
  exact gaussianProductLaw_smooth_stein fi fij j hij hfi hjfi hfij

variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The first Stein formula for a polynomial multiplier of a smooth bounded
composition. All Gaussian integrability is proved from polynomial moments. -/
theorem weighted_composition_stein (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (P : MvPolynomial (Fin d) ℝ) (j : Fin d) :
    boundedExpectation (composedTest F q) (X j * P) =
      boundedExpectation (composedTest F q) (pderiv j P) +
      ∑ b, boundedExpectation (composedGradient F q b) (P * pderiv j (q b)) := by
  have hd (x : Fin d → ℝ) := (hasDerivAt_eval_update P x j).mul
    (hasDerivAt_composedTest F q x j)
  have hsum : Integrable (fun x => ∑ b, eval x (P * pderiv j (q b)) *
      composedGradient F q b x) (gaussianProductLaw (Fin d)) :=
    integrable_finset_sum _ (fun b _ => integrable_poly_bounded _ _)
  have hh := gaussianProductLaw_smooth_stein
    (fun x => eval x P * composedTest F q x)
    (fun x => eval x (pderiv j P) * composedTest F q x +
      ∑ b, eval x (P * pderiv j (q b)) * composedGradient F q b x) j
    (fun x => by
      simpa [Function.update_eq_self, Finset.mul_sum, mul_assoc] using! hd x)
    (integrable_poly_bounded _ _)
    (by
      convert integrable_poly_bounded (composedTest F q) (X j * P) using 1
      funext x
      simp only [map_mul, eval_X, mul_assoc])
    ((integrable_poly_bounded _ _).add hsum)
  rw [integral_add (integrable_poly_bounded _ _) hsum,
    integral_finset_sum _ (fun b _ => integrable_poly_bounded _ _)] at hh
  simpa [boundedExpectation, weightedExpectation, mul_assoc] using hh

/-- Bounded C² tests, represented by actual differentiable gradient tests. -/
structure SmoothTest2 (κ : Type*) [Fintype κ] where
  first : SmoothTest κ
  gradientTest : κ → SmoothTest κ
  gradient_value : ∀ b, (gradientTest b).value = first.gradient b

/-- Exact nonpolynomial second-order centered-pair identity after polynomial
substitution. In the paper the test is a first derivative of the cavity free
energy, so its second derivative is precisely the required third derivative. -/
theorem centered_pair_composition_second (F : SmoothTest2 κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (i j : Fin d) :
    boundedExpectation (composedTest F.first q) (X i * X j - if i = j then 1 else 0) =
      ∑ b, (boundedExpectation (composedGradient F.first q b) (pderiv j (pderiv i (q b))) +
        ∑ c, boundedExpectation (composedGradient (F.gradientTest b) q c)
          (pderiv i (q b) * pderiv j (q c))) := by
  rw [boundedExpectation_centered_pair]
  apply Finset.sum_congr rfl
  intro b _
  have he : composedTest (F.gradientTest b) q = composedGradient F.first q b := by
    unfold composedTest composedGradient
    rw [F.gradient_value b]
  simpa only [he] using weighted_composition_stein (F.gradientTest b) q (pderiv i (q b)) j

/-- Exact second-chaos identity for a general centered quadratic row. This
is the coefficientwise matrix identity before identifying the Frobenius
Laplacian and the ordered pure-tensor contraction. -/
theorem centered_quadratic_composition_second (F : SmoothTest2 κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    boundedExpectation (composedTest F.first q) (centeredQuadratic A) =
      ∑ i, ∑ j, A i j * ∑ b,
        (boundedExpectation (composedGradient F.first q b) (pderiv j (pderiv i (q b))) +
          ∑ c, boundedExpectation (composedGradient (F.gradientTest b) q c)
            (pderiv i (q b) * pderiv j (q c))) := by
  simp only [centeredQuadratic, map_sum, map_smul, smul_eq_mul,
    centered_pair_composition_second]

#print axioms centered_pair_second
#print axioms weighted_composition_stein
#print axioms centered_pair_composition_second
end PaperCavityThird
