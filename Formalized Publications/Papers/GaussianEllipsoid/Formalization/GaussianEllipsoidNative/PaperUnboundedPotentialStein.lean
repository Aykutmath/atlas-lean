import PaperMatrixSecondStein
noncomputable section
open MeasureTheory GaussianTensorMoments BMQuadraticStein BMSmoothQuadraticComposition
open PaperCavityThird PaperMatrixSecondStein
open scoped BigOperators BoundedContinuousFunction
namespace PaperUnboundedPotentialStein
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}

/-- A generic potential need not be bounded. Only its genuine first derivative
slices and their first two derivatives are packaged as bounded tests. -/
theorem derivative_slice_second_stein (Φ : (κ → ℝ) → ℝ)
    (H : κ → SmoothTest2 κ)
    (hΦ : ∀ y, HasFDerivAt Φ
      (∑ a, ((H a).first.value y) • (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (a : κ) :
    (∫ w, MvPolynomial.eval w (centeredQuadratic (A a)) *
      (fderiv ℝ Φ (polynomialFamily (fun b => centeredQuadratic (A b)) w)) (Pi.single a 1)
        ∂gaussianProductLaw (Fin d)) =
      ∑ b, (Matrix.trace (kernelMatrix (A a) (A b)) *
        boundedExpectation (composedGradient (H a).first (fun c => centeredQuadratic (A c)) b) 1 +
        ∑ c, boundedExpectation
          (composedGradient ((H a).gradientTest b) (fun e => centeredQuadratic (A e)) c)
          (rawQuadratic (kernelMatrix (kernelMatrix (A a) (A b)) (A c)))) := by
  have he (y : κ → ℝ) : (fderiv ℝ Φ y) (Pi.single a 1) = (H a).first.value y := by
    rw [(hΦ y).fderiv]
    simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, Pi.single_apply]
  simp_rw [he]
  exact vector_stein_second (H a) A a

#print axioms derivative_slice_second_stein
end PaperUnboundedPotentialStein
