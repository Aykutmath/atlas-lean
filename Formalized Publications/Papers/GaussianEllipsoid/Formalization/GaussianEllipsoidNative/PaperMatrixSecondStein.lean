import PaperCavityThird

/-! Reconstructed source, not an original-source recovery. The exported identity
is fixed by the preserved PaperNormalizedSecondStein and
PaperUnboundedPotentialStein consumers. -/
noncomputable section
open BMQuadraticStein BMSmoothQuadraticComposition PaperCavityThird
open scoped BigOperators BoundedContinuousFunction
namespace PaperMatrixSecondStein
variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem vector_stein_second (F : SmoothTest2 κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (a : κ) :
    boundedExpectation (composedTest F.first (fun b => centeredQuadratic (A b)))
      (centeredQuadratic (A a)) =
      ∑ b, (Matrix.trace (kernelMatrix (A a) (A b)) *
        boundedExpectation (composedGradient F.first (fun c => centeredQuadratic (A c)) b) 1 +
        ∑ c, boundedExpectation
          (composedGradient (F.gradientTest b) (fun e => centeredQuadratic (A e)) c)
          (rawQuadratic (kernelMatrix (kernelMatrix (A a) (A b)) (A c)))) := by
  rw [boundedExpectation_vector_stein]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  have he : composedTest (F.gradientTest b) (fun c => centeredQuadratic (A c)) =
      composedGradient F.first (fun c => centeredQuadratic (A c)) b := by
    unfold composedTest composedGradient
    rw [F.gradient_value b]
  rw [← he, boundedExpectation_centeredQuadratic]
  simp_rw [← rawQuadratic_kernelMatrix]

#print axioms vector_stein_second
end PaperMatrixSecondStein
