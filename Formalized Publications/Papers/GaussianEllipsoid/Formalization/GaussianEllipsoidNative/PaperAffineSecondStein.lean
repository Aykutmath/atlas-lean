import PaperNormalizedSecondStein
import BMAffineSmooth

/-! New reconstruction of the affine normalized second-chaos identity. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open BMQuadraticStein BMSmoothQuadraticComposition PaperCavityThird
open PaperNormalizedSecondStein BMAffineSmooth
open scoped BigOperators BoundedContinuousFunction
namespace PaperAffineSecondStein
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}

/-- Scaling a test also scales its actual derivative. -/
def scaleTest (r : ℝ) (F : SmoothTest κ) : SmoothTest κ where
  value := r • F.value
  gradient b := r • F.gradient b
  hasFDeriv y := by
    convert! (F.hasFDeriv y).const_smul r using 1
    ext z
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.proj_apply, BoundedContinuousFunction.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring

def affineTest2 (F : SmoothTest2 κ) (s : ℝ) (v : κ → ℝ) : SmoothTest2 κ where
  first := affineTest F.first s v
  gradientTest b := scaleTest s (affineTest (F.gradientTest b) s v)
  gradient_value b := by
    simp only [scaleTest, affineTest, F.gradient_value b]

theorem normalized_affine_second_stein (F : SmoothTest2 κ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ)
    (hR : ∀ a, (R a).transpose = R a) (a : κ) (s : ℝ) (v : κ → ℝ) :
    boundedExpectation
      (composedTest F.first (affinePolynomials s v (fun b => centeredQuadratic (rowMatrix (R b)))))
      (centeredQuadratic (rowMatrix (R a))) =
      ∑ b, (s * Matrix.trace (R a * R b) *
        boundedExpectation
          (composedGradient F.first (affinePolynomials s v (fun c => centeredQuadratic (rowMatrix (R c)))) b) 1 +
        s^2 * Real.sqrt 2 * ∑ c, boundedExpectation
          (composedGradient (F.gradientTest b)
            (affinePolynomials s v (fun e => centeredQuadratic (rowMatrix (R e)))) c)
          (rawQuadratic (R b * R a * R c))) := by
  have h := normalized_vector_stein_second (affineTest2 F s v) R hR a
  have hg (b c : κ) :
      composedGradient ((affineTest2 F s v).gradientTest b)
        (fun e => centeredQuadratic (rowMatrix (R e))) c =
      (s*s) • composedGradient (F.gradientTest b)
        (affinePolynomials s v (fun e => centeredQuadratic (rowMatrix (R e)))) c := by
    ext w
    simp only [affineTest2, scaleTest, composedGradient, affineTest,
      BoundedContinuousFunction.compContinuous_apply, BoundedContinuousFunction.smul_apply,
      affineMap, ContinuousMap.coe_mk, smul_eq_mul]
    have he : polynomialFamily
        (affinePolynomials s v (fun e => centeredQuadratic (rowMatrix (R e)))) w =
        s • polynomialFamily (fun e => centeredQuadratic (rowMatrix (R e))) w + v := by
      ext e
      simp [polynomialFamily]
    rw [he]
    ring
  simp_rw [hg] at h
  have hf : (affineTest2 F s v).first = affineTest F.first s v := rfl
  simp only [hf, composedTest_affineTest, composedGradient_affineTest,
    boundedExpectation_smul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.mul_sum]
  ring

#print axioms normalized_affine_second_stein
end PaperAffineSecondStein
