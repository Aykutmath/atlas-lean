import PaperMatrixSecondStein
import PaperNormalizedRowPolynomial
noncomputable section
open BMQuadraticStein BMSmoothQuadraticComposition PaperCavityThird PaperMatrixSecondStein
open scoped BigOperators BoundedContinuousFunction
namespace PaperNormalizedSecondStein
variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowMatrix (R : Matrix (Fin d) (Fin d) ℝ) := (1 / Real.sqrt 2) • R

theorem row_kernel (A B : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) :
    kernelMatrix (rowMatrix A) (rowMatrix B) = A * B := by
  rw [rowMatrix, rowMatrix, kernelMatrix_symmetric_smul _ _ _ hA hB]
  have h : 2 * (1 / Real.sqrt 2)^2 = (1 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h, one_smul]

theorem row_kernel_second (A B C : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (hC : C.transpose = C) :
    kernelMatrix (kernelMatrix (rowMatrix A) (rowMatrix B)) (rowMatrix C) =
      Real.sqrt 2 • (B * A * C) := by
  rw [kernelMatrix_kernelMatrix_symmetric _ _ _
    (by simp [rowMatrix, Matrix.transpose_smul, hA])
    (by simp [rowMatrix, Matrix.transpose_smul, hB])
    (by simp [rowMatrix, Matrix.transpose_smul, hC])]
  simp only [rowMatrix, smul_mul_assoc, mul_smul_comm, smul_smul]
  have h : 4 * ((1 / Real.sqrt 2) * ((1 / Real.sqrt 2) * (1 / Real.sqrt 2))) = Real.sqrt 2 := by
    have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp
    nlinarith [sq_nonneg (Real.sqrt 2)]
  convert congrArg (fun c : ℝ => c • (B * A * C)) h using 1
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- Exact paper-normalized second-chaos identity: covariance trace and √2
ordered triple coefficient, under the literal iid standard Gaussian law. -/
theorem normalized_vector_stein_second (F : SmoothTest2 κ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) (hR : ∀ a, (R a).transpose = R a) (a : κ) :
    boundedExpectation (composedTest F.first (fun b => centeredQuadratic (rowMatrix (R b))))
      (centeredQuadratic (rowMatrix (R a))) =
      ∑ b, (Matrix.trace (R a * R b) *
        boundedExpectation (composedGradient F.first (fun c => centeredQuadratic (rowMatrix (R c))) b) 1 +
        Real.sqrt 2 * ∑ c, boundedExpectation
          (composedGradient (F.gradientTest b) (fun e => centeredQuadratic (rowMatrix (R e))) c)
          (rawQuadratic (R b * R a * R c))) := by
  have h := vector_stein_second F (fun b => rowMatrix (R b)) a
  simp_rw [row_kernel _ _ (hR _) (hR _)] at h
  -- The outer kernel is rewritten separately, retaining its ordered product.
  have hk (b c : κ) : kernelMatrix (R a * R b) (rowMatrix (R c)) =
      Real.sqrt 2 • (R b * R a * R c) := by
    rw [← row_kernel _ _ (hR a) (hR b)]
    exact row_kernel_second _ _ _ (hR a) (hR b) (hR c)
  simp_rw [hk] at h
  simpa only [rawQuadratic, Matrix.smul_apply, smul_eq_mul, mul_smul,
    ← Finset.smul_sum, map_smul, ← Finset.mul_sum] using h

#print axioms normalized_vector_stein_second
end PaperNormalizedSecondStein
