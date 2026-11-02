import BMNormalizedStein

/-! Reconstructed source. The ordered product B*A*C is fixed by the
preserved normalized second-Stein consumer; no commuting assumption is used. -/
noncomputable section
open scoped BigOperators
namespace BMQuadraticStein
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kernelMatrix_kernelMatrix_symmetric (A B C : Matrix ι ι ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) (hC : C.transpose = C) :
    kernelMatrix (kernelMatrix A B) C = (4 : ℕ) • (B * A * C) := by
  simp only [kernelMatrix, Matrix.transpose_mul, Matrix.transpose_add,
    Matrix.transpose_transpose, hA, hB, hC, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc]
  module

#print axioms kernelMatrix_kernelMatrix_symmetric
end BMQuadraticStein
