import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open WithLp
namespace AHHAlgebraBridges

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def embedReal (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  toLp 2 (fun i => (x i : ℂ))
def realPart (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => (z i).re)
def imagPart (z : EuclideanSpace ℂ ι) : EuclideanSpace ℝ ι :=
  toLp 2 (fun i => (z i).im)

theorem embedReal_norm (x : EuclideanSpace ℝ ι) : ‖embedReal x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [PiLp.norm_sq_eq_of_L2, embedReal]

theorem complex_norm_sq_parts (z : EuclideanSpace ℂ ι) :
    ‖z‖ ^ 2 = ‖realPart z‖ ^ 2 + ‖imagPart z‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, realPart, imagPart, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem real_matrix_on_embed (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A.map Complex.ofReal) (embedReal x) =
      embedReal ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A x) := by
  ext i
  simp [embedReal, Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct,
    Matrix.ofLp_toEuclideanCLM, ← Complex.ofReal_mul, ← Complex.ofReal_sum]

theorem real_matrix_realPart (A : Matrix ι ι ℝ) (z : EuclideanSpace ℂ ι) :
    realPart ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A.map Complex.ofReal) z) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A (realPart z) := by
  ext i
  simp [realPart, Matrix.ofLp_toEuclideanCLM, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Complex.mul_re]

theorem real_matrix_imagPart (A : Matrix ι ι ℝ) (z : EuclideanSpace ℂ ι) :
    imagPart ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A.map Complex.ofReal) z) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A (imagPart z) := by
  ext i
  simp [imagPart, Matrix.ofLp_toEuclideanCLM, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Complex.mul_im]

/-- Complexification preserves the genuine Euclidean operator norm, including
zero-dimensional spaces. This does not invoke any entrywise matrix norm. -/
theorem real_complex_operator_norm (A : Matrix ι ι ℝ) :
    ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A.map Complex.ofReal)‖ = ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [complex_norm_sq_parts, real_matrix_realPart, real_matrix_imagPart, mul_pow,
      complex_norm_sq_parts z, mul_add]
    have hr := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A).le_opNorm (realPart z)
    have hi := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A).le_opNorm (imagPart z)
    exact add_le_add (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hr 2)
      (by simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hi 2)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A.map Complex.ofReal)).le_opNorm (embedReal x)
    simpa only [real_matrix_on_embed, embedReal_norm] using h

/-- The same exact bridge, stated with Mathlib's explicitly scoped L2 matrix norm. -/
theorem real_complex_l2_matrix_norm (A : Matrix ι ι ℝ) :
    ‖A.map Complex.ofReal‖ = ‖A‖ := by
  simpa only [← Matrix.l2_opNorm_toEuclideanCLM] using real_complex_operator_norm A

end AHHAlgebraBridges
