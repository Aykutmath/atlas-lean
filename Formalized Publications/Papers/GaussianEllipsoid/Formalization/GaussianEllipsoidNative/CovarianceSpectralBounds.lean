import CovarianceTraceExpansion
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Basic

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace GaussianTensorTrace

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Genuine Euclidean operator, with no use of the default entrywise Matrix norm. -/
def matrixCLM (A : Matrix α β ℝ) : EuclideanSpace ℝ β →L[ℝ] EuclideanSpace ℝ α :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

theorem matrix_l2_norm_eq (A : Matrix α β ℝ) : ‖A‖ = ‖matrixCLM A‖ := rfl

theorem diagonal_norm_le (d : α → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : ‖Matrix.diagonal d‖ ≤ C := by
  rw [matrix_l2_norm_eq]
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow]
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : (matrixCLM (Matrix.diagonal d) x) i = d i * x i := by
    simp [matrixCLM, Matrix.mulVec_diagonal]
  rw [hi', mul_pow]
  have hsq : d i ^ 2 ≤ C ^ 2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hd i)
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- Positive powers retain the same diagonalizing Unitary. -/
theorem hermitian_pow_diagonalization (A : Matrix α α ℝ) (hA : A.IsHermitian) (m : ℕ) :
    A^m = (hA.eigenvectorUnitary : Matrix α α ℝ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i)^m) *
      star (hA.eigenvectorUnitary : Matrix α α ℝ) := by
  let U : Matrix α α ℝ := hA.eigenvectorUnitary
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal hA.eigenvalues * star U := by
    simpa only [Unitary.conjStarAlgAut_apply, Function.comp_apply, RCLike.ofReal_real_eq_id, Function.id_comp, id_eq] using hA.spectral_theorem
  change A^m = U * Matrix.diagonal (fun i => hA.eigenvalues i ^ m) * star U
  induction m with
  | zero => simpa using hUU'.symm
  | succ m ih =>
    rw [pow_succ, ih]
    conv_lhs => arg 2; rw [hspec]
    calc
      U * Matrix.diagonal (fun i => hA.eigenvalues i ^ m) * star U *
          (U * Matrix.diagonal hA.eigenvalues * star U) =
        U * Matrix.diagonal (fun i => hA.eigenvalues i ^ m) * (star U * U) *
          Matrix.diagonal hA.eigenvalues * star U := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i => hA.eigenvalues i ^ (m+1)) * star U := by
        rw [hUU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
        simp only [pow_succ]

theorem trace_pow_eq_sum_eigenvalues (A : Matrix α α ℝ) (hA : A.IsHermitian) (m : ℕ) :
    Matrix.trace (A^m) = ∑ i, (hA.eigenvalues i)^m := by
  rw [hermitian_pow_diagonalization A hA m, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]

theorem hermitian_norm_eq_diagonal (A : Matrix α α ℝ) (hA : A.IsHermitian) :
    ‖A‖ = ‖Matrix.diagonal hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hA.eigenvectorUnitary.prop),
    CStarRing.norm_coe_unitary_mul]
  rfl


/-- Every Hermitian eigenvalue is bounded by the genuine Euclidean operator norm. -/
theorem abs_eigenvalue_le_norm (A : Matrix α α ℝ) (hA : A.IsHermitian) (i : α) :
    |hA.eigenvalues i| ≤ ‖A‖ := by
  have heig : matrixCLM A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i) • hA.eigenvectorBasis i := by
    ext j
    simpa [matrixCLM] using
      congrFun (hA.mulVec_eigenvectorBasis i) j
  have hb := (matrixCLM A).le_opNorm (hA.eigenvectorBasis i)
  rw [heig, norm_smul, hA.eigenvectorBasis.orthonormal.1 i, mul_one, mul_one] at hb
  exact hb

/-- PSD trace powers dominate the corresponding spectral norm powers. -/
theorem posSemidef_norm_pow_le_trace [Nonempty α]
    (A : Matrix α α ℝ) (hA : A.PosSemidef) (m : ℕ) :
    ‖matrixCLM A‖^m ≤ Matrix.trace (A^m) := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty) hA.1.eigenvalues
  have hbound : ∀ j, hA.1.eigenvalues j ≤ hA.1.eigenvalues i := by
    intro j
    rw [← hmax]
    exact Finset.le_sup' _ (Finset.mem_univ j)
  have hn : ‖A‖ ≤ hA.1.eigenvalues i := by
    rw [hermitian_norm_eq_diagonal A hA.1]
    apply diagonal_norm_le _ (hA.eigenvalues_nonneg i)
    intro j
    simpa only [abs_of_nonneg (hA.eigenvalues_nonneg j)] using hbound j
  rw [← matrix_l2_norm_eq, trace_pow_eq_sum_eigenvalues A hA.1]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn m).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (hA.eigenvalues_nonneg j) m) (Finset.mem_univ i))

/-- PSD trace powers are at most dimension times the spectral norm power. -/
theorem posSemidef_trace_pow_le (A : Matrix α α ℝ) (hA : A.PosSemidef) (m : ℕ) :
    Matrix.trace (A^m) ≤ (Fintype.card α : ℝ) * ‖matrixCLM A‖^m := by
  rw [trace_pow_eq_sum_eigenvalues A hA.1]
  calc
    ∑ i, hA.1.eigenvalues i ^ m ≤ ∑ _i : α, ‖A‖^m := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (hA.eigenvalues_nonneg i)
        ((le_abs_self _).trans (abs_eigenvalue_le_norm A hA.1 i)) m
    _ = _ := by simp [matrix_l2_norm_eq]

/-- Rectangular Gaussian comparison uses h columns and a q by h entry matrix. -/
theorem gram_trace_pow_le (G : Matrix β α ℝ) (m : ℕ) :
    Matrix.trace ((Gᵀ * G)^m) ≤ (Fintype.card α : ℝ) * ‖matrixCLM G‖^(2*m) := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  have hp : (Gᵀ * G).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self G
  have hn : ‖Gᵀ * G‖ = ‖G‖^2 := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using
      Matrix.l2_opNorm_conjTranspose_mul_self G
  simpa only [← matrix_l2_norm_eq, hn, ← pow_mul] using posSemidef_trace_pow_le (Gᵀ*G) hp m

#print axioms diagonal_norm_le
#print axioms trace_pow_eq_sum_eigenvalues
#print axioms hermitian_norm_eq_diagonal
#print axioms abs_eigenvalue_le_norm
#print axioms posSemidef_norm_pow_le_trace
#print axioms posSemidef_trace_pow_le
#print axioms gram_trace_pow_le
end GaussianTensorTrace
