import UCQuadraticMGF
import OperatorFractionalNet
import BMMatrixBridge
import GaussianEllipsoid.ExactFit

/-! The correct Frobenius-domain, l1-codomain empirical operator and its
fixed deterministic half-net. -/
noncomputable section
open Module MeasureTheory
open scoped BigOperators Matrix InnerProductSpace ENNReal

namespace GaussianEllipsoid.UCContinuityGeometry

/-- Symmetric operators represented by their columns with the Frobenius norm. -/
def symmetricFrobenius (d : ℕ) : Submodule ℝ (FrobeniusMatrix d d) :=
  (BMUniformMoment.symmetricOperators d).comap
    (operatorFrobeniusLinearEquiv d d).symm.toLinearMap

abbrev SymFrob (d : ℕ) := ↥(symmetricFrobenius d)

def matrix {d : ℕ} (A : SymFrob d) : Square d := frobeniusToMatrix A.val

@[simp] theorem matrix_add {d : ℕ} (A B : SymFrob d) : matrix (A+B) = matrix A+matrix B := rfl
@[simp] theorem matrix_smul {d : ℕ} (t : ℝ) (A : SymFrob d) : matrix (t • A) = t • matrix A := rfl

 theorem matrix_transpose {d : ℕ} (A : SymFrob d) : (matrix A).transpose = matrix A := by
  have hsym : (frobeniusOperator A.val).toLinearMap.IsSymmetric := A.property
  have he : Matrix.toEuclideanLin (matrix A) = (frobeniusOperator A.val).toLinearMap := by
    simpa only [BMGeometry.opMatrix, operatorFrobenius_frobeniusOperator, matrix] using
      BMGeometry.opMatrix_toEuclideanLin (frobeniusOperator A.val)
  rw [← he] at hsym
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_iff_isSymmetric.mpr hsym

 theorem matrix_frobeniusNorm {d : ℕ} (A : SymFrob d) : frobeniusNorm (matrix A) = ‖A‖ := by
  apply (sq_eq_sq₀ (frobeniusNorm_nonneg _) (norm_nonneg _)).mp
  rw [frobeniusNorm_sq]
  change _ = ‖A.val‖^2
  rw [frobenius_norm_sq, Finset.sum_comm]
  rfl

 theorem symFrob_finrank_le (d : ℕ) : finrank ℝ (SymFrob d) ≤ d*d :=
  (symmetricFrobenius d).finrank_le.trans_eq (finrank_frobenius d d)

/-- A fixed Frobenius half-net with no cardinality assumption. -/
theorem exists_half_net (d : ℕ) :
    ∃ s : Finset (SymFrob d), (∀ A ∈ s, ‖A‖ = 1) ∧
      (s.card:ℝ) ≤ (5:ℝ)^(d*d) ∧
      ∀ A : SymFrob d, ‖A‖ = 1 → ∃ B ∈ s, ‖A-B‖ < (1:ℝ)/2 := by
  obtain ⟨s, hs, hc, hn, _⟩ := exists_internal_net
    {A : SymFrob d | ‖A‖ = 1} (R := 1) (ε := 1/2) (by norm_num) (by norm_num)
    (fun A hA => hA.le)
  refine ⟨s, hs, ?_, ?_⟩
  · norm_num at hc
    exact hc.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤5) (symFrob_finrank_le d))
  · intro A hA
    simpa only [dist_eq_norm] using hn A hA

abbrev L1Rows (n : ℕ) := PiLp 1 (fun _ : Fin n => ℝ)

/-- Actual centered quadratic rows, as a linear map into l1. -/
def empiricalLinear {d n : ℕ} (x : Sample d n) : SymFrob d →ₗ[ℝ] L1Rows n where
  toFun A := WithLp.toLp 1
    (fun i => ((quadratic (matrix A) (x i)-Matrix.trace (matrix A))/Real.sqrt 2)/(n:ℝ))
  map_add' A B := by
    ext i
    change ((quadratic (matrix (A+B)) (x i)-Matrix.trace (matrix (A+B)))/Real.sqrt 2)/(n:ℝ) =
      ((quadratic (matrix A) (x i)-Matrix.trace (matrix A))/Real.sqrt 2)/(n:ℝ) +
      ((quadratic (matrix B) (x i)-Matrix.trace (matrix B))/Real.sqrt 2)/(n:ℝ)
    rw [matrix_add, quadratic_add, Matrix.trace_add]
    ring
  map_smul' t A := by
    ext i
    change ((quadratic (matrix (t • A)) (x i)-Matrix.trace (matrix (t • A)))/Real.sqrt 2)/(n:ℝ) =
      t * (((quadratic (matrix A) (x i)-Matrix.trace (matrix A))/Real.sqrt 2)/(n:ℝ))
    rw [matrix_smul, quadratic_smul, Matrix.trace_smul]
    simp only [smul_eq_mul]
    ring

def empiricalOperator {d n : ℕ} (x : Sample d n) : SymFrob d →L[ℝ] L1Rows n :=
  (empiricalLinear x).toContinuousLinearMap

/-- Exact averaging normalization and exact project measurement. -/
theorem empiricalOperator_norm {d n : ℕ} (x : Sample d n) (A : SymFrob d) :
    ‖empiricalOperator x A‖ = (1/(n:ℝ))*∑ i, |measurementQ x (matrix A) i| := by
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one]
  change (∑ i, ‖((quadratic (matrix A) (x i)-Matrix.trace (matrix A))/Real.sqrt 2)/(n:ℝ)‖) = _
  simp only [Real.norm_eq_abs, abs_div, abs_of_nonneg (show (0:ℝ) ≤ n from Nat.cast_nonneg n),
    measurementQ]
  rw [← Finset.sum_div]
  ring

/-- Deterministic net transfer applies to every sample, without any random
operator norm assumption. -/
theorem operator_le_twice_net {d n : ℕ} (x : Sample d n) (s : Finset (SymFrob d))
    (hnet : ∀ A : SymFrob d, ‖A‖ = 1 → ∃ B ∈ s, ‖A-B‖ < (1:ℝ)/2)
    (b : ℝ) (hb : 0 ≤ b)
    (hvals : ∀ B ∈ s, (1/(n:ℝ))*∑ i, |measurementQ x (matrix B) i| ≤ b) :
    ‖empiricalOperator x‖ ≤ 2*b := by
  apply BMUniformMoment.operator_norm_le_twice_half_net _ s hnet b hb
  intro B hB
  rw [empiricalOperator_norm]
  exact hvals B hB

#print axioms empiricalOperator_norm
#print axioms exists_half_net
#print axioms operator_le_twice_net
end GaussianEllipsoid.UCContinuityGeometry
