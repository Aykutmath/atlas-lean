import SpectralFrobenius
import Mathlib.Tactic

open scoped BigOperators InnerProductSpace

namespace GaussianEllipsoid

/-- The squared norm of an operator is its actual Gram eigenvalue quadratic
form in the right singular coordinates. -/
theorem norm_sq_gram_diagonal {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (x : Euclid q) :
    ‖T x‖^2 = ∑ i, gramEigenvalue T i * ((rightSingularBasis T).repr x i)^2 := by
  let b := rightSingularBasis T
  have hinner : ‖T x‖^2 = ⟪x, ContinuousLinearMap.adjoint T (T x)⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  rw [hinner, ← b.sum_inner_mul_inner x (ContinuousLinearMap.adjoint T (T x))]
  apply Finset.sum_congr rfl
  intro i _
  have heig := (gramSymmetric T).eigenvectorBasis_apply_self_apply finrank_euclideanSpace_fin x i
  change (b.repr (ContinuousLinearMap.adjoint T (T x))) i =
    gramEigenvalue T i * (b.repr x i) at heig
  simp only [OrthonormalBasis.repr_apply_apply] at heig ⊢
  change ⟪x, b i⟫_ℝ * ⟪b i, ContinuousLinearMap.adjoint T (T x)⟫_ℝ = _
  rw [real_inner_comm x (b i), heig]
  rw [real_inner_comm (b i) x]
  ring

/-- Gram eigenvalues are nonnegative and controlled by the genuine operator norm. -/
theorem gramEigenvalue_bounds {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    0 ≤ gramEigenvalue T i ∧ gramEigenvalue T i ≤ ‖T‖^2 := by
  rw [gramEigenvalue_eq_norm_sq]
  refine ⟨sq_nonneg _, ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
  have hh := T.le_opNorm (rightSingularBasis T i)
  simpa using hh

/-- The sum of Gram eigenvalues is exactly the squared Frobenius norm. -/
theorem sum_gramEigenvalue {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    ∑ i, gramEigenvalue T i = ‖operatorFrobenius T‖^2 := by
  simp_rw [gramEigenvalue_eq_norm_sq]
  exact sum_norm_sq_operator_basis T (rightSingularBasis T)

#print axioms norm_sq_gram_diagonal
#print axioms gramEigenvalue_bounds
#print axioms sum_gramEigenvalue

end GaussianEllipsoid
