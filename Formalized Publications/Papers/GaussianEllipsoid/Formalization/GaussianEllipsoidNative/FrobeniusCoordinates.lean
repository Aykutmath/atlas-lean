import FrobeniusFactorCover

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid

/-- Flattening in `(row,column)` coordinates is a genuine real linear isometry
between Frobenius matrices and Euclidean entry space. -/
def frobeniusEquivEuclidean (r q : ℕ) :
    FrobeniusMatrix r q ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r × Fin q) where
  toFun A := (WithLp.equiv 2 _).symm (fun p => A p.2 p.1)
  invFun x := (WithLp.equiv 2 _).symm (fun j =>
    (WithLp.equiv 2 _).symm (fun i => x (i, j)))
  left_inv A := by ext j i; rfl
  right_inv x := by ext p; rfl
  map_add' A B := by ext p; rfl
  map_smul' c A := by ext p; rfl
  norm_map' A := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, frobenius_norm_sq, Fintype.sum_prod_type, Finset.sum_comm]
    change (∑ j, ∑ i, ‖A j i‖ ^ 2) = ∑ j, ∑ i, (A j i) ^ 2
    simp only [Real.norm_eq_abs, sq_abs]

@[simp] theorem frobeniusEquivEuclidean_apply {r q : ℕ} (A : FrobeniusMatrix r q)
    (i : Fin r) (j : Fin q) : frobeniusEquivEuclidean r q A (i, j) = frobeniusToMatrix A i j := rfl

end GaussianEllipsoid
#print axioms GaussianEllipsoid.frobeniusEquivEuclidean
