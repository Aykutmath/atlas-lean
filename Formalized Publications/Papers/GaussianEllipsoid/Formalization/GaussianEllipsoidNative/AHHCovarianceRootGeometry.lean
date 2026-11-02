import AHHSphereObservableBounds
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Real.Sqrt

/-! Exact Euclidean synthesis and covariance-root geometry for the actual observable. -/
noncomputable section
open GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators Matrix.Norms.L2Operator
namespace AHHRadial

/-- The genuine rectangular synthesis matrix with the supplied vectors as columns. -/
def complexColumnMatrix {n h : ℕ} (v : Fin n → ProductSpace h) :
    Matrix (Fin h × Fin h) (Fin n) ℂ := fun p i => v i p

theorem complexColumnMatrix_covariance {n h : ℕ} (v : Fin n → ProductSpace h) :
    complexColumnMatrix v * (complexColumnMatrix v).conjTranspose =
      ∑ i, projector (fun p => v i p) := by
  ext p q
  simp [complexColumnMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, projector]

theorem complexColumnMatrix_norm_sq {n h : ℕ} (v : Fin n → ProductSpace h) :
    ‖complexColumnMatrix v‖ ^ 2 =
      ‖∑ i, InnerProductSpace.rankOne ℂ (v i) (v i)‖ := by
  have hm : cMatrixCLM (complexColumnMatrix v * (complexColumnMatrix v).conjTranspose) =
      ∑ i, InnerProductSpace.rankOne ℂ (v i) (v i) := by
    rw [complexColumnMatrix_covariance]
    unfold cMatrixCLM
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => cMatrixCLM_projector_eq_rankOne (v i)
  rw [← hm, cMatrixCLM_norm]
  have he := Matrix.l2_opNorm_conjTranspose_mul_self (complexColumnMatrix v).conjTranspose
  simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, pow_two]
    using he.symm

theorem sqrt_covariance_norm_eq_column_norm {n h : ℕ} (v : Fin n → ProductSpace h) :
    Real.sqrt ‖∑ i, InnerProductSpace.rankOne ℂ (v i) (v i)‖ =
      ‖complexColumnMatrix v‖ := by
  rw [← complexColumnMatrix_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem complexColumnMatrix_opNorm_le {n h : ℕ} (v : Fin n → ProductSpace h) :
    ‖complexColumnMatrix v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  have happ : ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
      (complexColumnMatrix v)) z = ∑ i, z i • v i := by
    ext p
    simp [complexColumnMatrix, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      mul_comm, PiLp.smul_apply]
  rw [happ]
  calc
    ‖∑ i, z i • v i‖ ≤ ∑ i, ‖z i • v i‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖z i‖ := by simp only [norm_smul, mul_comm]
    _ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Real.sqrt (∑ i, ‖z i‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ i, ‖v i‖ ^ 2) * ‖z‖ := by
      rw [← EuclideanSpace.norm_sq_eq z, Real.sqrt_sq (norm_nonneg z)]

theorem covariance_root_sq_dist_le {n h : ℕ} (v w : Fin n → ProductSpace h) :
    (Real.sqrt ‖∑ i, InnerProductSpace.rankOne ℂ (v i) (v i)‖ -
      Real.sqrt ‖∑ i, InnerProductSpace.rankOne ℂ (w i) (w i)‖) ^ 2 ≤
      ∑ i, ‖v i - w i‖ ^ 2 := by
  rw [sqrt_covariance_norm_eq_column_norm, sqrt_covariance_norm_eq_column_norm]
  have he : complexColumnMatrix v - complexColumnMatrix w =
      complexColumnMatrix (fun i => v i - w i) := rfl
  have hb : |‖complexColumnMatrix v‖ - ‖complexColumnMatrix w‖| ≤
      Real.sqrt (∑ i, ‖v i - w i‖ ^ 2) := by
    exact (abs_norm_sub_norm_le (complexColumnMatrix v) (complexColumnMatrix w)).trans
      (by rw [he]; exact complexColumnMatrix_opNorm_le (fun i => v i - w i))
  have hs : 0 ≤ ∑ i, ‖v i - w i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq := sq_le_sq₀ (abs_nonneg (‖complexColumnMatrix v‖ - ‖complexColumnMatrix w‖))
    (Real.sqrt_nonneg (∑ i, ‖v i - w i‖ ^ 2))
  rw [← sq_abs, ← Real.sq_sqrt hs]
  exact hsq.mpr hb

#print axioms complexColumnMatrix_norm_sq
#print axioms covariance_root_sq_dist_le
end AHHRadial
