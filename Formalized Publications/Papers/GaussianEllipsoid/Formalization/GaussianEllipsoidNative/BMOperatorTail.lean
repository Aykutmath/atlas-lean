import BMIsotropicGaussian

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

theorem operatorFrobenius_adjoint {d : ℕ} (T : Op d) :
    operatorFrobenius (ContinuousLinearMap.adjoint T) = transposeFrob (operatorFrobenius T) := by
  ext j i
  change (ContinuousLinearMap.adjoint T (EuclideanSpace.basisFun (Fin d) ℝ j)) i =
    T (EuclideanSpace.basisFun (Fin d) ℝ i) j
  rw [← EuclideanSpace.basisFun_repr (Fin d) ℝ
    (ContinuousLinearMap.adjoint T (EuclideanSpace.basisFun (Fin d) ℝ j)) i,
    (EuclideanSpace.basisFun (Fin d) ℝ).repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_comm,
    ← (EuclideanSpace.basisFun (Fin d) ℝ).repr_apply_apply,
    EuclideanSpace.basisFun_repr]

theorem gaussianMatrixCLM_opMatrix (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    opMatrix (gaussianMatrixCLM d d x) = entryMatrix d d x := by
  apply Matrix.toEuclideanLin.injective
  rw [opMatrix_toEuclideanLin]
  rfl

theorem gaussianMatrixCLM_frobenius (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    operatorFrobenius (gaussianMatrixCLM d d x) =
      (frobeniusEquivEuclidean d d).symm ((WithLp.equiv 2 _).symm x) := by
  ext j i
  have h := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) (gaussianMatrixCLM_opMatrix d x)
  exact h

theorem isotropicSymmetricOp_eq_symmetrize (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x) =
      (1/2 : ℝ) • (gaussianMatrixCLM d d x + ContinuousLinearMap.adjoint (gaussianMatrixCLM d d x)) := by
  apply (operatorFrobeniusLinearEquiv d d).injective
  simp only [operatorFrobeniusLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [isotropicSymmetricOp_frobenius, operatorFrobenius_smul, operatorFrobenius_add,
    operatorFrobenius_adjoint, gaussianMatrixCLM_frobenius]
  rfl

theorem isotropicSymmetricOp_norm_le (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖ ≤ ‖gaussianMatrixCLM d d x‖ := by
  rw [isotropicSymmetricOp_eq_symmetrize]
  change ‖(1/2 : ℝ) • (gaussianMatrixCLM d d x + ContinuousLinearMap.adjoint (gaussianMatrixCLM d d x))‖ ≤ ‖gaussianMatrixCLM d d x‖
  rw [norm_smul (1/2 : ℝ) (gaussianMatrixCLM d d x + ContinuousLinearMap.adjoint (gaussianMatrixCLM d d x)), Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have h := norm_add_le (gaussianMatrixCLM d d x) (ContinuousLinearMap.adjoint (gaussianMatrixCLM d d x))
  rw [ContinuousLinearMap.adjoint.norm_map] at h
  linarith

/-- Genuine finite-dimensional operator-norm tail for the standard symmetric Gaussian. -/
theorem isotropicSymmetricOp_net_tail (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (gaussianProductLaw (Fin d × Fin d)).real
      {x | 2*r < ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖} ≤
      2*(9:ℝ)^(d+d)*Real.exp (-(r^2)/2) := by
  apply (measureReal_mono (show {x | 2*r < ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖} ⊆
    {x | 2*r < ‖gaussianMatrixCLM d d x‖} from fun x hx => hx.trans_le (isotropicSymmetricOp_norm_le d x))).trans
  exact gaussianMatrixCLM_net_tail d d hr

/-- A coarse spectral bound already gives the Frobenius good-event bound at scale d. -/
theorem frobenius_le_sqrt_dim_opNorm {d : ℕ} (T : Op d) :
    ‖operatorFrobenius T‖ ≤ Real.sqrt d * ‖T‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [← sum_norm_sq_operator_basis _ (EuclideanSpace.basisFun (Fin d) ℝ), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    _ ≤ ∑ _i : Fin d, ‖T‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := T.le_opNorm (EuclideanSpace.basisFun (Fin d) ℝ i)
      rw [(EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one, mul_one] at h
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
    _ = _ := by simp

end BMGeometry
