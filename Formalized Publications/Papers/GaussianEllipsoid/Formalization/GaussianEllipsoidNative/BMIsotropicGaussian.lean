import BMMatrixBridge
import FrobeniusCoordinates
import GaussianProductMoments
import GaussianMatrixOperator

noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

def transposeFrob {d : ℕ} (A : HMat d) : HMat d :=
  (WithLp.equiv 2 _).symm (fun j => (WithLp.equiv 2 _).symm (fun i => A i j))

theorem transposeFrob_norm {d : ℕ} (A : HMat d) : ‖transposeFrob A‖ = ‖A‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [frobenius_norm_sq, frobenius_norm_sq, Finset.sum_comm]
  rfl

def symmetricFrobLM (d : ℕ) : HMat d →ₗ[ℝ] HMat d where
  toFun A := (1/2 : ℝ) • (A + transposeFrob A)
  map_add' A B := by ext j i; simp [transposeFrob]; ring
  map_smul' c A := by ext j i; simp [transposeFrob]; ring

@[simp] theorem symmetricFrob_apply {d : ℕ} (A : HMat d) (j i : Fin d) :
    symmetricFrobLM d A j i = (A j i + A i j)/2 := by
  change (1/2 : ℝ) * (A j i + A i j) = _
  ring

theorem symmetricFrob_norm_le {d : ℕ} (A : HMat d) : ‖symmetricFrobLM d A‖ ≤ ‖A‖ := by
  change ‖(1/2 : ℝ) • (A + transposeFrob A)‖ ≤ ‖A‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have h := norm_add_le A (transposeFrob A)
  rw [transposeFrob_norm] at h
  linarith

def isotropicSymmetricOp (d : ℕ) (x : EuclideanSpace ℝ (Fin d × Fin d)) : Op d :=
  frobeniusOperator (symmetricFrobLM d ((frobeniusEquivEuclidean d d).symm x))

theorem isotropicSymmetricOp_symmetric (d : ℕ) (x : EuclideanSpace ℝ (Fin d × Fin d)) :
    (isotropicSymmetricOp d x).toLinearMap.IsSymmetric := by
  rw [← opMatrix_toEuclideanLin, ← Matrix.isHermitian_iff_isSymmetric]
  change (opMatrix (isotropicSymmetricOp d x))ᴴ = opMatrix (isotropicSymmetricOp d x)
  unfold opMatrix isotropicSymmetricOp
  rw [operatorFrobenius_frobeniusOperator]
  ext i j
  simp [frobeniusToMatrix]
  ring

theorem isotropicSymmetricOp_frobenius (d : ℕ) (x : EuclideanSpace ℝ (Fin d × Fin d)) :
    operatorFrobenius (isotropicSymmetricOp d x) =
      symmetricFrobLM d ((frobeniusEquivEuclidean d d).symm x) := by
  simp [isotropicSymmetricOp]

theorem isotropicSymmetricOp_frobenius_lipschitz (d : ℕ)
    (x y : EuclideanSpace ℝ (Fin d × Fin d)) :
    ‖operatorFrobenius (isotropicSymmetricOp d x) - operatorFrobenius (isotropicSymmetricOp d y)‖ ≤
      ‖x-y‖ := by
  rw [isotropicSymmetricOp_frobenius, isotropicSymmetricOp_frobenius,
    ← map_sub, ← map_sub]
  exact (symmetricFrob_norm_le _).trans_eq (LinearIsometryEquiv.norm_map _ _)

/-- PSD unit-ball support of an actual standard Gaussian in the symmetric matrix space.
The input is d² independent standard real Gaussian coordinates; symmetrization is the
orthogonal projection, giving variances 1 on diagonal and 1/2 off diagonal. -/
def gaussianPSDSupport (d : ℕ) (x : EuclideanSpace ℝ (Fin d × Fin d)) : ℝ :=
  ‖operatorFrobenius (positivePart (isotropicSymmetricOp d x) (isotropicSymmetricOp_symmetric d x))‖

theorem gaussianPSDSupport_lipschitz (d : ℕ) : LipschitzWith 1 (gaussianPSDSupport d) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  exact (positive_norm_lipschitz _ _ _ _).trans (isotropicSymmetricOp_frobenius_lipschitz d x y)

theorem gaussianPSDSupport_continuous (d : ℕ) : Continuous (gaussianPSDSupport d) :=
  (gaussianPSDSupport_lipschitz d).continuous

theorem isotropicSymmetricOp_neg (d : ℕ) (x : EuclideanSpace ℝ (Fin d × Fin d)) :
    isotropicSymmetricOp d (-x) = -isotropicSymmetricOp d x := by
  apply (operatorFrobeniusLinearEquiv d d).injective
  simp only [operatorFrobeniusLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, isotropicSymmetricOp_frobenius, map_neg, operatorFrobenius_neg]

theorem gaussianPSDSupport_sign_energy (d : ℕ) (x : EuclideanSpace ℝ (Fin d × Fin d)) :
    (gaussianPSDSupport d x)^2 + (gaussianPSDSupport d (-x))^2 =
      ‖operatorFrobenius (isotropicSymmetricOp d x)‖^2 := by
  have h := positive_energy_sign_split (isotropicSymmetricOp d x) (isotropicSymmetricOp_symmetric d x)
  simpa only [gaussianPSDSupport, isotropicSymmetricOp_neg] using h

end BMGeometry
