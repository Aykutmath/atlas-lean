import GaussianRandomCenterSmallBall
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace GaussianEllipsoid.SmallBall
variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]

/-- The genuine Euclidean continuous linear map associated with a real matrix. -/
def matrixCLM (A : Matrix ι κ ℝ) : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)

@[simp] theorem matrixCLM_mul (A : Matrix ι κ ℝ) (B : Matrix κ τ ℝ) :
    matrixCLM (A * B) = matrixCLM A ∘L matrixCLM B := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (A * B) x = Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x)
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [Matrix.toLin_mul (EuclideanSpace.basisFun τ ℝ).toBasis
    (EuclideanSpace.basisFun κ ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis A B]
  rfl

@[simp] theorem matrixCLM_one : matrixCLM (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toEuclideanLin (1 : Matrix ι ι ℝ) x = x
  simp only [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.toLin_one, LinearMap.id_apply]

@[simp] theorem matrixCLM_transpose (A : Matrix ι κ ℝ) :
    matrixCLM A.transpose = ContinuousLinearMap.adjoint (matrixCLM A) := by
  rw [matrixCLM, matrixCLM, ← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]

theorem det_matrixCLM (A : Matrix ι ι ℝ) :
    LinearMap.det (matrixCLM A).toLinearMap = A.det := by
  change LinearMap.det (Matrix.toEuclideanLin A) = A.det
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]

/-- Real covariance of a rectangular matrix. -/
def covariance (A : Matrix ι κ ℝ) : Matrix ι ι ℝ := A * A.transpose

theorem covariance_posSemidef (A : Matrix ι κ ℝ) : (covariance A).PosSemidef := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  simpa only [covariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose A

/-- The unique positive-semidefinite square root of the actual covariance. -/
def covarianceRoot (A : Matrix ι κ ℝ) : Matrix ι ι ℝ := CFC.sqrt (covariance A)

theorem covarianceRoot_mul_self (A : Matrix ι κ ℝ) :
    covarianceRoot A * covarianceRoot A = covariance A :=
  CFC.sqrt_mul_sqrt_self (covariance A) (covariance_posSemidef A).nonneg

theorem covarianceRoot_posSemidef (A : Matrix ι κ ℝ) : (covarianceRoot A).PosSemidef :=
  (CFC.sqrt_nonneg (covariance A)).posSemidef

theorem covarianceRoot_det_sq (A : Matrix ι κ ℝ) :
    (covarianceRoot A).det ^ 2 = (covariance A).det := by
  rw [pow_two, ← Matrix.det_mul, covarianceRoot_mul_self]

theorem posSemidef_det_nonneg {H : Matrix ι ι ℝ} (hH : H.PosSemidef) : 0 ≤ H.det := by
  rw [hH.isHermitian.det_eq_prod_eigenvalues]
  exact Finset.prod_nonneg (fun i _ => by simpa using hH.eigenvalues_nonneg i)

/-- The determinant of the covariance square root is the positive square root
of the covariance determinant, including the singular case. -/
theorem covarianceRoot_det (A : Matrix ι κ ℝ) :
    (covarianceRoot A).det = Real.sqrt (covariance A).det := by
  have h := congrArg Real.sqrt (covarianceRoot_det_sq A)
  simpa only [Real.sqrt_sq (posSemidef_det_nonneg (covarianceRoot_posSemidef A))] using h

def whitenedMatrix (A : Matrix ι κ ℝ) : Matrix ι κ ℝ := (covarianceRoot A)⁻¹ * A

theorem covarianceRoot_det_ne_zero (A : Matrix ι κ ℝ) (hA : (covariance A).det ≠ 0) :
    (covarianceRoot A).det ≠ 0 := by
  intro hzero
  have h := covarianceRoot_det_sq A
  rw [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  exact hA h.symm

/-- Whitening is an actual factorization, not a distributional premise. -/
theorem covarianceRoot_mul_whitened (A : Matrix ι κ ℝ) (hA : (covariance A).det ≠ 0) :
    covarianceRoot A * whitenedMatrix A = A := by
  rw [whitenedMatrix, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (covarianceRoot_det_ne_zero A hA)),
    Matrix.one_mul]

/-- The rows of the whitened matrix are exactly orthonormal. -/
theorem whitenedMatrix_mul_transpose (A : Matrix ι κ ℝ) (hA : (covariance A).det ≠ 0) :
    whitenedMatrix A * (whitenedMatrix A).transpose = 1 := by
  have hS : IsUnit (covarianceRoot A).det :=
    isUnit_iff_ne_zero.mpr (covarianceRoot_det_ne_zero A hA)
  have hsym : ((covarianceRoot A)⁻¹).transpose = (covarianceRoot A)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (covarianceRoot_posSemidef A).inv.isHermitian.eq
  simp only [whitenedMatrix, Matrix.transpose_mul, hsym]
  calc (covarianceRoot A)⁻¹ * A * (A.transpose * (covarianceRoot A)⁻¹) =
      (covarianceRoot A)⁻¹ * (covariance A) * (covarianceRoot A)⁻¹ := by
        simp only [covariance, Matrix.mul_assoc]
    _ = (covarianceRoot A)⁻¹ * (covarianceRoot A * covarianceRoot A) * (covarianceRoot A)⁻¹ := by
      rw [covarianceRoot_mul_self]
    _ = 1 := by
      rw [← Matrix.mul_assoc (covarianceRoot A)⁻¹,
        Matrix.nonsing_inv_mul _ hS, Matrix.one_mul, Matrix.mul_nonsing_inv _ hS]

/-- The corresponding Euclidean map is a coisometry. -/
theorem whitenedMatrix_coisometry (A : Matrix ι κ ℝ) (hA : (covariance A).det ≠ 0) :
    matrixCLM (whitenedMatrix A) ∘L ContinuousLinearMap.adjoint (matrixCLM (whitenedMatrix A)) =
      ContinuousLinearMap.id ℝ _ := by
  rw [← matrixCLM_transpose, ← matrixCLM_mul, whitenedMatrix_mul_transpose A hA, matrixCLM_one]

/-- Exact Jacobian in covariance form, also valid at singular covariance. -/
theorem covarianceRoot_inverseJacobian (A : Matrix ι κ ℝ) :
    inverseJacobian (matrixCLM (covarianceRoot A)).toLinearMap =
      (ENNReal.ofReal (Real.sqrt (covariance A).det))⁻¹ := by
  rw [inverseJacobian, det_matrixCLM, covarianceRoot_det, abs_of_nonneg (Real.sqrt_nonneg _)]

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.whitenedMatrix_coisometry
#print axioms GaussianEllipsoid.SmallBall.covarianceRoot_inverseJacobian
