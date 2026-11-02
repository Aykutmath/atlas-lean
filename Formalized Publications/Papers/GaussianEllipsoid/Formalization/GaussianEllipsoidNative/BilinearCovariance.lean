import GaussianRectangularSmallBall
import CappedDeterminantExtended
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open Matrix Finset
open scoped Kronecker ENNReal

namespace GaussianEllipsoid.SmallBall
open CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- With the left Gaussian family fixed, the bilinear output is a rectangular
linear image of all right Gaussian coordinates. Output coordinates are row,column. -/
def bilinearDriver (scale : ℝ) (z : κ → ℝ) (g : κ → ι → ℝ) :
    Matrix (ι × ι) (κ × ι) ℝ :=
  fun p q => if q.2 = p.2 then scale * z q.1 * g q.1 p.1 else 0

/-- The exact covariance of the full vectorized bilinear matrix, with independent
columns. This is an equality of actual finite matrices. -/
theorem covariance_bilinearDriver (scale : ℝ) (z : κ → ℝ) (g : κ → ι → ℝ) :
    covariance (bilinearDriver scale z g) =
      (scale ^ 2 • weightedGram g (fun i => (z i) ^ 2)) ⊗ₖ (1 : Matrix ι ι ℝ) := by
  ext p q
  rcases p with ⟨p, j⟩
  rcases q with ⟨q, l⟩
  simp only [covariance, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    bilinearDriver, Matrix.kronecker_apply, Matrix.smul_apply, smul_eq_mul,
    weightedGram, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply]
  by_cases hjl : j = l
  · subst l
    simp only [Matrix.one_apply_eq, mul_one]
    simp only [ite_mul, mul_ite, mul_zero, zero_mul, if_true]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [hjl, Matrix.one_apply, ite_mul, mul_ite, Finset.sum_ite_eq', eq_comm]

/-- Kronecker covariance gives precisely the determinant exponent required by
conditioning on one Gaussian factor. -/
theorem det_covariance_bilinearDriver (scale : ℝ) (z : κ → ℝ) (g : κ → ι → ℝ) :
    (covariance (bilinearDriver scale z g)).det =
      ((scale ^ 2) ^ Fintype.card ι * (weightedGram g (fun i => (z i) ^ 2)).det) ^ Fintype.card ι := by
  rw [covariance_bilinearDriver, Matrix.det_kronecker, Matrix.det_smul, Matrix.det_one]
  simp

/-- In even row dimension, the square-root determinant becomes a natural
inverse-Wishart power. No real half-power at a singular determinant is used. -/
theorem sqrt_det_covariance_bilinearDriver {s : ℕ} (hs : Fintype.card ι = 2 * s)
    (scale : ℝ) (z : κ → ℝ) (g : κ → ι → ℝ) :
    Real.sqrt (covariance (bilinearDriver scale z g)).det =
      scale ^ (Fintype.card ι * Fintype.card ι) *
        (weightedGram g (fun i => (z i) ^ 2)).det ^ s := by
  let D := (weightedGram g (fun i => (z i) ^ 2)).det
  have hD : 0 ≤ D := posSemidef_det_nonneg (weightedGram_posSemidef g (fun i => sq_nonneg (z i)))
  rw [det_covariance_bilinearDriver]
  have he : ((scale ^ 2) ^ Fintype.card ι * D) ^ Fintype.card ι =
      (((scale ^ 2) ^ Fintype.card ι * D) ^ s) ^ 2 := by
    rw [← pow_mul (((scale ^ 2) ^ Fintype.card ι) * D) s 2]
    congr 1
    omega
  change Real.sqrt (((scale ^ 2) ^ Fintype.card ι * D) ^ Fintype.card ι) = _
  rw [he, Real.sqrt_sq (by positivity)]
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have hn : 2 * (Fintype.card ι * s) = Fintype.card ι * Fintype.card ι := by
    rw [hs]
    ring
  rw [hn]

/-- The extended inverse covariance Jacobian factors into a finite scale and
the exact extended inverse determinant moment already controlled by capped weights. -/
theorem covarianceInverseJacobian_bilinearDriver {s : ℕ} (hs : Fintype.card ι = 2 * s)
    {scale : ℝ} (hscale : 0 < scale) (z : κ → ℝ) (g : κ → ι → ℝ) :
    covarianceInverseJacobian (bilinearDriver scale z g) =
      (ENNReal.ofReal (scale ^ (Fintype.card ι * Fintype.card ι)))⁻¹ *
        extendedDetInv s (weightedGram g (fun i => (z i) ^ 2)) := by
  have hD : 0 ≤ (weightedGram g (fun i => (z i) ^ 2)).det :=
    posSemidef_det_nonneg (weightedGram_posSemidef g (fun i => sq_nonneg (z i)))
  have hpow : 0 < scale ^ (Fintype.card ι * Fintype.card ι) := pow_pos hscale _
  rw [covarianceInverseJacobian, sqrt_det_covariance_bilinearDriver hs,
    ENNReal.ofReal_mul (le_of_lt hpow), ENNReal.ofReal_pow hD]
  exact ENNReal.mul_inv (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hpow))
    (Or.inl ENNReal.ofReal_ne_top)

/-- Coordinate form of the actual bilinear linear image. -/
theorem matrixCLM_bilinearDriver_apply (scale : ℝ) (z : κ → ℝ) (g : κ → ι → ℝ)
    (x : EuclideanSpace ℝ (κ × ι)) (p q : ι) :
    matrixCLM (bilinearDriver scale z g) x (p, q) =
      scale * ∑ i, z i * g i p * x (i, q) := by
  change ((bilinearDriver scale z g).mulVec (fun j => x j)) (p, q) = _
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, bilinearDriver]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.covarianceInverseJacobian_bilinearDriver
#print axioms GaussianEllipsoid.SmallBall.matrixCLM_bilinearDriver_apply
