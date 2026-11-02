import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import InverseQuadratic
import Mathlib.Tactic

noncomputable section
open Matrix

namespace GaussianEllipsoid.CappedSimplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def twoColumns (u v : ι → ℝ) : Matrix ι (Fin 2) ℝ :=
  fun i j => ![u i, v i] j

def signedDiag (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![t, -t]

/-- The signed rank-two update factors through a two-column matrix. -/
theorem rankTwo_update_factor (u v : ι → ℝ) (t : ℝ) :
    t • (Matrix.vecMulVec u u - Matrix.vecMulVec v v) =
      twoColumns u v * signedDiag t * (twoColumns u v).transpose := by
  ext i j
  simp [twoColumns, signedDiag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.vecMulVec, smul_eq_mul]
  ring

/-- The elementary two-dimensional determinant polynomial. -/
theorem det_one_signedDiag_mul (G : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) :
    Matrix.det (1 + signedDiag t * G) =
      1 + (G 0 0 - G 1 1) * t - Matrix.det G * t ^ 2 := by
  simp [signedDiag, Matrix.det_fin_two, Matrix.diagonal_mul]
  ring

/-- A positive-definite matrix under a signed rank-two perturbation has a
concave quadratic determinant, with its coefficient certified by a Gram determinant. -/
theorem det_rankTwo_update {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (u v : ι → ℝ) (t : ℝ) :
    Matrix.det (A + t • (Matrix.vecMulVec u u - Matrix.vecMulVec v v)) =
      A.det + A.det *
        (((twoColumns u v).transpose * A⁻¹ * twoColumns u v) 0 0 -
         ((twoColumns u v).transpose * A⁻¹ * twoColumns u v) 1 1) * t -
      (A.det * Matrix.det ((twoColumns u v).transpose * A⁻¹ * twoColumns u v)) * t ^ 2 := by
  rw [rankTwo_update_factor]
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (ne_of_gt hA.det_pos)
  rw [Matrix.mul_assoc, Matrix.det_add_mul _ _ hunit]
  rw [Matrix.mul_assoc (signedDiag t), Matrix.mul_assoc (signedDiag t)]
  rw [det_one_signedDiag_mul]
  ring

/-- The negative quadratic coefficient is nonnegative by positivity of the
inverse-matrix Gram determinant. -/
theorem rankTwo_quadratic_coefficient_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (u v : ι → ℝ) :
    0 ≤ A.det * Matrix.det ((twoColumns u v).transpose * A⁻¹ * twoColumns u v) := by
  have hGram := hA.inv.posSemidef.conjTranspose_mul_mul_same (twoColumns u v)
  have hGram' : ((twoColumns u v).transpose * A⁻¹ * twoColumns u v).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hGram
  have hdet : 0 ≤ Matrix.det ((twoColumns u v).transpose * A⁻¹ * twoColumns u v) := by
    rw [hGram'.isHermitian.det_eq_prod_eigenvalues]
    exact Finset.prod_nonneg (fun i _ => by simpa using hGram'.eigenvalues_nonneg i)
  exact mul_nonneg (le_of_lt hA.det_pos) hdet

/-- Inverse natural determinant powers are convex along every signed
rank-two direction while the updated matrices remain positive definite. -/
theorem convexOn_det_rankTwo_neg_nat_zpow {A : Matrix ι ι ℝ} (hA : A.PosDef)
    (u v : ι → ℝ) {I : Set ℝ} (hI : Convex ℝ I)
    (hpos : ∀ t ∈ I, (A + t • (Matrix.vecMulVec u u - Matrix.vecMulVec v v)).PosDef)
    (s : ℕ) :
    ConvexOn ℝ I (fun t =>
      (Matrix.det (A + t • (Matrix.vecMulVec u u - Matrix.vecMulVec v v))) ^ (-(s : ℤ))) := by
  simp_rw [det_rankTwo_update hA u v]
  apply convexOn_quadratic_neg_nat_zpow _ _ _
    (rankTwo_quadratic_coefficient_nonneg hA u v) hI
  intro t ht
  rw [← det_rankTwo_update hA u v t]
  exact (hpos t ht).det_pos

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.convexOn_det_rankTwo_neg_nat_zpow
