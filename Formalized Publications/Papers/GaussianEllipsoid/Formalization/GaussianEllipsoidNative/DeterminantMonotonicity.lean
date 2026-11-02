import BilinearCovariance
import Mathlib.Analysis.Matrix.Order

noncomputable section
open Matrix Finset MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator MatrixOrder

namespace GaussianEllipsoid.SmallBall
open CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Determinant is monotone under addition of a PSD matrix, including singular
base matrices. The proof uses whitening and the already proved scalar ridge bound. -/
theorem posSemidef_det_add_ge {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    B.det ≤ (A + B).det := by
  by_cases hBzero : B.det = 0
  · rw [hBzero]
    exact posSemidef_det_nonneg (hA.add hB)
  let S : Matrix ι ι ℝ := CFC.sqrt B
  have hS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg B).posSemidef
  have hSdet : S.det ≠ 0 := by
    intro hz
    have hd := congrArg Matrix.det hS
    rw [Matrix.det_mul, hz, zero_mul] at hd
    exact hBzero hd.symm
  have hSunit : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet
  have hinvsym : (S⁻¹).transpose = S⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hSpsd.inv.isHermitian.eq
  let C : Matrix ι ι ℝ := S⁻¹ * A * S⁻¹
  have hC : C.PosSemidef := by
    simpa only [C, Matrix.conjTranspose_eq_transpose_of_trivial, hinvsym] using
      hA.mul_mul_conjTranspose_same (S⁻¹)
  have hfactor : S * (1 + C) * S = A + B := by
    calc S * (1 + C) * S = S * S + S * C * S := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
         _ = B + A := by
            rw [hS]
            congr 1
            simp only [C, ← Matrix.mul_assoc]
            rw [Matrix.mul_nonsing_inv S hSunit, Matrix.one_mul,
              Matrix.mul_assoc A, Matrix.nonsing_inv_mul S hSunit, Matrix.mul_one]
         _ = A + B := add_comm _ _
  have hdet : (A + B).det = B.det * (1 + C).det := by
    rw [← hfactor, Matrix.det_mul_right_comm, hS, Matrix.det_mul]
  have hCdet : (1 : ℝ) ≤ (1 + C).det := by
    simpa only [one_pow, one_smul] using det_scalar_add_posSemidef_ge hC (show (0 : ℝ) ≤ 1 by norm_num)
  rw [hdet]
  exact le_mul_of_one_le_right (posSemidef_det_nonneg hB) hCdet

/-- Correct extended inverse determinant order reversal; singular determinants
never become zero through real division. -/
theorem extendedDetInv_add_le (s : ℕ) {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    extendedDetInv s (A + B) ≤ extendedDetInv s B := by
  unfold extendedDetInv
  apply ENNReal.inv_le_inv.mpr
  apply pow_le_pow_left'
  exact ENNReal.ofReal_le_ofReal (posSemidef_det_add_ge hA hB)

theorem weightedGram_add (g : κ → ι → ℝ) (u v : κ → ℝ) :
    weightedGram g (u + v) = weightedGram g u + weightedGram g v := by
  simp only [weightedGram, Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Disjoint coefficients add their conditional covariances exactly. -/
theorem weightedGram_disjoint_sq (g : κ → ι → ℝ) (u v : κ → ℝ)
    (hdisj : ∀ i, u i * v i = 0) :
    weightedGram g (fun i => (u i + v i) ^ 2) =
      weightedGram g (fun i => (u i) ^ 2) + weightedGram g (fun i => (v i) ^ 2) := by
  have hc : (fun i => (u i + v i) ^ 2) =
      (fun i => (u i) ^ 2) + (fun i => (v i) ^ 2) := by
    funext i
    simp only [Pi.add_apply]
    nlinarith [hdisj i]
  rw [hc, weightedGram_add]

/-- A completely arbitrary disjoint head can only improve the determinant
moment needed for the small-ball estimate. This avoids head/tail law splitting. -/
theorem extendedMoment_disjoint_le (μ : Measure (κ → ι → ℝ)) (s : ℕ)
    (u v : κ → ℝ) (hdisj : ∀ i, u i * v i = 0) :
    extendedMoment μ s (fun i => (u i + v i) ^ 2) ≤
      extendedMoment μ s (fun i => (v i) ^ 2) := by
  apply lintegral_mono
  intro g
  dsimp only
  rw [weightedGram_disjoint_sq g u v hdisj]
  exact extendedDetInv_add_le s
    (weightedGram_posSemidef g (fun i => sq_nonneg (u i)))
    (weightedGram_posSemidef g (fun i => sq_nonneg (v i)))

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.posSemidef_det_add_ge
#print axioms GaussianEllipsoid.SmallBall.extendedMoment_disjoint_le
