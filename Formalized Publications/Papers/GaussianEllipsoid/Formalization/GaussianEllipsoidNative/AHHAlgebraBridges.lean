import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open WithLp
namespace AHHAlgebraBridges

variable {ι κ : Type*}

/-- The two signs are precisely -1 and +1. -/
def sign (s : Bool) : ℝ := if s then 1 else -1
/-- Unnormalized complex Gaussian factor from two real copies. -/
def complexFactor (a a' : ι → ℝ) (s : Bool) : ι → ℂ :=
  fun j => (a j : ℂ) + Complex.I * (sign s : ℂ) * (a' j : ℂ)
/-- Coordinate realization of a pure tensor. -/
def pureTensor (a : ι → ℂ) (b : κ → ℂ) : ι × κ → ℂ :=
  fun p => a p.1 * b p.2
/-- The paper's state, with the literal denominator 2h. -/
def productState (h : ℝ) (a a' : ι → ℝ) (b b' : κ → ℝ)
    (s t : Bool) : ι × κ → ℂ :=
  fun p => pureTensor (complexFactor a a' s) (complexFactor b b' t) p / (2 * (h : ℂ))
/-- Hermitian rank-one projector. -/
def projector (v : ι → ℂ) : Matrix ι ι ℂ := fun i j => v i * star (v j)
/-- Real tensor embedded into the complex coordinate space. -/
def realTensor (a : ι → ℝ) (b : κ → ℝ) : ι × κ → ℂ :=
  fun p => ((a p.1 * b p.2 : ℝ) : ℂ)

/-- Manuscript display 2696: all four exact coefficients of the tensor expansion. -/
theorem tensor_expansion (h : ℝ) (hh : h ≠ 0)
    (a a' : ι → ℝ) (b b' : κ → ℝ) (s t : Bool) :
    (2 * (h : ℂ)) • productState h a a' b b' s t =
      realTensor a b + (Complex.I * (sign t : ℂ)) • realTensor a b' +
      (Complex.I * (sign s : ℂ)) • realTensor a' b -
      ((sign s : ℂ) * (sign t : ℂ)) • realTensor a' b' := by
  ext p
  simp only [Pi.smul_apply, smul_eq_mul, productState, pureTensor, complexFactor,
    realTensor, Pi.add_apply, Pi.sub_apply, Complex.ofReal_mul]
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  field_simp
  ring_nf
  simp
  ring

/-- Unscaled four-sign cancellation, valid in every coordinate dimension. -/
theorem four_sign_cancellation_unscaled (a a' : ι → ℝ) (b b' : κ → ℝ) :
    (∑ s : Bool, ∑ t : Bool,
      projector (pureTensor (complexFactor a a' s) (complexFactor b b' t))) =
      (4 : ℂ) • (projector (realTensor a b) + projector (realTensor a b') +
        projector (realTensor a' b) + projector (realTensor a' b')) := by
  ext p q
  simp [projector, pureTensor, complexFactor, realTensor, sign, star_add,
    star_mul, Complex.star_def, Complex.conj_ofReal]
  ring_nf
  simp
  ring

/-- Manuscript display 2704: exact sum of the four Hermitian projectors. -/
theorem four_sign_projector_sum (h : ℝ) (hh : h ≠ 0)
    (a a' : ι → ℝ) (b b' : κ → ℝ) :
    (∑ s : Bool, ∑ t : Bool, projector (productState h a a' b b' s t)) =
      (h ^ 2)⁻¹ • (projector (realTensor a b) + projector (realTensor a b') +
        projector (realTensor a' b) + projector (realTensor a' b')) := by
  ext p q
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  simp [projector, productState, pureTensor, complexFactor, realTensor, sign,
    Complex.real_smul]
  field_simp
  ring_nf
  simp
  ring

/-- Every complex rank-one projector is positive semidefinite. -/
theorem projector_posSemidef [Fintype ι] (v : ι → ℂ) : (projector v).PosSemidef := by
  change (Matrix.vecMulVec v (star v)).PosSemidef
  exact Matrix.posSemidef_vecMulVec_self_star v

/-- Manuscript display 2709, in the genuine Hermitian PSD order. -/
theorem real_projector_le_four_sign_sum [Fintype ι] [Fintype κ]
    (h : ℝ) (hh : 0 < h) (a a' : ι → ℝ) (b b' : κ → ℝ) :
    projector (realTensor a b) ≤
      h ^ 2 • (∑ s : Bool, ∑ t : Bool, projector (productState h a a' b b' s t)) := by
  rw [four_sign_projector_sum h (ne_of_gt hh), smul_smul, mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hh)), one_smul]
  calc
    _ ≤ projector (realTensor a b) + (projector (realTensor a b') +
        projector (realTensor a' b) + projector (realTensor a' b')) :=
      le_add_of_nonneg_right (add_nonneg
        (add_nonneg (projector_posSemidef _).nonneg (projector_posSemidef _).nonneg)
        (projector_posSemidef _).nonneg)
    _ = _ := by abel

/-- Explicit complex Euclidean operator; its norm is never the entrywise norm. -/
def cMatrixCLM [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A

theorem cMatrixCLM_norm [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ‖cMatrixCLM A‖ = ‖A‖ := Matrix.l2_opNorm_toEuclideanCLM A

/-- The actual covariance for one fixed sign pair. -/
def complexCov (n h : ℕ) (a a' b b' : Fin n → Fin h → ℝ) (s t : Bool) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℂ :=
  ∑ i, projector (productState (h : ℝ) (a i) (a' i) (b i) (b' i) s t)

theorem complexCov_posSemidef (n h : ℕ) (a a' b b' : Fin n → Fin h → ℝ)
    (s t : Bool) : (complexCov n h a a' b b' s t).PosSemidef := by
  exact Matrix.posSemidef_sum _ (fun i _ => projector_posSemidef _)

end AHHAlgebraBridges
