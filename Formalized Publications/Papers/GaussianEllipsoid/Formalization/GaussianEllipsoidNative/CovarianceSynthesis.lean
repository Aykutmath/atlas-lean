import CovarianceSpectralBounds

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace GaussianTensorTrace

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The synthesis operator sends coefficients y to the ordinary column sum. -/
def synthesisCLM (v : α → β → ℝ) : EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ β :=
  matrixCLM (Matrix.of v)ᵀ

@[simp] theorem synthesisCLM_apply (v : α → β → ℝ) (y : EuclideanSpace ℝ α) (r : β) :
    synthesisCLM v y r = ∑ i, y i * v i r := by
  simp [synthesisCLM, matrixCLM, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem covariance_posSemidef (v : α → β → ℝ) : (covariance v).PosSemidef := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  rw [covariance_eq_mul_transpose]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (Matrix.of v)

/-- Exact covariance/operator norm identity, including zero-dimensional spaces. -/
theorem synthesisCLM_norm_sq (v : α → β → ℝ) :
    ‖synthesisCLM v‖^2 = ‖matrixCLM (covariance v)‖ := by
  have ht : ‖(Matrix.of v)ᵀ‖ = ‖Matrix.of v‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.l2_opNorm_conjTranspose (Matrix.of v)
  rw [synthesisCLM, ← matrix_l2_norm_eq, ht, covariance_eq_mul_transpose,
    ← matrix_l2_norm_eq]
  symm
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, pow_two] using
    Matrix.l2_opNorm_conjTranspose_mul_self (Matrix.of v)

/-- The exact normalization used for the bilinear measurement operator. -/
def scaledSynthesisCLM (v : α → β → ℝ) (d : ℝ) :
    EuclideanSpace ℝ α →L[ℝ] EuclideanSpace ℝ β :=
  (Real.sqrt d)⁻¹ • synthesisCLM v

@[simp] theorem scaledSynthesisCLM_apply (v : α → β → ℝ) (d : ℝ)
    (y : EuclideanSpace ℝ α) (r : β) :
    scaledSynthesisCLM v d y r = (Real.sqrt d)⁻¹ * ∑ i, y i * v i r := by
  simp [scaledSynthesisCLM]

theorem scaledSynthesisCLM_norm_sq (v : α → β → ℝ) (d : ℝ) (hd : 0 ≤ d) :
    ‖scaledSynthesisCLM v d‖^2 = ‖matrixCLM (covariance v)‖ / d := by
  rw [scaledSynthesisCLM, norm_smul (Real.sqrt d)⁻¹ (synthesisCLM v), mul_pow, Real.norm_eq_abs, sq_abs,
    inv_pow, Real.sq_sqrt hd, synthesisCLM_norm_sq]
  ring

#print axioms synthesisCLM_apply
#print axioms covariance_posSemidef
#print axioms synthesisCLM_norm_sq
#print axioms scaledSynthesisCLM_apply
#print axioms scaledSynthesisCLM_norm_sq
end GaussianTensorTrace
