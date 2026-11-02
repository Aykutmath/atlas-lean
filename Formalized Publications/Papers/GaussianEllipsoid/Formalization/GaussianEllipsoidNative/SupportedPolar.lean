import NuclearCompression
import Mathlib.LinearAlgebra.Trace

noncomputable section
open Set Module
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid

/-- The coordinate trace is the sum of diagonal orthonormal pairings. -/
theorem trace_eq_sum_inner_basis {q : ℕ} (E : Euclid q →L[ℝ] Euclid q)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) :
    LinearMap.trace ℝ (Euclid q) E.toLinearMap = ∑ j, ⟪b j, E (b j)⟫_ℝ := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply]
  rfl

/-- A self-adjoint idempotent is automatically an operator contraction. -/
theorem norm_projection_le_one {q : ℕ} (E : Euclid q →L[ℝ] Euclid q)
    (hSelf : ContinuousLinearMap.adjoint E = E) (hIdem : E ∘L E = E) : ‖E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  have hsq : ‖E x‖ ^ 2 = ⟪x, E x⟫_ℝ := by
    have h := ContinuousLinearMap.adjoint_inner_right E x (E x)
    rw [hSelf, real_inner_self_eq_norm_sq] at h
    have hx := congrArg (fun L : Euclid q →L[ℝ] Euclid q => L x) hIdem
    change E (E x) = E x at hx
    rw [hx] at h
    exact h.symm
  have hi := real_inner_le_norm x (E x)
  have hn := norm_nonneg (E x)
  have hnx := norm_nonneg x
  nlinarith

/-- Squared Frobenius norm of a genuine orthogonal projection is its rank. -/
theorem frobenius_projection_sq_eq_rank {q : ℕ} (E : Euclid q →L[ℝ] Euclid q)
    (hSelf : ContinuousLinearMap.adjoint E = E) (hIdem : E ∘L E = E) :
    ‖operatorFrobenius E‖ ^ 2 = (finrank ℝ (LinearMap.range E.toLinearMap) : ℝ) := by
  have hproj : LinearMap.IsProj (LinearMap.range E.toLinearMap) E.toLinearMap := by
    constructor
    · intro x; exact LinearMap.mem_range_self _ x
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact congrArg (fun L : Euclid q →L[ℝ] Euclid q => L y) hIdem
  rw [← hproj.trace, trace_eq_sum_inner_basis E (EuclideanSpace.basisFun (Fin q) ℝ),
    ← sum_norm_sq_operator_basis E (EuclideanSpace.basisFun (Fin q) ℝ)]
  apply Finset.sum_congr rfl
  intro j _
  have h := ContinuousLinearMap.adjoint_inner_right E
    (EuclideanSpace.basisFun (Fin q) ℝ j) (E (EuclideanSpace.basisFun (Fin q) ℝ j))
  rw [hSelf, real_inner_self_eq_norm_sq] at h
  have hx := congrArg (fun L : Euclid q →L[ℝ] Euclid q =>
    L (EuclideanSpace.basisFun (Fin q) ℝ j)) hIdem
  change E (E _) = E _ at hx
  rw [hx] at h
  exact h.symm

/-- A contraction supported on a right rank-k orthogonal projection has
Frobenius energy at most k. -/
theorem frobenius_supported_contraction_sq_le_rank {r q : ℕ}
    (W : Euclid q →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q)
    (hW : ‖W‖ ≤ 1) (hSelf : ContinuousLinearMap.adjoint E = E)
    (hIdem : E ∘L E = E) (hSupport : W ∘L E = W) :
    ‖operatorFrobenius W‖ ^ 2 ≤ (finrank ℝ (LinearMap.range E.toLinearMap) : ℝ) := by
  rw [← frobenius_projection_sq_eq_rank E hSelf hIdem]
  apply pow_le_pow_left₀ (norm_nonneg _)
  have heq : operatorFrobenius (W ∘L E) = leftAction W (operatorFrobenius E) := by ext j i; rfl
  calc
    ‖operatorFrobenius W‖ = ‖leftAction W (operatorFrobenius E)‖ := by rw [← heq, hSupport]
    _ ≤ ‖W‖ * ‖operatorFrobenius E‖ := norm_leftAction_le _ _
    _ ≤ ‖operatorFrobenius E‖ := by
      simpa using mul_le_mul_of_nonneg_right hW (norm_nonneg _)

/-- Exact supported polar witnesses for two-sided orthogonal matrix blocks.
The witness is an actual contraction, attains the nuclear norm, and has the
rank-controlled Frobenius energy needed for Gaussian product moments. -/
theorem exists_supported_polar {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (D : Euclid r →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q)
    (hDself : ContinuousLinearMap.adjoint D = D) (hEself : ContinuousLinearMap.adjoint E = E)
    (hDsq : D ∘L D = D) (hEsq : E ∘L E = E) (hT : D ∘L T ∘L E = T) :
    ∃ W : Euclid q →L[ℝ] Euclid r,
      ‖W‖ ≤ 1 ∧ D ∘L W ∘L E = W ∧
      ⟪operatorFrobenius T, operatorFrobenius W⟫_ℝ = spectralNuclearNorm (operatorFrobenius T) ∧
      ‖operatorFrobenius W‖ ^ 2 ≤ (finrank ℝ (LinearMap.range E.toLinearMap) : ℝ) := by
  let W₀ := polarWitness T
  let W := D ∘L W₀ ∘L E
  have hDn := norm_projection_le_one D hDself hDsq
  have hEn := norm_projection_le_one E hEself hEsq
  have hW : ‖W‖ ≤ 1 := norm_comp_le_one D _ hDn (norm_comp_le_one W₀ E (norm_polarWitness_le T) hEn)
  have hRight : W ∘L E = W := by
    dsimp [W]
    simp only [ContinuousLinearMap.comp_assoc, hEsq]
  have hLeft : D ∘L W = W := by
    dsimp [W]
    rw [← ContinuousLinearMap.comp_assoc, hDsq]
  have hSupport : D ∘L W ∘L E = W := by rw [← ContinuousLinearMap.comp_assoc, hLeft, hRight]
  refine ⟨W, hW, hSupport, ?_, frobenius_supported_contraction_sq_le_rank W E hW hEself hEsq hRight⟩
  have hp₀ := inner_operator_comp_left D (T ∘L E) W₀
  rw [hDself] at hp₀
  have hp₁ := inner_operator_comp_right T E (D ∘L W₀)
  rw [hEself] at hp₁
  have hp := hp₀.trans hp₁
  rw [hT] at hp
  have hTarget : (D ∘L W₀) ∘L E = W := by dsimp [W]; rw [ContinuousLinearMap.comp_assoc]
  rw [hTarget] at hp
  rw [← hp]
  simpa only [frobeniusOperator_operatorFrobenius] using
    inner_polarWitness_eq_nuclear (operatorFrobenius T)

end GaussianEllipsoid
#print axioms GaussianEllipsoid.frobenius_projection_sq_eq_rank
#print axioms GaussianEllipsoid.exists_supported_polar
