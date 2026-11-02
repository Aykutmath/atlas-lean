import UCFrameAlignment
import UCMatrixRotation
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Exact frame, support and rank transport under the source project's orthogonal conjugation. -/
noncomputable section
set_option maxHeartbeats 800000
open GaussianEllipsoid
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.UCFrameGeometry

/-- The actual column operator of an orthonormal frame, bundled as an isometry. -/
def frameLinearIsometry {d j : ℕ} (U : FrobeniusMatrix d j) (hU : IsFrame U) :
    Euclid j →ₗᵢ[ℝ] Euclid d :=
  (frobeniusOperator U).toLinearMap.isometryOfOrthonormal
    (v := (EuclideanSpace.basisFun (Fin j) ℝ).toBasis)
    (EuclideanSpace.basisFun (Fin j) ℝ).orthonormal
    (by
      change Orthonormal ℝ (fun i => frobeniusOperator U (EuclideanSpace.basisFun (Fin j) ℝ i))
      simpa only [frobeniusOperator_basis] using hU)

@[simp] theorem frameLinearIsometry_basis {d j : ℕ}
    (U : FrobeniusMatrix d j) (hU : IsFrame U) (i : Fin j) :
    frameLinearIsometry U hU (EuclideanSpace.basisFun (Fin j) ℝ i) = U i :=
  frobeniusOperator_basis U i

@[simp] theorem frameLinearIsometry_toContinuousLinearMap {d j : ℕ}
    (U : FrobeniusMatrix d j) (hU : IsFrame U) :
    (frameLinearIsometry U hU).toContinuousLinearMap = frobeniusOperator U := by
  ext x
  rfl

/-- Exact range, including the empty-frame case. -/
theorem frameLinearIsometry_range {d j : ℕ}
    (U : FrobeniusMatrix d j) (hU : IsFrame U) :
    LinearMap.range (frameLinearIsometry U hU).toLinearMap =
      Submodule.span ℝ (Set.range fun i => U i) := by
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    change frameLinearIsometry U hU y ∈ _
    rw [← (EuclideanSpace.basisFun (Fin j) ℝ).sum_repr y, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul,frameLinearIsometry_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact ⟨EuclideanSpace.basisFun (Fin j) ℝ i,frameLinearIsometry_basis U hU i⟩

/-- Every pre-existing Euclidean frame isometry gives a genuine orthonormal
column matrix, allowing the conditioning frame API to use the finite net. -/
theorem linearIsometry_columns_isFrame {d j : ℕ} (F : Euclid j →ₗᵢ[ℝ] Euclid d) :
    IsFrame (operatorFrobenius F.toContinuousLinearMap) :=
  (EuclideanSpace.basisFun (Fin j) ℝ).orthonormal.comp_linearIsometry F

@[simp] theorem frameLinearIsometry_columns {d j : ℕ} (F : Euclid j →ₗᵢ[ℝ] Euclid d) :
    frameLinearIsometry (operatorFrobenius F.toContinuousLinearMap)
      (linearIsometry_columns_isFrame F) = F := by
  apply LinearIsometry.ext
  intro x
  have h := frameLinearIsometry_toContinuousLinearMap
    (operatorFrobenius F.toContinuousLinearMap) (linearIsometry_columns_isFrame F)
  rw [frobeniusOperator_operatorFrobenius] at h
  exact congrArg (fun T : Euclid j →L[ℝ] Euclid d => T x) h

/-- Pointwise column alignment is exactly alignment of the whole isometric
embedding, not merely agreement on selected coefficient vectors. -/
theorem alignment_frameLinearIsometry {d j : ℕ} {U V : FrobeniusMatrix d j}
    (hU : IsFrame U) (hV : IsFrame V) (O : Euclid d ≃ₗᵢ[ℝ] Euclid d)
    (hO : ∀ i, O (U i) = V i) (x : Euclid j) :
    O (frameLinearIsometry U hU x) = frameLinearIsometry V hV x := by
  have he : (isoCLM O).comp (frameLinearIsometry U hU).toContinuousLinearMap =
      (frameLinearIsometry V hV).toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin j) ℝ).toBasis.ext
    intro i
    change O (frameLinearIsometry U hU (EuclideanSpace.basisFun (Fin j) ℝ i)) =
      frameLinearIsometry V hV (EuclideanSpace.basisFun (Fin j) ℝ i)
    rw [frameLinearIsometry_basis,frameLinearIsometry_basis]
    exact hO i
  exact congrArg (fun T : Euclid j →L[ℝ] Euclid d => T x) he

/-- The coordinate matrix rank equals the true Euclidean operator range dimension. -/
theorem matrix_rank_eq_finrank_range {d : ℕ} (A : Square d) :
    A.rank = Module.finrank ℝ
      (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap) := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.rank_eq_finrank_range_toLin A
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis

theorem head_dimension_le_of_rank_le {d K : ℕ} (H : Square d) (hH : H.rank ≤ K) :
    Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) H).toLinearMap) ≤ K := by
  rw [← matrix_rank_eq_finrank_range H]
  exact hH

open UCMatrixRotation

@[simp] theorem conjugate_operator_apply {d : ℕ}
    (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) (A : Square d) (x : Euclid d) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O A)) x =
      O ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) (O.symm x)) := by
  rw [toEuclideanCLM_conjugate]
  rfl

theorem conjugate_rank_le {d : ℕ} (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) (A : Square d) :
    (conjugate O A).rank ≤ A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

@[simp] theorem conjugate_rank {d : ℕ} (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) (A : Square d) :
    (conjugate O A).rank = A.rank := by
  have h := conjugate_rank_le O.symm (conjugate O A)
  rw [conjugate_inverse] at h
  exact le_antisymm (conjugate_rank_le O A) h

/-- General exact range transport under conjugation. -/
theorem conjugate_operator_range {d : ℕ}
    (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) (A : Square d) :
    LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O A)).toLinearMap =
      Submodule.map O.toLinearEquiv.toLinearMap
        (LinearMap.range (Matrix.toEuclideanCLM (𝕜 := ℝ) A).toLinearMap) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨(Matrix.toEuclideanCLM (𝕜 := ℝ) A) (O.symm y),⟨O.symm y,rfl⟩,?_⟩
    exact (conjugate_operator_apply O A y).symm
  · rintro ⟨z,⟨y,rfl⟩,rfl⟩
    refine ⟨O y,?_⟩
    simp only [ContinuousLinearMap.coe_coe, conjugate_operator_apply,O.symm_apply_apply]
    rfl

/-- A head supported in one frame is supported in the exactly aligned frame. -/
theorem conjugate_supported_on_frame {d j : ℕ}
    (F G : Euclid j →ₗᵢ[ℝ] Euclid d) (O : Euclid d ≃ₗᵢ[ℝ] Euclid d)
    (hO : ∀ x, O (F x) = G x) (A : Square d)
    (hA : ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) A) x ∈ LinearMap.range F.toLinearMap) :
    ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O A)) x ∈ LinearMap.range G.toLinearMap := by
  intro x
  obtain ⟨z,hz⟩ := hA (O.symm x)
  refine ⟨z,?_⟩
  rw [conjugate_operator_apply]
  change G z = O ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) (O.symm x))
  rw [← hO z]
  exact congrArg O hz

/-- Annihilation of the head frame is preserved exactly. -/
theorem conjugate_annihilates_frame {d j : ℕ}
    (F G : Euclid j →ₗᵢ[ℝ] Euclid d) (O : Euclid d ≃ₗᵢ[ℝ] Euclid d)
    (hO : ∀ x, O (F x) = G x) (A : Square d)
    (hA : ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (F x) = 0) :
    ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O A)) (G x) = 0 := by
  intro x
  rw [conjugate_operator_apply,← hO x,O.symm_apply_apply,hA,map_zero]

/-- A diffuse tail supported in the head's orthogonal complement remains so
in the aligned deterministic frame. No PSD hypothesis is needed for transport. -/
theorem conjugate_supported_on_frame_orthogonal {d j : ℕ}
    (F G : Euclid j →ₗᵢ[ℝ] Euclid d) (O : Euclid d ≃ₗᵢ[ℝ] Euclid d)
    (hO : ∀ x, O (F x) = G x) (A : Square d)
    (hA : ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) A) x ∈ (LinearMap.range F.toLinearMap)ᗮ) :
    ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O A)) x ∈
      (LinearMap.range G.toLinearMap)ᗮ := by
  intro x
  apply (Submodule.mem_orthogonal _ _).mpr
  intro z hz
  obtain ⟨y,rfl⟩ := hz
  rw [conjugate_operator_apply]
  change ⟪G y,O ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) (O.symm x))⟫_ℝ = 0
  rw [← hO y,O.inner_map_map]
  exact (Submodule.mem_orthogonal _ _).mp (hA (O.symm x)) (F y) ⟨y,rfl⟩

/-- Ready-to-use simultaneous transport of a peeled PSD head and orthogonal
diffuse tail to an aligned net frame. Ranks and zero composition are exact. -/
theorem aligned_conjugate_head_tail {d j : ℕ} {U V : FrobeniusMatrix d j}
    (hU : IsFrame U) (hV : IsFrame V) (O : Euclid d ≃ₗᵢ[ℝ] Euclid d)
    (hO : ∀ i, O (U i) = V i) (H D : Square d)
    (hH : H.PosSemidef) (hD : D.PosSemidef) (hHD : H*D=0)
    (hHead : ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) H) x ∈
      LinearMap.range (frameLinearIsometry U hU).toLinearMap)
    (hTail : ∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) D) x ∈
      (LinearMap.range (frameLinearIsometry U hU).toLinearMap)ᗮ) :
    (conjugate O H).PosSemidef ∧ (conjugate O D).PosSemidef ∧
      conjugate O H*conjugate O D=0 ∧
      (conjugate O H).rank=H.rank ∧ (conjugate O D).rank=D.rank ∧
      (∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O H)) x ∈
        LinearMap.range (frameLinearIsometry V hV).toLinearMap) ∧
      (∀ x, (Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O D)) x ∈
        (LinearMap.range (frameLinearIsometry V hV).toLinearMap)ᗮ) := by
  have hFG := alignment_frameLinearIsometry hU hV O hO
  exact ⟨conjugate_posSemidef O hH,conjugate_posSemidef O hD,
    conjugate_zero_product O hHD,conjugate_rank O H,conjugate_rank O D,
    conjugate_supported_on_frame _ _ O hFG H hHead,
    conjugate_supported_on_frame_orthogonal _ _ O hFG D hTail⟩

end GaussianEllipsoid.UCFrameGeometry
