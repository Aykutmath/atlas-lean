import UCGaussianBlockConditioning

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace UCEscape

/-- Canonical full orthonormal frame of an actual finite-dimensional subspace. -/
def subspaceOrthonormalFrame {d : ℕ} (E : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  E.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ E).repr.symm.toLinearIsometry

theorem subspaceOrthonormalFrame_mem {d : ℕ} (E : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) : subspaceOrthonormalFrame E x ∈ E :=
  ((stdOrthonormalBasis ℝ E).repr.symm x).prop

theorem subspaceOrthonormalFrame_range {d : ℕ}
    (E : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    (subspaceOrthonormalFrame E).toLinearMap.range = E := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact subspaceOrthonormalFrame_mem E y
  · intro hx
    refine ⟨(stdOrthonormalBasis ℝ E).repr ⟨x, hx⟩, ?_⟩
    simp [subspaceOrthonormalFrame]

theorem subspaceFrames_orthogonal {d : ℕ}
    (E : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ Eᗮ))) :
    ⟪subspaceOrthonormalFrame E x, subspaceOrthonormalFrame Eᗮ y⟫_ℝ = 0 :=
  Submodule.inner_right_of_mem_orthogonal (subspaceOrthonormalFrame_mem E x)
    (subspaceOrthonormalFrame_mem Eᗮ y)

theorem subspaceFrames_dimensions {d : ℕ}
    (E : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Module.finrank ℝ E + Module.finrank ℝ Eᗮ = d := by
  simpa using E.finrank_add_finrank_orthogonal

def leftBlockLinearMap {j p : ℕ} :
    EuclideanSpace ℝ (Fin j ⊕ Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin j) where
  toFun := BMGordon.leftBlock
  map_add' := by intro x y; ext i; rfl
  map_smul' := by intro c x; ext i; rfl

def rightBlockLinearMap {j p : ℕ} :
    EuclideanSpace ℝ (Fin j ⊕ Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p) where
  toFun := BMGordon.rightBlock
  map_add' := by intro x y; ext i; rfl
  map_smul' := by intro c x; ext i; rfl

/-- Add vectors in two orthogonal frames, preserving their joint Euclidean norm. -/
def orthogonalBlockIsometry {d j p : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (V : EuclideanSpace ℝ (Fin p) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hUV : ∀ x y, ⟪U x, V y⟫_ℝ = 0) :
    EuclideanSpace ℝ (Fin j ⊕ Fin p) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (U.toLinearMap.comp leftBlockLinearMap + V.toLinearMap.comp rightBlockLinearMap).isometryOfInner
    (by
      intro x y
      change ⟪U (BMGordon.leftBlock x) + V (BMGordon.rightBlock x),
        U (BMGordon.leftBlock y) + V (BMGordon.rightBlock y)⟫_ℝ = ⟪x, y⟫_ℝ
      have hcross : ⟪V (BMGordon.rightBlock x), U (BMGordon.leftBlock y)⟫_ℝ = 0 := by
        rw [real_inner_comm]; exact hUV _ _
      rw [inner_add_left, inner_add_right, inner_add_right,
        U.inner_map_map, V.inner_map_map, hUV, hcross]
      simp only [add_zero, zero_add, PiLp.inner_apply, Fintype.sum_sum_type,
        BMGordon.leftBlock_apply, BMGordon.rightBlock_apply])

/-- Complementary orthogonal frames give a complete orthogonal coordinate rotation. -/
def orthogonalBlockEquiv {d j p : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (V : EuclideanSpace ℝ (Fin p) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hUV : ∀ x y, ⟪U x, V y⟫_ℝ = 0) (hdim : j + p = d) :
    EuclideanSpace ℝ (Fin j ⊕ Fin p) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometryEquiv.ofSurjective (orthogonalBlockIsometry U V hUV)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hdim)).mp
      (orthogonalBlockIsometry U V hUV).injective)

@[simp] theorem orthogonalBlockEquiv_apply {d j p : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (V : EuclideanSpace ℝ (Fin p) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hUV : ∀ x y, ⟪U x, V y⟫_ℝ = 0) (hdim : j + p = d)
    (z : EuclideanSpace ℝ (Fin j ⊕ Fin p)) :
    orthogonalBlockEquiv U V hUV hdim z = U (BMGordon.leftBlock z) + V (BMGordon.rightBlock z) := rfl

/-- The inverse orthogonal coordinate rotation is exactly the pair of frame adjoints. -/
theorem orthogonalBlockEquiv_inverse_blocks {d j p : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (V : EuclideanSpace ℝ (Fin p) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hUV : ∀ x y, ⟪U x, V y⟫_ℝ = 0) (hdim : j + p = d)
    (w : EuclideanSpace ℝ (Fin d)) :
    BMGordon.splitBlocks ((orthogonalBlockEquiv U V hUV hdim).symm w) =
      (U.toContinuousLinearMap.adjoint w, V.toContinuousLinearMap.adjoint w) := by
  obtain ⟨z, rfl⟩ := (orthogonalBlockEquiv U V hUV hdim).surjective w
  rw [LinearIsometryEquiv.symm_apply_apply, orthogonalBlockEquiv_apply]
  apply Prod.ext
  · change BMGordon.leftBlock z = U.toContinuousLinearMap.adjoint _
    symm
    apply ext_inner_right ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
    change ⟪U (BMGordon.leftBlock z), U x⟫_ℝ + ⟪V (BMGordon.rightBlock z), U x⟫_ℝ = _
    rw [U.inner_map_map]
    have hz : ⟪V (BMGordon.rightBlock z), U x⟫_ℝ = 0 := by
      rw [real_inner_comm]; exact hUV _ _
    rw [hz, add_zero]
  · change BMGordon.rightBlock z = V.toContinuousLinearMap.adjoint _
    symm
    apply ext_inner_right ℝ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
    change ⟪U (BMGordon.leftBlock z), V x⟫_ℝ + ⟪V (BMGordon.rightBlock z), V x⟫_ℝ = _
    rw [hUV, V.inner_map_map, zero_add]

/-- Canonical orthogonal splitting associated to any deterministic head subspace. -/
def subspaceBlockEquiv {d : ℕ} (E : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E) ⊕ Fin (Module.finrank ℝ Eᗮ)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  orthogonalBlockEquiv (subspaceOrthonormalFrame E) (subspaceOrthonormalFrame Eᗮ)
    (subspaceFrames_orthogonal E) (subspaceFrames_dimensions E)

/-- An isometric j-frame has exactly j-dimensional range. -/
theorem frame_range_finrank {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Module.finrank ℝ U.toLinearMap.range = j := by
  simpa using LinearMap.finrank_range_of_inj U.injective

theorem frame_orthogonal_finrank {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Module.finrank ℝ U.toLinearMap.rangeᗮ = d - j := by
  have h := subspaceFrames_dimensions U.toLinearMap.range
  rw [frame_range_finrank U] at h
  omega

/-- Canonical complementary frame, with the natural tail dimension d-j. -/
def frameComplement {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (d - j)) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (subspaceOrthonormalFrame U.toLinearMap.rangeᗮ).comp
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (frame_orthogonal_finrank U).symm)).toLinearIsometry

theorem frameComplement_mem {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin (d - j))) : frameComplement U x ∈ U.toLinearMap.rangeᗮ :=
  subspaceOrthonormalFrame_mem _ _

theorem frameComplement_range {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    (frameComplement U).toLinearMap.range = U.toLinearMap.rangeᗮ := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact frameComplement_mem U y
  · intro hx
    have hr := subspaceOrthonormalFrame_range U.toLinearMap.rangeᗮ
    rw [← hr] at hx
    obtain ⟨y, hy⟩ := hx
    let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finCongr (frame_orthogonal_finrank U).symm)
    refine ⟨e.symm y, ?_⟩
    change subspaceOrthonormalFrame U.toLinearMap.rangeᗮ (e (e.symm y)) = x
    rw [e.apply_symm_apply]
    exact hy

theorem frameComplement_orthogonal {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin j)) (y : EuclideanSpace ℝ (Fin (d - j))) :
    ⟪U x, frameComplement U y⟫_ℝ = 0 :=
  Submodule.inner_right_of_mem_orthogonal
    (show U x ∈ U.toLinearMap.range from ⟨x, rfl⟩) (frameComplement_mem U y)

theorem frame_dimension_le {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : j ≤ d := by
  have h := U.toLinearMap.range.finrank_le
  rw [frame_range_finrank U] at h
  simpa using h

/-- Complete an arbitrary given isometric frame, keeping its exact head coordinates. -/
def frameCompletion {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin j ⊕ Fin (d - j)) :=
  (orthogonalBlockEquiv U (frameComplement U) (frameComplement_orthogonal U)
    (by have h := frame_dimension_le U; omega)).symm

theorem frameCompletion_blocks {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (w : EuclideanSpace ℝ (Fin d)) :
    BMGordon.splitBlocks (frameCompletion U w) =
      (U.toContinuousLinearMap.adjoint w, (frameComplement U).toContinuousLinearMap.adjoint w) :=
  orthogonalBlockEquiv_inverse_blocks _ _ _ _ _

/-- Exact original Gaussian row law under completed-frame head/tail coordinates. -/
theorem frameCompletion_gaussianSample_preserving {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    MeasurePreserving (gaussianSampleBlockSplit (frameCompletion U) n)
      (GaussianEllipsoid.gaussianSampleLaw d n)
      ((GaussianEllipsoid.gaussianSampleLaw j n).prod (GaussianEllipsoid.gaussianSampleLaw (d - j) n)) :=
  gaussianSampleBlockSplit_preserving _ _

/-- Completed sample head rows are literally the given frame-adjoint coordinates. -/
theorem frameCompletion_sample_head {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (z : GaussianEllipsoid.Sample d n) (i : Fin n) :
    (gaussianSampleBlockSplit (frameCompletion U) n z).1 i =
      WithLp.ofLp (U.toContinuousLinearMap.adjoint (WithLp.toLp 2 (z i))) := by
  exact congrArg (fun q : EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (d - j)) =>
    WithLp.ofLp q.1) (frameCompletion_blocks U (WithLp.toLp 2 (z i)))

/-- Completed sample tail rows are literally the complementary frame-adjoint coordinates. -/
theorem frameCompletion_sample_tail {d j : ℕ}
    (U : EuclideanSpace ℝ (Fin j) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (z : GaussianEllipsoid.Sample d n) (i : Fin n) :
    (gaussianSampleBlockSplit (frameCompletion U) n z).2 i =
      WithLp.ofLp ((frameComplement U).toContinuousLinearMap.adjoint (WithLp.toLp 2 (z i))) := by
  exact congrArg (fun q : EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (d - j)) =>
    WithLp.ofLp q.2) (frameCompletion_blocks U (WithLp.toLp 2 (z i)))

#print axioms frameCompletion_sample_tail
#print axioms frameCompletion_blocks
#print axioms frameComplement_range
#print axioms frameCompletion_gaussianSample_preserving
#print axioms subspaceOrthonormalFrame_range
#print axioms orthogonalBlockEquiv_inverse_blocks
#print axioms subspaceBlockEquiv
end UCEscape
