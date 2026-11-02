import CoordinateBlockPinching

noncomputable section
open Module
namespace GaussianEllipsoid

/-- A Euclidean coordinate isometry into any subspace with sufficient dimension. -/
def subspaceEmbeddingIsometry {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) : Euclid k →ₗᵢ[ℝ] Euclid h :=
  W.subtypeₗᵢ.comp ((stdOrthonormalBasis ℝ W).repr.symm.toLinearIsometry.comp
    (coordinateEmbeddingLinearIsometry (Fin.castLEEmb hk)))

/-- The corresponding genuine Euclidean operator. -/
def subspaceEmbedding {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) : Euclid k →L[ℝ] Euclid h :=
  (subspaceEmbeddingIsometry W hk).toContinuousLinearMap

@[simp] theorem subspaceEmbedding_norm {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) (x : Euclid k) : ‖subspaceEmbedding W hk x‖ = ‖x‖ :=
  (subspaceEmbeddingIsometry W hk).norm_map x

theorem subspaceEmbedding_norm_le_one {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) : ‖subspaceEmbedding W hk‖ ≤ 1 :=
  (subspaceEmbeddingIsometry W hk).norm_toContinuousLinearMap_le

theorem subspaceEmbedding_adjoint_comp {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) :
    ContinuousLinearMap.adjoint (subspaceEmbedding W hk) ∘L subspaceEmbedding W hk =
      ContinuousLinearMap.id ℝ _ :=
  (subspaceEmbedding W hk).norm_map_iff_adjoint_comp_self.mp (subspaceEmbedding_norm W hk)

theorem subspaceEmbedding_mem {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) (x : Euclid k) : subspaceEmbedding W hk x ∈ W := by
  exact ((stdOrthonormalBasis ℝ W).repr.symm
    (coordinateEmbeddingLinearIsometry (Fin.castLEEmb hk) x)).property

/-- Projecting onto the containing subspace fixes the embedded coordinates. -/
theorem subspaceProjector_comp_embedding {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) :
    (W.subtypeL ∘L W.orthogonalProjection) ∘L subspaceEmbedding W hk =
      subspaceEmbedding W hk := by
  apply ContinuousLinearMap.ext
  intro x
  exact congrArg (fun v : W => (v : Euclid h))
    (W.orthogonalProjection_mem_subspace_eq_self
      ⟨subspaceEmbedding W hk x, subspaceEmbedding_mem W hk x⟩)

/-- Taking small coordinates after the ambient projection is the same as taking
those coordinates directly. This is the fixed-projection Gaussian law bridge. -/
theorem subspaceEmbedding_adjoint_comp_projector {h k : ℕ}
    (W : Submodule ℝ (Euclid h)) (hk : k ≤ finrank ℝ W) :
    ContinuousLinearMap.adjoint (subspaceEmbedding W hk) ∘L
      (W.subtypeL ∘L W.orthogonalProjection) =
        ContinuousLinearMap.adjoint (subspaceEmbedding W hk) := by
  have he := congrArg ContinuousLinearMap.adjoint (subspaceProjector_comp_embedding W hk)
  change ContinuousLinearMap.adjoint (W.starProjection ∘L subspaceEmbedding W hk) =
    ContinuousLinearMap.adjoint (subspaceEmbedding W hk) at he
  rw [ContinuousLinearMap.adjoint_comp, (isSelfAdjoint_starProjection W).adjoint_eq] at he
  exact he

/-- Any sufficiently large subspace contains isometric Euclidean coordinates,
with both useful projection identities stated explicitly. -/
theorem exists_subspaceEmbedding {h k : ℕ} (W : Submodule ℝ (Euclid h))
    (hk : k ≤ finrank ℝ W) :
    ∃ U : Euclid k →L[ℝ] Euclid h, ‖U‖ ≤ 1 ∧
      ContinuousLinearMap.adjoint U ∘L U = ContinuousLinearMap.id ℝ _ ∧
      (∀ x, U x ∈ W) ∧
      (W.subtypeL ∘L W.orthogonalProjection) ∘L U = U ∧
      ContinuousLinearMap.adjoint U ∘L (W.subtypeL ∘L W.orthogonalProjection) =
        ContinuousLinearMap.adjoint U :=
  ⟨subspaceEmbedding W hk, subspaceEmbedding_norm_le_one W hk,
    subspaceEmbedding_adjoint_comp W hk, subspaceEmbedding_mem W hk,
    subspaceProjector_comp_embedding W hk, subspaceEmbedding_adjoint_comp_projector W hk⟩

end GaussianEllipsoid
#print axioms GaussianEllipsoid.exists_subspaceEmbedding
