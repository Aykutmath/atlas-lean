import UCFrameConjugation
import UCHeadCompression

/-! Canonical source-matrix head frames and exact support transport into a deterministic frame net. -/
noncomputable section
set_option maxHeartbeats 800000
open GaussianEllipsoid BMGeometry UCEscape
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.UCFrameGeometry

/-- The compression API's source operator is exactly the coordinate Euclidean operator. -/
theorem sourceOperator_eq_toEuclideanCLM {d : ℕ} (A : Square d) :
    sourceOperator A = Matrix.toEuclideanCLM (𝕜 := ℝ) A := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have h := opMatrix_toEuclideanLin (sourceOperator A)
  rw [opMatrix_sourceFrobenius] at h
  exact h.symm

/-- The canonical orthonormal columns of the actual range of a source head. -/
def headFrameColumns {d : ℕ} (H : Square d) :
    FrobeniusMatrix d (Module.finrank ℝ (headSpace H)) :=
  operatorFrobenius (subspaceOrthonormalFrame (headSpace H)).toContinuousLinearMap

theorem headFrameColumns_isFrame {d : ℕ} (H : Square d) : IsFrame (headFrameColumns H) :=
  linearIsometry_columns_isFrame (subspaceOrthonormalFrame (headSpace H))

@[simp] theorem headFrameColumns_isometry {d : ℕ} (H : Square d) :
    frameLinearIsometry (headFrameColumns H) (headFrameColumns_isFrame H) =
      subspaceOrthonormalFrame (headSpace H) :=
  frameLinearIsometry_columns (subspaceOrthonormalFrame (headSpace H))

@[simp] theorem headFrameColumns_range {d : ℕ} (H : Square d) :
    LinearMap.range (frameLinearIsometry (headFrameColumns H)
      (headFrameColumns_isFrame H)).toLinearMap = headSpace H := by
  rw [headFrameColumns_isometry, subspaceOrthonormalFrame_range]

theorem headFrameColumns_span {d : ℕ} (H : Square d) :
    Submodule.span ℝ (Set.range fun i => headFrameColumns H i) = headSpace H := by
  rw [← frameLinearIsometry_range _ (headFrameColumns_isFrame H), headFrameColumns_range]

theorem source_head_frame_dimension_le {d K : ℕ} (H : Square d) (hK : H.rank ≤ K) :
    Module.finrank ℝ (headSpace H) ≤ K := by
  rwa [headSpace_finrank]

theorem source_head_supported {d : ℕ} (H : Square d) :
    ∀ x, sourceOperator H x ∈ LinearMap.range (frameLinearIsometry (headFrameColumns H)
      (headFrameColumns_isFrame H)).toLinearMap := by
  intro x
  rw [headFrameColumns_range]
  exact ⟨x,rfl⟩

theorem source_tail_supported_head_orthogonal {d : ℕ} (H D : Square d)
    (hH : H.PosSemidef) (hHD : H*D=0) :
    ∀ x, sourceOperator D x ∈ (LinearMap.range (frameLinearIsometry (headFrameColumns H)
      (headFrameColumns_isFrame H)).toLinearMap)ᗮ := by
  intro x
  rw [headFrameColumns_range]
  simpa only [tailFrame, subspaceOrthonormalFrame_range] using source_tail_supported H D hH hHD x

/-- Exactly the two support conditions consumed by the fixed-frame bad event.
The frame is canonical for the source head; no geometric hypothesis is added. -/
theorem aligned_source_head_tail_support {d : ℕ} (H D : Square d)
    (hH : H.PosSemidef) (hHD : H*D=0)
    (V : FrobeniusMatrix d (Module.finrank ℝ (headSpace H))) (hV : IsFrame V)
    (O : Euclid d ≃ₗᵢ[ℝ] Euclid d)
    (hO : ∀ i, O (headFrameColumns H i) = V i) :
    (∀ x, sourceOperator (UCMatrixRotation.conjugate O H) x ∈
      LinearMap.range (frameLinearIsometry V hV).toLinearMap) ∧
    (∀ x, sourceOperator (UCMatrixRotation.conjugate O D) x ∈
      (LinearMap.range (frameLinearIsometry V hV).toLinearMap)ᗮ) := by
  have hF := alignment_frameLinearIsometry (headFrameColumns_isFrame H) hV O hO
  constructor
  · have h := conjugate_supported_on_frame _ _ O hF H (by
      simpa only [← sourceOperator_eq_toEuclideanCLM] using source_head_supported H)
    simpa only [← sourceOperator_eq_toEuclideanCLM] using h
  · have h := conjugate_supported_on_frame_orthogonal _ _ O hF D (by
      simpa only [← sourceOperator_eq_toEuclideanCLM] using
        source_tail_supported_head_orthogonal H D hH hHD)
    simpa only [← sourceOperator_eq_toEuclideanCLM] using h

end GaussianEllipsoid.UCFrameGeometry
