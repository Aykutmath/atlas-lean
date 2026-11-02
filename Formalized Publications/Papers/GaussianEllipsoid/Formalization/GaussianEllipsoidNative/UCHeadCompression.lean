import UCCompressionObservables
import UCOrthogonalBlockFrames

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
namespace UCEscape

lemma opMatrix_injective {d : ℕ} : Function.Injective (@opMatrix d) := by
  intro T U h
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun A : GaussianEllipsoid.Square d => Matrix.toEuclideanLin A x) h
  simpa only [opMatrix_toEuclideanLin, ContinuousLinearMap.coe_coe] using he

lemma orthogonal_range_of_comp_zero {d : ℕ} (H D : Op d)
    (hH : IsPSD H) (hzero : H.comp D = 0) (x : Euclid d) :
    D x ∈ (LinearMap.range H.toLinearMap)ᗮ := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  obtain ⟨z,rfl⟩ := hy
  have hh := hH.1 z (D x)
  have hz := congrArg (fun T : Op d => T x) hzero
  change H (D x) = 0 at hz
  change ⟪H z,D x⟫_ℝ = 0
  change ⟪H z,D x⟫_ℝ = ⟪z,H (D x)⟫_ℝ at hh
  simpa only [hz, inner_zero_right] using hh

abbrev sourceOperator {d : ℕ} (A : GaussianEllipsoid.Square d) : Op d :=
  frobeniusOperator (sourceFrobenius A)

def headSpace {d : ℕ} (H : GaussianEllipsoid.Square d) : Submodule ℝ (Euclid d) :=
  LinearMap.range (sourceOperator H).toLinearMap

def tailFrame {d : ℕ} (H : GaussianEllipsoid.Square d) :
    Euclid (Module.finrank ℝ (headSpace H)ᗮ) →ₗᵢ[ℝ] Euclid d :=
  subspaceOrthonormalFrame (headSpace H)ᗮ

def tailCompressed {d : ℕ} (H D : GaussianEllipsoid.Square d) :
    GaussianEllipsoid.Square (Module.finrank ℝ (headSpace H)ᗮ) :=
  opMatrix (compress (tailFrame H) (sourceOperator D))

lemma headSpace_finrank {d : ℕ} (H : GaussianEllipsoid.Square d) :
    Module.finrank ℝ (headSpace H) = H.rank := by
  symm
  calc
    H.rank = (opMatrix (sourceOperator H)).rank := by rw [opMatrix_sourceFrobenius]
    _ = _ := by
      rw [opMatrix_eq_toMatrix, Matrix.rank_eq_finrank_range_toLin _
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin d) ℝ).toBasis, Matrix.toLin_toMatrix]
      rfl

lemma tailFrame_dimension {d : ℕ} (H : GaussianEllipsoid.Square d) :
    H.rank + Module.finrank ℝ (headSpace H)ᗮ = d := by
  rw [← headSpace_finrank]
  exact subspaceFrames_dimensions (headSpace H)

lemma source_tail_supported {d : ℕ} (H D : GaussianEllipsoid.Square d)
    (hH : H.PosSemidef) (hzero : H*D=0) :
    ∀ x, sourceOperator D x ∈ LinearMap.range (tailFrame H).toLinearMap := by
  have hc : (sourceOperator H).comp (sourceOperator D) = 0 := by
    apply opMatrix_injective
    rw [opMatrix_comp, opMatrix_sourceFrobenius, opMatrix_sourceFrobenius, hzero, opMatrix_zero]
  intro x
  rw [tailFrame, subspaceOrthonormalFrame_range]
  exact orthogonal_range_of_comp_zero _ _ ((sourceFrobenius_psd H).mpr hH) hc x

/-- Exact dimensional compression of a supported diffuse tail into the source
project's p-dimensional matrix model, where p=d−rank(head). -/
theorem tailCompressed_constraints {d : ℕ} (H D : GaussianEllipsoid.Square d)
    (hH : H.PosSemidef) (hD : D.PosSemidef) (hzero : H*D=0) :
    (tailCompressed H D).PosSemidef ∧
      frobeniusNorm (tailCompressed H D) = frobeniusNorm D ∧
      matrixOpNorm (tailCompressed H D) ≤ matrixOpNorm D := by
  have hp : IsPSD (sourceOperator D) := (sourceFrobenius_psd D).mpr hD
  have hs := source_tail_supported H D hH hzero
  refine ⟨(opMatrix_posSemidef_iff _).mpr (compress_psd _ _ hp), ?_, ?_⟩
  · rw [tailCompressed, frobeniusNorm_opMatrix, compress_frobenius_norm _ _ hp hs,
      operatorFrobenius_frobeniusOperator, sourceFrobenius_norm]
  · rw [tailCompressed, matrixOpNorm_opMatrix]
    have h := compress_opNorm_le (tailFrame H) (sourceOperator D)
    rwa [← matrixOpNorm_opMatrix (sourceOperator D), opMatrix_sourceFrobenius] at h

/-- No error or scale loss occurs in the centered quadratic observations. -/
theorem tailCompressed_measurement_row {d : ℕ} (H D : GaussianEllipsoid.Square d)
    (hH : H.PosSemidef) (hD : D.PosSemidef) (hzero : H*D=0) (x : Euclid d) :
    (quadratic D (fun i => x i)-Matrix.trace D)/Real.sqrt 2 =
      (quadratic (tailCompressed H D) (fun i => (tailFrame H).toContinuousLinearMap.adjoint x i)-
        Matrix.trace (tailCompressed H D))/Real.sqrt 2 := by
  have h := compressed_measurement_row (tailFrame H) (sourceOperator D)
    ((sourceFrobenius_psd D).mpr hD) (source_tail_supported H D hH hzero) x
  simpa only [opMatrix_sourceFrobenius, tailCompressed] using h

#print axioms headSpace_finrank
#print axioms tailCompressed_constraints
#print axioms tailCompressed_measurement_row
end UCEscape
