/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Native verification pending. -/
import ActualMultiscaleUniform
import ActualUniformExtension
import GaussianCoisometry
import NuclearCompression
import SubspaceCoordinateEmbedding

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoidCandidate

def compressCanonicalRows {n h k : ℕ} (U : Euclid h →L[ℝ] Euclid k)
    (X : Fin n → Euclid h × Euclid h) : Fin n → Euclid k × Euclid k :=
  fun i => (U (X i).1, U (X i).2)

theorem compressCanonicalRows_preserving {n h k : ℕ} (U : Euclid h →L[ℝ] Euclid k)
    (hU : U ∘L ContinuousLinearMap.adjoint U = ContinuousLinearMap.id ℝ _) :
    MeasurePreserving (compressCanonicalRows (n:=n) U)
      (gaussianBilinearSampleLaw (Fin n) h h) (gaussianBilinearSampleLaw (Fin n) k k) := by
  have hrow : MeasurePreserving U (euclideanGaussianLaw (Fin h))
      (euclideanGaussianLaw (Fin k)) :=
    ⟨U.continuous.measurable, GaussianEllipsoid.SmallBall.euclideanGaussianLaw_map_coisometry U hU⟩
  exact measurePreserving_pi _ _ (f := fun _ : Fin n => fun p : Euclid h × Euclid h => (U p.1, U p.2))
    (fun _ => hrow.prod hrow)

theorem bilinearSynthesis_compress {n h k : ℕ} (U : Euclid h →L[ℝ] Euclid k)
    (u : Fin n → ℝ) (X : Fin n → Euclid h × Euclid h) :
    bilinearSynthesis u (compressCanonicalRows U X) =
      U ∘L bilinearSynthesis u X ∘L U.adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [bilinearSynthesis, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul, bilinearRowOperator_apply,
    compressCanonicalRows]
  apply Finset.sum_congr rfl
  intro i _
  rw [← ContinuousLinearMap.adjoint_inner_right U]

theorem scaledBilinearNuclear_compress_le {n h k : ℕ}
    (U : Euclid h →L[ℝ] Euclid k) (hU : ‖U‖ ≤ 1)
    (d : ℕ) (u : Fin n → ℝ) (X : Fin n → Euclid h × Euclid h) :
    scaledBilinearNuclear d u (compressCanonicalRows U X) ≤ scaledBilinearNuclear d u X := by
  have he : (Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u (compressCanonicalRows U X) =
      U ∘L ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X) ∘L U.adjoint := by
    rw [bilinearSynthesis_compress]
    ext x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, map_smul]
  unfold scaledBilinearNuclear
  rw [he]
  exact spectralNuclear_compression_le U _ U.adjoint hU (by simpa using hU)

end GaussianEllipsoidCandidate
