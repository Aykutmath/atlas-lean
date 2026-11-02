import GaussianSelectedSigmaField
import Mathlib.Data.Finset.Sort

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open scoped Classical
open MeasureTheory ProbabilityTheory
open GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.ProjectedClusters

/-- Increasing enumeration of every sample index outside the selected support. -/
def outsideSampleEmbedding {N s : ℕ} (e : Fin s ↪ Fin N) :
    Fin (Finset.univ.filter (fun i : Fin N => i ∉ Set.range e)).card ↪ Fin N :=
  ((Finset.univ.filter (fun i : Fin N => i ∉ Set.range e)).orderEmbOfFin rfl).toEmbedding

theorem outsideSampleEmbedding_range {N s : ℕ} (e : Fin s ↪ Fin N) :
    Set.range (outsideSampleEmbedding e) = (Set.range e)ᶜ := by
  ext i
  simp [outsideSampleEmbedding, Finset.range_orderEmbOfFin]

/-- The exact sigma-field of all outside rows of both Gaussian factors. -/
def outsideSampleSigmaField {N s h : ℕ} (e : Fin s ↪ Fin N) :
    MeasurableSpace (GaussianEntries N h × GaussianEntries N h) :=
  selectedSampleSigmaField (outsideSampleEmbedding e)

theorem outsideSampleSigmaField_le {N s h : ℕ} (e : Fin s ↪ Fin N) :
    outsideSampleSigmaField (h := h) e ≤ (inferInstance : MeasurableSpace (GaussianEntries N h × GaussianEntries N h)) :=
  selectedSampleSigmaField_le (outsideSampleEmbedding e)

theorem outsideSampleSigmaField_indep {N s h : ℕ} (e : Fin s ↪ Fin N) :
    Indep (outsideSampleSigmaField (h := h) e)
      (MeasurableSpace.comap (selectSample (h := h) e) inferInstance)
      (tensorGaussianLaw N h) := by
  apply selectedSampleSigmaField_indep
  intro i j hij
  have hi : outsideSampleEmbedding e i ∈ Set.range (outsideSampleEmbedding e) := ⟨i, rfl⟩
  rw [outsideSampleEmbedding_range] at hi
  exact hi ⟨j, hij.symm⟩

end GaussianEllipsoid.ProjectedClusters

#print axioms GaussianEllipsoid.ProjectedClusters.outsideSampleSigmaField_indep
