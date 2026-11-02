import GaussianExtractedRowsLaw
import AspectRatioLimit

open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers
open scoped ENNReal Topology
namespace GaussianEllipsoidCandidate

/-- The even half-block used throughout the determinant-moment proof. -/
def evenHalfDim (d : ℕ) : ℕ := 2 * (d / 4)

theorem twice_evenHalfDim_le (d : ℕ) : 2 * evenHalfDim d ≤ d := by
  unfold evenHalfDim
  omega

/-- First half-block coordinates. -/
def evenLeft (d : ℕ) : Fin (evenHalfDim d) ↪ Fin d where
  toFun j := ⟨j.val, by have := twice_evenHalfDim_le d; omega⟩
  inj' := by intro i j hij; exact Fin.ext (congrArg (fun z : Fin d => z.val) hij)

/-- Second half-block coordinates; at most three ambient coordinates are unused. -/
def evenRight (d : ℕ) : Fin (evenHalfDim d) ↪ Fin d where
  toFun j := ⟨evenHalfDim d + j.val, by have := twice_evenHalfDim_le d; omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg (fun z : Fin d => z.val) hij; simp only at this; omega

theorem evenLeft_ne_evenRight (d : ℕ) (i j : Fin (evenHalfDim d)) :
    evenLeft d i ≠ evenRight d j := by
  intro hh
  have := congrArg Fin.val hh
  change i.val = evenHalfDim d + j.val at this
  omega

theorem even_extractedRows_preserving (d n : ℕ) :
    MeasurePreserving (extractedRows (n := n) (evenLeft d) (evenRight d))
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d)))
      (gaussianBilinearSampleLaw (Fin n) (evenHalfDim d) (evenHalfDim d)) :=
  extractedRows_preserving _ _ (evenLeft_ne_evenRight d)

/-- Exact good-event transfer, including the probability of its complement.
The rectangular event and its pointwise bounds are supplied by the proved
bilinear estimates, so this lemma contains no Gaussian comparison assumption. -/
theorem even_good_event_transfer (d n : ℕ)
    (E : Set (Fin n → Euclid (evenHalfDim d) × Euclid (evenHalfDim d)))
    (hE : MeasurableSet E) (F : (Fin n → ℝ) → ℝ) (a : ℝ)
    (hbound : ∀ X ∈ E, ∀ y, F y ≤
      spectralNuclearNorm (operatorFrobenius (a • bilinearSynthesis y X))) :
    ∃ G : Set (Fin n → Euclid d), MeasurableSet G ∧
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))) Gᶜ =
        (gaussianBilinearSampleLaw (Fin n) (evenHalfDim d) (evenHalfDim d)) Eᶜ ∧
      ∀ X ∈ G, ∀ y, F y ≤
        spectralNuclearNorm (operatorFrobenius (a • centeredRankOneSynthesis y X)) := by
  let f := extractedRows (n := n) (evenLeft d) (evenRight d)
  have hp := even_extractedRows_preserving d n
  refine ⟨f ⁻¹' E, hE.preimage hp.measurable, ?_, ?_⟩
  · change (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))) (f ⁻¹' Eᶜ) = _
    rw [← Measure.map_apply hp.measurable hE.compl, hp.map_eq]
  · intro X hX y
    exact (hbound (f X) hX y).trans
      (extracted_bilinear_nuclear_le_centered _ _ (evenLeft_ne_evenRight d) y X a)

#print axioms twice_evenHalfDim_le
#print axioms evenLeft_ne_evenRight
#print axioms even_extractedRows_preserving
#print axioms even_good_event_transfer
end GaussianEllipsoidCandidate
