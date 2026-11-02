import CanonicalGaussianSplit
import CanonicalMultiscaleLaw
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.ProjectedClusters
open scoped ENNReal Topology
namespace GaussianEllipsoidCandidate

/-- Eventual rectangular lower bounds and vanishing bad probability yield
all-dimension centered lower bounds after discarding only finitely many events.
The limit is zero, so the requested limsup ≤ δ follows for every δ>0. -/
theorem eventual_even_good_event_transfer (n : ℕ → ℕ)
    (E : ∀ d, Set (Fin (n d) → Euclid (evenHalfDim d) × Euclid (evenHalfDim d)))
    (hE : ∀ d, MeasurableSet (E d))
    (F : ∀ d, (Fin (n d) → ℝ) → ℝ) (a : ℕ → ℝ)
    (hbound : ∀ᶠ d in atTop, ∀ X ∈ E d, ∀ y, F d y ≤
      spectralNuclearNorm (operatorFrobenius (a d • bilinearSynthesis y X)))
    (hlim : Tendsto (fun d =>
      ((gaussianBilinearSampleLaw (Fin (n d)) (evenHalfDim d) (evenHalfDim d)) (E d)ᶜ).toReal)
      atTop (𝓝 0)) :
    ∃ G : ∀ d, Set (Fin (n d) → Euclid d),
      (∀ d, MeasurableSet (G d)) ∧
      limsup (fun d => ((Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d)))
        (G d)ᶜ).toReal) atTop = 0 ∧
      ∀ d X, X ∈ G d → ∀ y, F d y ≤
        spectralNuclearNorm (operatorFrobenius (a d • centeredRankOneSynthesis y X)) := by
  obtain ⟨D, hD⟩ := eventually_atTop.1 hbound
  let f (d : ℕ) := extractedRows (n := n d) (evenLeft d) (evenRight d)
  let G (d : ℕ) : Set (Fin (n d) → Euclid d) :=
    if D ≤ d then f d ⁻¹' E d else ∅
  have hg (d : ℕ) : MeasurableSet (G d) := by
    dsimp [G]
    split_ifs
    · exact (hE d).preimage (even_extractedRows_preserving d (n d)).measurable
    · exact MeasurableSet.empty
  have heq : (fun d => ((Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d)))
      (G d)ᶜ).toReal) =ᶠ[atTop]
      (fun d => ((gaussianBilinearSampleLaw (Fin (n d)) (evenHalfDim d) (evenHalfDim d))
        (E d)ᶜ).toReal) := by
    filter_upwards [eventually_ge_atTop D] with d hd
    have hp := even_extractedRows_preserving d (n d)
    have he : (G d)ᶜ = f d ⁻¹' (E d)ᶜ := by simp [G, hd]
    rw [he, ← Measure.map_apply hp.measurable (hE d).compl, hp.map_eq]
  refine ⟨G, hg, (hlim.congr' heq.symm).limsup_eq, ?_⟩
  intro d X hX y
  by_cases hd : D ≤ d
  · have hXin : f d X ∈ E d := by simpa only [G, if_pos hd, Set.mem_preimage] using hX
    exact (hD d hd (f d X) hXin y).trans
      (extracted_bilinear_nuclear_le_centered _ _ (evenLeft_ne_evenRight d) y X (a d))
  · simp [G, hd] at hX

/-- The original-sample compression bridge written in tensor coordinates. -/
theorem tensor_bilinear_nuclear_le_centered (d n : ℕ)
    (y : Fin n → ℝ) (X : Fin n → Euclid d) :
    spectralNuclearNorm (gaussianBilinearOperator n (evenHalfDim d) d
      (splitCoordinateRows n (evenLeft d) (evenRight d) X)
      ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) y)) ≤
    spectralNuclearNorm (operatorFrobenius
      ((Real.sqrt (d:ℝ))⁻¹ • centeredRankOneSynthesis y X)) := by
  rw [← scaled_bilinearSynthesis_tensorToCanonicalRows,
    ← extractedRows_eq_tensorToCanonicalRows]
  exact extracted_bilinear_nuclear_le_centered _ _ (evenLeft_ne_evenRight d) y X _

/-- Tensor-coordinate version of the final probability/finite-prefix wrapper. -/
theorem eventual_even_tensor_good_event_transfer (n : ℕ → ℕ)
    (E : ∀ d, Set (GaussianEntries (n d) (evenHalfDim d) × GaussianEntries (n d) (evenHalfDim d)))
    (hE : ∀ d, MeasurableSet (E d))
    (F : ∀ d, (Fin (n d) → ℝ) → ℝ)
    (hbound : ∀ᶠ d in atTop, ∀ z ∈ E d, ∀ y, F d y ≤
      spectralNuclearNorm (gaussianBilinearOperator (n d) (evenHalfDim d) d z
        ((MeasurableEquiv.toLp 2 ((Fin (n d)) → ℝ)) y)))
    (hlim : Tendsto (fun d => ((tensorGaussianLaw (n d) (evenHalfDim d)) (E d)ᶜ).toReal)
      atTop (𝓝 0)) :
    ∃ G : ∀ d, Set (Fin (n d) → Euclid d),
      (∀ d, MeasurableSet (G d)) ∧
      limsup (fun d => ((Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d)))
        (G d)ᶜ).toReal) atTop = 0 ∧
      ∀ d X, X ∈ G d → ∀ y, F d y ≤
        spectralNuclearNorm (operatorFrobenius
          ((Real.sqrt (d:ℝ))⁻¹ • centeredRankOneSynthesis y X)) := by
  obtain ⟨D, hD⟩ := eventually_atTop.1 hbound
  let f (d : ℕ) := splitCoordinateRows (n d) (evenLeft d) (evenRight d)
  have hp (d : ℕ) : MeasurePreserving (f d)
      (Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d)))
      (tensorGaussianLaw (n d) (evenHalfDim d)) :=
    splitCoordinateRows_preserving (n d) _ _ (evenLeft_ne_evenRight d)
  let G (d : ℕ) : Set (Fin (n d) → Euclid d) :=
    if D ≤ d then f d ⁻¹' E d else ∅
  have hg (d : ℕ) : MeasurableSet (G d) := by
    dsimp [G]
    split_ifs
    · exact (hE d).preimage (hp d).measurable
    · exact MeasurableSet.empty
  have heq : (fun d => ((Measure.pi (fun _ : Fin (n d) => euclideanGaussianLaw (Fin d)))
      (G d)ᶜ).toReal) =ᶠ[atTop]
      (fun d => ((tensorGaussianLaw (n d) (evenHalfDim d)) (E d)ᶜ).toReal) := by
    filter_upwards [eventually_ge_atTop D] with d hd
    have he : (G d)ᶜ = f d ⁻¹' (E d)ᶜ := by simp [G, hd]
    rw [he, ← Measure.map_apply (hp d).measurable (hE d).compl, (hp d).map_eq]
  refine ⟨G, hg, (hlim.congr' heq.symm).limsup_eq, ?_⟩
  intro d X hX y
  by_cases hd : D ≤ d
  · have hXin : f d X ∈ E d := by simpa only [G, if_pos hd, Set.mem_preimage] using hX
    exact (hD d hd (f d X) hXin y).trans (tensor_bilinear_nuclear_le_centered d (n d) y X)
  · simp [G, hd] at hX

#print axioms tensor_bilinear_nuclear_le_centered
#print axioms eventual_even_tensor_good_event_transfer
#print axioms eventual_even_good_event_transfer
end GaussianEllipsoidCandidate
