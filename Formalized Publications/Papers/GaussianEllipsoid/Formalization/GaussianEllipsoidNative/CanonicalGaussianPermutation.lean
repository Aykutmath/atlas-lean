import GaussianExtractedRowsLaw
import BilinearSynthesis

noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Move old row `i` to the new position `e i`. -/
def permuteRows {ι : Type*} (e : Equiv.Perm ι) {E : Type*} (X : ι → E) : ι → E :=
  fun i => X (e.symm i)

/-- Exact invariance of the canonical iid Gaussian pair law under any fixed row permutation. -/
theorem permuteRows_preserving {ι : Type*} [Fintype ι] (e : Equiv.Perm ι) (q r : ℕ) :
    MeasurePreserving (permuteRows (E := Euclid q × Euclid r) e)
      (gaussianBilinearSampleLaw ι q r) (gaussianBilinearSampleLaw ι q r) := by
  convert (measurePreserving_piCongrLeft
      (fun _ : ι => (euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) e) using 1
  funext X i
  obtain ⟨j,rfl⟩ := e.surjective i
  simp [permuteRows, MeasurableEquiv.piCongrLeft_apply_apply]
  all_goals rfl

/-- Map-equality form of iid row permutation invariance. -/
theorem gaussianBilinearSampleLaw_map_permuteRows {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (q r : ℕ) :
    (gaussianBilinearSampleLaw ι q r).map (permuteRows e) =
      gaussianBilinearSampleLaw ι q r :=
  (permuteRows_preserving e q r).map_eq

/-- Simultaneously reindexing the coefficients and rows leaves the actual
unscaled synthesis operator unchanged. -/
theorem bilinearSynthesis_permuteRows {ι : Type*} [Fintype ι] {q r : ℕ}
    (e : Equiv.Perm ι) (u : ι → ℝ) (X : ι → Euclid q × Euclid r) :
    bilinearSynthesis (permuteRows e u) (permuteRows e X) = bilinearSynthesis u X := by
  exact e.symm.sum_comp (fun i => u i • bilinearRowOperator (X i))

/-- Any measurable canonical-row event has exactly the same probability after
moving samples to their deterministic support-ordered positions. -/
theorem gaussianBilinearSampleLaw_permuteRows_event {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (q r : ℕ) (A : Set (ι → Euclid q × Euclid r))
    (hA : MeasurableSet A) :
    gaussianBilinearSampleLaw ι q r (permuteRows e ⁻¹' A) =
      gaussianBilinearSampleLaw ι q r A :=
  (permuteRows_preserving e q r).measure_preimage hA.nullMeasurableSet

end GaussianEllipsoidCandidate
