import GaussianLinearMoments

/-! Shared exact Gaussian coordinate-law transport used by both endpoints. -/
noncomputable section
open MeasureTheory GaussianTensorMoments GaussianMixedNormHelpers BMQuadraticSpectral
open scoped BigOperators

namespace BMUniformMoment

/-- Actual Gaussian sample law, in which each row is an independent d-vector. -/
abbrev gaussianSampleLaw (d n : ℕ) : Measure (Fin n → BMQuadraticSpectral.Euclid d) :=
  Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))

end BMUniformMoment

namespace BMBoxRiskAssembly

abbrev CoordinateSample (d n : ℕ) := Fin n → (Fin d → ℝ)

/-- The literal iid N(0,I_d) law in ordinary coordinates. -/
abbrev coordinateSampleLaw (d n : ℕ) : Measure (CoordinateSample d n) :=
  Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin d))

/-- The rowwise measurable equivalence, retaining exactly n rows. -/
def sampleEuclideanEquiv (d n : ℕ) : CoordinateSample d n ≃ᵐ (Fin n → Euclid d) :=
  MeasurableEquiv.piCongrRight (fun _ : Fin n => (MeasurableEquiv.toLp 2 ((Fin d) → ℝ)))

@[simp] theorem sampleEuclideanEquiv_apply (d n : ℕ) (x : CoordinateSample d n) (i : Fin n) :
    sampleEuclideanEquiv d n x i = (MeasurableEquiv.toLp 2 ((Fin d) → ℝ)) (x i) := rfl

/-- Exact source transport for the entire iid sample. -/
theorem sampleEuclideanEquiv_measurePreserving (d n : ℕ) :
    MeasurePreserving (sampleEuclideanEquiv d n) (coordinateSampleLaw d n)
      (BMUniformMoment.gaussianSampleLaw d n) := by
  let e := (MeasurableEquiv.toLp 2 ((Fin d) → ℝ))
  letI : ∀ _i : Fin n, SigmaFinite (euclideanGaussianLaw (Fin d)) := fun _ => inferInstance
  have he : MeasurePreserving e (gaussianProductLaw (Fin d))
      (euclideanGaussianLaw (Fin d)) := ⟨e.measurable, rfl⟩
  exact measurePreserving_pi _ _ (fun _ => he)

/-- Equality holds for every event, including an existential event before its
measurability has been separately proved. -/
theorem coordinate_event_probability (d n : ℕ) (E : Set (Fin n → Euclid d)) :
    (coordinateSampleLaw d n).real ((sampleEuclideanEquiv d n) ⁻¹' E) =
      (BMUniformMoment.gaussianSampleLaw d n).real E := by
  exact congrArg ENNReal.toReal
    ((sampleEuclideanEquiv_measurePreserving d n).measure_preimage_emb
      (sampleEuclideanEquiv d n).measurableEmbedding E)

end BMBoxRiskAssembly
