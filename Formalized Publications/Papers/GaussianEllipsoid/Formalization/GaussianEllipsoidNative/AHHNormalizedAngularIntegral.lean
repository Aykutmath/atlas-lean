import AHHActualAngularEnergy
import AHHActualAmbientMarginals

/-! Exact integral transfer for the genuine block-normalized observable. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers
namespace AHHRadial

theorem blockNormalize_eq_directions_ae (n h : ℕ) [NeZero h] (hh : 0 < h) :
    ∀ᵐ z ∂sphereAmbientGaussianLaw n h,
      blockNormalize z = (directionsToEuclidean n h (sphereAmbientDirections n h z)).val := by
  filter_upwards [sphereAmbientGaussian_ae_nonzero n h hh] with z hz
  have hn : ∀ i, (sphereAmbientToPairs n h z i).1 ≠ 0 ∧
      (sphereAmbientToPairs n h z i).2 ≠ 0 := fun i => ⟨hz (i,false), hz (i,true)⟩
  have he := blockNormalize_pairsToSphereAmbient n h (sphereAmbientToPairs n h z) hn
  rw [pairsToSphereAmbient_sphereAmbientToPairs] at he
  exact he

/-- Any measurable scalar test of the normalized ambient sample has its actual sphere integral. -/
theorem integral_comp_blockNormalize (n h : ℕ) [NeZero h] (hh : 0 < h)
    (φ : SphereAmbient n h → ℝ) (hφ : Measurable φ) :
    (∫ z, φ (blockNormalize z) ∂sphereAmbientGaussianLaw n h) =
      ∫ d, φ (directionsToEuclidean n h d).val ∂directionsLaw n h := by
  have he : (fun z => φ (blockNormalize z)) =ᵐ[sphereAmbientGaussianLaw n h]
      (fun z => φ (directionsToEuclidean n h (sphereAmbientDirections n h z)).val) :=
    (blockNormalize_eq_directions_ae n h hh).mono fun z hz => congrArg φ hz
  rw [integral_congr_ae he]
  have hp := sphereAmbientDirections_preserving n h hh
  have hm := integral_map (μ := sphereAmbientGaussianLaw n h) hp.measurable.aemeasurable
    ((hφ.comp (continuous_directionsToEuclidean_val n h).measurable).aestronglyMeasurable)
  rw [hp.map_eq] at hm
  exact hm.symm

theorem integrable_comp_blockNormalize (n h : ℕ) [NeZero h] (hh : 0 < h)
    (φ : SphereAmbient n h → ℝ)
    (hφ : Integrable (fun d => φ (directionsToEuclidean n h d).val) (directionsLaw n h)) :
    Integrable (fun z => φ (blockNormalize z)) (sphereAmbientGaussianLaw n h) := by
  have hp := (sphereAmbientDirections_preserving n h hh).integrable_comp_of_integrable hφ
  apply hp.congr
  filter_upwards [blockNormalize_eq_directions_ae n h hh] with z hz
  exact congrArg φ hz.symm

#print axioms blockNormalize_eq_directions_ae
#print axioms integral_comp_blockNormalize
#print axioms integrable_comp_blockNormalize
end AHHRadial
