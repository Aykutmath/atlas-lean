import AHHSphereAmbientGaussianLaw
import AHHAngularGaussianIntegrability

/-! Block marginals and null-origin/inverse-radius control for the actual ambient Gaussian. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers
open scoped BigOperators
namespace AHHRadial

theorem sphereAmbient_block_preserving (n h : ℕ) (hh : 0 < h) (j : Fin n × Bool) :
    MeasurePreserving (fun z : SphereAmbient n h => z j) (sphereAmbientGaussianLaw n h)
      (radialGaussianLaw (volume : Measure (CE h)) h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  letI := gaussianPairLaw_probability h hh
  letI := radialGaussianLaw_isProbabilityMeasure (volume : Measure (CE h))
    (show (0 : ℝ) < h by exact_mod_cast hh)
  rcases j with ⟨i,b⟩
  have hi := measurePreserving_eval (μ := fun _ : Fin n => gaussianPairLaw h) i
  cases b
  · exact (measurePreserving_fst.comp hi).comp (sphereAmbientToPairs_preserving n h)
  · exact (measurePreserving_snd.comp hi).comp (sphereAmbientToPairs_preserving n h)

theorem sphereAmbient_integrable_inv_norm_sq (n h : ℕ) (hh : 2 ≤ h) (j : Fin n × Bool) :
    Integrable (fun z : SphereAmbient n h => (‖z j‖ ^ 2)⁻¹) (sphereAmbientGaussianLaw n h) := by
  letI : NeZero h := ⟨by omega⟩
  have hi := radialGaussian_integrable_inv_norm_sq (volume : Measure (CE h))
    (show (0 : ℝ) < h by exact_mod_cast (show 0 < h by omega))
    (by rw [complex_finrank_real]; omega)
  exact (sphereAmbient_block_preserving n h (by omega) j).integrable_comp_of_integrable hi

theorem sphereAmbientGaussian_ae_nonzero (n h : ℕ) (hh : 0 < h) :
    ∀ᵐ z ∂sphereAmbientGaussianLaw n h, ∀ j, z j ≠ 0 := by
  have hT := pairsToSphereAmbient_preserving n h
  rw [← hT.map_eq]
  apply (ae_map_iff hT.measurable.aemeasurable (by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl)).mpr
  filter_upwards [gaussianPairs_ae_nonzero n h hh] with z hz
  rintro ⟨i,b⟩
  cases b
  · exact (hz i).1
  · exact (hz i).2

#print axioms sphereAmbient_block_preserving
#print axioms sphereAmbient_integrable_inv_norm_sq
#print axioms sphereAmbientGaussian_ae_nonzero
end AHHRadial
