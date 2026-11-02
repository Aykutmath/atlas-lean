import StandaloneMixedNormBody
import SparseLimitTransport
import ActualMultiscaleUniform

/-!
UNCONDITIONAL STANDALONE SECTION 11 ENDPOINT.

This file calls the proved actual Gaussian multiscale theorem, the actual
localized Gaussian estimate, the actual L=96 continuity theorem, constructive
clipping, exact Gaussian pushforwards, and nuclear compression. There is no
remaining analytic/probabilistic project premise in its final theorems.

It proves the explicit Euclidean/operator analogue of the supplied interface.
It does not claim to compile against unavailable GaussianEllipsoid.Basic or
MixedNormAsm files, and does not claim the paper's other sections are complete.
-/
noncomputable section
set_option synthInstance.maxSize 1000
open MeasureTheory Filter GaussianEllipsoid GaussianEllipsoidCandidate
open GaussianEllipsoidFinalPassage GaussianTensorMoments
open scoped ENNReal Topology BigOperators
namespace GaussianEllipsoidStandalone

/-- Exact agreement of our assembly event with the actual multiscale event. -/
theorem canonicalSparseGood_eq_actual (n d : ℕ) :
    canonicalSparseGood n (2*(d/4)) d =
      actualMultiscaleGood d n (1/numericalEta^2) := by
  unfold canonicalSparseGood actualMultiscaleGood
  rw [fixed_sparse_coefficient_eq]

/-- The last probabilistic input is now discharged by the actual proved
Gaussian uniform multiscale theorem, at fixed K=η⁻² and A=1. -/
theorem actual_flat_sparse_failure_tendsto_zero (n : ℕ → ℕ)
    (haspect : limsup (dimensionRatio n) atTop < (1/4:ℝ≥0∞)) :
    Tendsto (fun d => (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatSparseBad (n d) (2*(d/4)) d)) atTop (𝓝 0) := by
  obtain ⟨α,hα,hα',hn⟩ := exists_eventual_quadratic_bound n haspect
  have hn1 : ∀ᶠ d in atTop, (n d:ℝ) ≤ 1*(d:ℝ)^2 := by
    filter_upwards [hn] with d hd
    exact hd.trans (mul_le_mul_of_nonneg_right (by linarith : α ≤ 1) (sq_nonneg _))
  have hK : 0 ≤ 1/numericalEta^2 := div_nonneg (by norm_num) (sq_nonneg _)
  have ht := actual_multiscale_uniform_failure_tendsto_zero 1 (1/numericalEta^2)
    (by norm_num) hK n hn1
  have heq (d : ℕ) : (tensorGaussianLaw (n d) (2*(d/4))).real
      (flatSparseBad (n d) (2*(d/4)) d) =
      (gaussianBilinearSampleLaw (Fin (n d)) (2*(d/4)) (2*(d/4))).real
        (actualMultiscaleBad d (n d) (1/numericalEta^2)) := by
    rw [flatSparseBad_probability, canonicalSparseGood_eq_actual,
      actualMultiscaleGood_eq_compl, compl_compl]
  simpa only [heq] using ht

/-- Strong unconditional form: one fixed eta works, good events are Borel,
small dimensions are explicitly removed, failure limsup is zero, and the
nuclear lower bound holds for every coefficient vector. -/
theorem unconditional_full_mixed_events (n : ℕ → ℕ)
    (haspect : limsup (dimensionRatio n) atTop < (1/4:ℝ≥0∞)) :
    ∃ c : ℝ, 0 < c ∧ ∃ G : ∀ d, Set (Sample d (n d)),
      (∀ d, MeasurableSet (G d)) ∧
      (∀ d, d < 4 → G d = ∅) ∧
      limsup (fun d => ((gaussianSampleLaw d (n d)) (G d)ᶜ).toReal) atTop = 0 ∧
      ∀ d, ∀ X ∈ G d, ∀ y : Fin (n d) → ℝ,
        c*mixedNorm numericalEta d (n d) y ≤ spectralNuclearNorm (centeredAdjoint X y) := by
  obtain ⟨α,hα,hα',hn⟩ := exists_eventual_quadratic_bound n haspect
  obtain ⟨c,hc,hlim⟩ := flat_mixed_limit_of_sparse_limit hα hα' n hn
    (actual_flat_sparse_failure_tendsto_zero n haspect)
  exact ⟨c,hc,full_mixed_events_of_flat_limit n hc hlim⟩

/-- The supplied MixedNormBody quantifiers, with measurability and the finite
exceptional prefix additionally established rather than postulated. -/
theorem mixedNormBound_measurable (n : ℕ → ℕ)
    (haspect : limsup (dimensionRatio n) atTop < (1/4:ℝ≥0∞)) :
    ∀ δ > 0, ∃ η c : ℝ, ∃ G : ∀ d, Set (Sample d (n d)),
      MixedNormBody n δ η c G ∧ (∀ d, MeasurableSet (G d)) ∧
      (∀ d, d < 4 → G d = ∅) :=
  mixedNormBody_of_sparse_limit n haspect (actual_flat_sparse_failure_tendsto_zero n haspect)

/-- Final unconditional standalone MixedNormBound, with exactly the supplied
positive-sample-count, strict ENNReal limsup, and every-tolerance quantifiers. -/
theorem mixedNormBound : MixedNormBound := by
  intro n _ haspect δ hδ
  obtain ⟨η,c,G,hbody,_,_⟩ := mixedNormBound_measurable n haspect δ hδ
  exact ⟨η,c,G,hbody⟩

end GaussianEllipsoidStandalone
