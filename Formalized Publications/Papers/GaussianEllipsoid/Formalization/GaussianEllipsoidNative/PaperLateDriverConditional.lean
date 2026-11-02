import IndependentConditionalBound
import PaperLateDriverCenter
import PaperConditionalSmallBall
import GaussianOutsideSigmaField

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Finset GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid GaussianEllipsoid.SmallBall GaussianEllipsoid.ProjectedClusters GaussianBilinearTransport
open scoped ENNReal BigOperators
namespace GaussianPairedBlocks

/-- Joint measurability for a randomly selected coefficient vector in the
literal flat Gaussian sample representation. -/
theorem measurable_flatBilinear_random_coefficients
    {Ω : Type*} [MeasurableSpace Ω] (d : ℝ) (h n : ℕ)
    (w : Ω → Fin n → ℝ) (hw : Measurable w) :
    Measurable (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      flatBilinear d h n (w p.1) p.2) := by
  have hFlat := measurable_random_bilinearFlat h n w hw
  have hFrob : Measurable (fun p : Ω × BilinearSample h n => bilinearFrobenius h n (w p.1) p.2) :=
    (frobeniusEquivEuclidean h h).symm.continuous.measurable.comp hFlat
  have hScaled : Measurable (fun p : Ω × BilinearSample h n => bilinearScaled d h n (w p.1) p.2) :=
    hFrob.const_smul (Real.sqrt (h:ℝ)/Real.sqrt d)
  have hMap : Measurable (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      (p.1, flatToSmallBall n h p.2)) :=
    measurable_fst.prodMk ((flatToSmallBall_measurable n h).comp measurable_snd)
  simpa only [flatBilinear, Function.comp_def] using hScaled.comp hMap

/-- Arbitrary-sigma-field late-driver bound. Only the actual selected Gaussian
driver is independent of the field; coefficients and center may depend on it.
No positivity assumption is made on the auxiliary amplitude lambda. -/
theorem late_driver_center_conditional
    {Ω : Type*} (𝓕 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h𝓕 : 𝓕 ≤ mΩ)
    {s d h : ℕ} (hmin : 64 ≤ min s d) (hdh : d ≤ 3*h)
    (G : Ω → GaussianEntries s h × GaussianEntries s h) (hG : Measurable G)
    (hLaw : μ.map G = tensorGaussianLaw s h)
    (hind : Indep 𝓕 (MeasurableSpace.comap G inferInstance) μ)
    (w : Ω → Fin s → ℝ) (C : Ω → FrobeniusMatrix h h)
    (hw : Measurable[𝓕] w) (hC : Measurable[𝓕] C)
    (hamplitude : ∀ᵐ ω ∂μ, ∃ ℓ : ℝ,
      (∀ i, ℓ ≤ |w ω i|) ∧ ∀ i, |w ω i| ≤ 2*ℓ) :
    μ[({ω | spectralNuclearNorm (C ω+flatBilinear (d:ℝ) h s (w ω) (G ω)) <
      (1/1048576:ℝ)*Real.sqrt d*(∑ i, |w ω i|)*Real.sqrt ((min s d:ℕ)/(s:ℝ))}).indicator
      (1 : Ω → ℝ) | 𝓕] ≤ᵐ[μ]
        fun _ => Real.exp (-(1/1048576:ℝ)*(d:ℝ)*(min s d:ℕ)) := by
  let A := (Fin s → ℝ) × FrobeniusMatrix h h
  let T : Ω → A := fun ω => (w ω,C ω)
  let S : Set (A × (GaussianEntries s h × GaussianEntries s h)) :=
    {p | spectralNuclearNorm (p.1.2+flatBilinear (d:ℝ) h s p.1.1 p.2) <
      (1/1048576:ℝ)*Real.sqrt d*(∑ i, |p.1.1 i|)*Real.sqrt ((min s d:ℕ)/(s:ℝ))}
  have hS : MeasurableSet S := by
    apply measurableSet_lt
      ((continuous_spectralNuclear h h).measurable.comp
        ((measurable_snd.comp measurable_fst).add
          (measurable_flatBilinear_random_coefficients (d:ℝ) h s (fun a : A => a.1) measurable_fst)))
    dsimp [A]
    fun_prop
  have hb : ∀ᵐ ω ∂μ, (μ.map G) {z | (T ω,z) ∈ S} ≤
      ENNReal.ofReal (Real.exp (-(1/1048576:ℝ)*(d:ℝ)*(min s d:ℕ))) := by
    rw [hLaw]
    filter_upwards [hamplitude] with ω hω
    obtain ⟨ℓ,hlower,hupper⟩ := hω
    have hp := late_driver_arbitrary_center (Finset.univ : Finset (Fin s)) (w ω) (C ω)
      (by simpa using hmin) hdh (fun i _ => hlower i) (fun i _ => hupper i)
    have hv : driverCoefficients (Finset.univ : Finset (Fin s)) (w ω) = w ω := by
      funext i
      simp [driverCoefficients]
    rw [hv] at hp
    change tensorGaussianLaw s h
      {z | spectralNuclearNorm (C ω+flatBilinear (d:ℝ) h s (w ω) z) <
        (1/1048576:ℝ)*Real.sqrt d*(∑ i, |w ω i|)*Real.sqrt ((min s d:ℕ)/(s:ℝ))} ≤ _
    simpa only [Finset.card_univ, Fintype.card_fin] using hp
  exact GaussianConditionalBound.condExp_event_le 𝓕 μ h𝓕 T G (hw.prodMk hC) hG hind S hS
    _ (Real.exp_nonneg _) hb

/-- Literal outside-sigma-field specialization on the original full Gaussian
array. The driver law and independence are proved for the S-selected samples;
the outside field contains all indices outside S, by outsideSampleEmbedding_range. -/
theorem late_driver_outside_conditional
    {N s d h : ℕ} (eS : Fin s ↪ Fin N) (hmin : 64 ≤ min s d) (hdh : d ≤ 3*h)
    (w : (GaussianEntries N h × GaussianEntries N h) → Fin s → ℝ)
    (C : (GaussianEntries N h × GaussianEntries N h) → FrobeniusMatrix h h)
    (hw : Measurable[outsideSampleSigmaField eS] w)
    (hC : Measurable[outsideSampleSigmaField eS] C)
    (hamplitude : ∀ᵐ ω ∂tensorGaussianLaw N h, ∃ ℓ : ℝ,
      (∀ i, ℓ ≤ |w ω i|) ∧ ∀ i, |w ω i| ≤ 2*ℓ) :
    (tensorGaussianLaw N h)[({ω | spectralNuclearNorm
      (C ω+flatBilinear (d:ℝ) h s (w ω) (selectSample eS ω)) <
      (1/1048576:ℝ)*Real.sqrt d*(∑ i, |w ω i|)*Real.sqrt ((min s d:ℕ)/(s:ℝ))}).indicator
      (1 : (GaussianEntries N h × GaussianEntries N h) → ℝ) | outsideSampleSigmaField eS] ≤ᵐ[tensorGaussianLaw N h]
        fun _ => Real.exp (-(1/1048576:ℝ)*(d:ℝ)*(min s d:ℕ)) :=
  late_driver_center_conditional (outsideSampleSigmaField eS) (tensorGaussianLaw N h)
    (outsideSampleSigmaField_le eS) hmin hdh (selectSample eS) (measurable_selectSample eS)
    (selectSample_preserving eS).map_eq (outsideSampleSigmaField_indep eS) w C hw hC hamplitude

/-- Exact h=floor(d/2) version; the source's large-minimum regime implies the
ambient rank inequality, so no additional dimension premise is introduced. -/
theorem late_driver_outside_half_dimension_conditional
    {N s d : ℕ} (eS : Fin s ↪ Fin N) (hmin : 64 ≤ min s d)
    (w : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → Fin s → ℝ)
    (C : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → FrobeniusMatrix (d/2) (d/2))
    (hw : Measurable[outsideSampleSigmaField eS] w)
    (hC : Measurable[outsideSampleSigmaField eS] C)
    (hamplitude : ∀ᵐ ω ∂tensorGaussianLaw N (d/2), ∃ ℓ : ℝ,
      (∀ i, ℓ ≤ |w ω i|) ∧ ∀ i, |w ω i| ≤ 2*ℓ) :
    (tensorGaussianLaw N (d/2))[({ω | spectralNuclearNorm
      (C ω+flatBilinear (d:ℝ) (d/2) s (w ω) (selectSample eS ω)) <
      (1/1048576:ℝ)*Real.sqrt d*(∑ i, |w ω i|)*Real.sqrt ((min s d:ℕ)/(s:ℝ))}).indicator
      (1 : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → ℝ) | outsideSampleSigmaField eS] ≤ᵐ[tensorGaussianLaw N (d/2)]
        fun _ => Real.exp (-(1/1048576:ℝ)*(d:ℝ)*(min s d:ℕ)) :=
  late_driver_outside_conditional eS hmin (by omega) w C hw hC hamplitude

#print axioms late_driver_center_conditional
#print axioms late_driver_outside_conditional
#print axioms late_driver_outside_half_dimension_conditional
end GaussianPairedBlocks
