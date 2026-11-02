import IndependentConditionalBound
import PaperConditionalSmallBall
import PaperNuclearSmallBall
import PolarDuality

noncomputable section
open MeasureTheory ProbabilityTheory Finset GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.SmallBall

/-- The paper's Frobenius small-ball bound conditioned on any independent
sigma-field, on an arbitrary underlying probability space. Coefficients and
center are measurable with respect to that sigma-field and may be random. -/
theorem paper_conditional_frobenius_small_ball
    {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (r n : ℕ) (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (G : Ω → BilinearSample r n) (hG : Measurable G)
    (hLaw : μ.map G = bilinearGaussianSampleLaw r n)
    (hind : Indep m (MeasurableSpace.comap G inferInstance) μ)
    (z : Ω → Fin n → ℝ) (M : Ω → EuclideanSpace ℝ (Fin r × Fin r))
    (hzmeas : Measurable[m] z) (hMmeas : Measurable[m] M)
    (hz : ∀ᵐ ω ∂μ, (∑ i, (z ω i)^2 = 1) ∧ Real.sqrt (r:ℝ)*‖z ω‖ ≤ θ)
    {t : ℝ} (ht : 0 < t) :
    μ[({ω | ‖bilinearFlat r n (z ω) (G ω)-M ω‖ ≤ t*Real.sqrt (r:ℝ)}).indicator
      (1 : Ω → ℝ) | m] ≤ᵐ[μ] fun _ => (4*t)^(r*r) := by
  let P := (Fin n → ℝ) × EuclideanSpace ℝ (Fin r × Fin r)
  let Z : Ω → P := fun ω => (z ω,M ω)
  let S : Set (P × BilinearSample r n) :=
    {p | ‖bilinearFlat r n p.1.1 p.2-p.1.2‖ ≤ t*Real.sqrt (r:ℝ)}
  have hS : MeasurableSet S := by
    exact ((measurable_random_bilinearFlat r n (fun p : P => p.1) measurable_fst).sub
      (measurable_snd.comp measurable_fst)).norm measurableSet_Iic
  have hb : ∀ᵐ ω ∂μ, (μ.map G) {g | (Z ω,g) ∈ S} ≤ ENNReal.ofReal ((4*t)^(r*r)) := by
    rw [hLaw]
    filter_upwards [hz] with ω hω
    exact paper_determinant_frobenius_small_ball r n hr hθ0 hθ (z ω) hω.1 hω.2 (M ω) ht
  exact GaussianConditionalBound.condExp_event_le m μ hm Z G (hzmeas.prodMk hMmeas)
    hG hind S hS ((4*t)^(r*r)) (by positivity) hb

/-- The arbitrary-center nuclear small-ball estimate as an actual conditional
expectation given any independent sigma-field. There is no product-model or
assumed conditional-law premise. -/
theorem paper_conditional_nuclear_small_ball
    {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (r n : ℕ) (hr : 0 < r) {θ : ℝ} (hθ : θ < 1/Real.sqrt 2)
    (G : Ω → BilinearSample r n) (hG : Measurable G)
    (hLaw : μ.map G = bilinearGaussianSampleLaw r n)
    (hind : Indep m (MeasurableSpace.comap G inferInstance) μ)
    (z : Ω → Fin n → ℝ) (M : Ω → FrobeniusMatrix r r)
    (hzmeas : Measurable[m] z) (hMmeas : Measurable[m] M)
    (hz : ∀ᵐ ω ∂μ, (∑ i, (z ω i)^2 = 1) ∧ Real.sqrt (r:ℝ)*‖z ω‖ ≤ θ) :
    μ[({ω | spectralNuclearNorm (bilinearFrobenius r n (z ω) (G ω)-M ω) ≤ (r:ℝ)/1024}).indicator
      (1 : Ω → ℝ) | m] ≤ᵐ[μ] fun _ => Real.exp (-(r*r:ℕ)) := by
  let P := (Fin n → ℝ) × FrobeniusMatrix r r
  let Z : Ω → P := fun ω => (z ω,M ω)
  let S : Set (P × BilinearSample r n) :=
    {p | spectralNuclearNorm (bilinearFrobenius r n p.1.1 p.2-p.1.2) ≤ (r:ℝ)/1024}
  have hB : Measurable (fun p : P × BilinearSample r n => bilinearFrobenius r n p.1.1 p.2) :=
    (frobeniusEquivEuclidean r r).symm.continuous.measurable.comp
      (measurable_random_bilinearFlat r n (fun p : P => p.1) measurable_fst)
  have hS : MeasurableSet S :=
    ((continuous_spectralNuclear r r).measurable.comp
      (hB.sub (measurable_snd.comp measurable_fst))) measurableSet_Iic
  have hb : ∀ᵐ ω ∂μ, (μ.map G) {g | (Z ω,g) ∈ S} ≤ ENNReal.ofReal (Real.exp (-(r*r:ℕ))) := by
    rw [hLaw]
    filter_upwards [hz] with ω hω
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact paper_arbitrary_center_nuclear_small_ball r n hr hθ (z ω) hω.1 hω.2 (M ω)
  exact GaussianConditionalBound.condExp_event_le m μ hm Z G (hzmeas.prodMk hMmeas)
    hG hind S hS _ (Real.exp_nonneg _) hb

#print axioms paper_conditional_frobenius_small_ball
#print axioms paper_conditional_nuclear_small_ball
end GaussianEllipsoid.SmallBall
