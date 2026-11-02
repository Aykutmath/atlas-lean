import PaperSigmaFieldSmallBall
import PaperScaledNuclearSmallBall

noncomputable section
open MeasureTheory ProbabilityTheory Finset GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.SmallBall

/-- The exact scaled nuclear block corollary conditioned on an arbitrary
independent sigma-field, with random measurable coefficients, length and center. -/
theorem paper_conditional_scaled_nuclear_small_ball_sigmaField
    {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (r n : ℕ) (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (G : Ω → BilinearSample r n) (hG : Measurable G)
    (hLaw : μ.map G = bilinearGaussianSampleLaw r n)
    (hind : Indep m (MeasurableSpace.comap G inferInstance) μ)
    (u : Ω → Fin n → ℝ) (σ : Ω → ℝ) (C : Ω → FrobeniusMatrix r r)
    (humeas : Measurable[m] u) (hσmeas : Measurable[m] σ) (hCmeas : Measurable[m] C)
    {d : ℝ} (hd : 0 < d)
    (hu : ∀ᵐ ω ∂μ, 0 < σ ω ∧ (∑ i, (u ω i)^2 = (σ ω)^2) ∧
      Real.sqrt (r:ℝ)*‖u ω‖/σ ω ≤ θ) :
    μ[({ω | spectralNuclearNorm (bilinearScaled d r n (u ω) (G ω)-C ω) ≤
      (1/1024:ℝ)*σ ω*(r:ℝ)^(3/2:ℝ)/Real.sqrt d}).indicator (1 : Ω → ℝ) | m] ≤ᵐ[μ]
        fun _ => Real.exp (-(r*r:ℕ)) := by
  let P := (Fin n → ℝ) × ℝ × FrobeniusMatrix r r
  let Z : Ω → P := fun ω => (u ω,σ ω,C ω)
  let S : Set (P × BilinearSample r n) :=
    {p | spectralNuclearNorm (bilinearScaled d r n p.1.1 p.2-p.1.2.2) ≤
      (1/1024:ℝ)*p.1.2.1*(r:ℝ)^(3/2:ℝ)/Real.sqrt d}
  have hB : Measurable (fun p : P × BilinearSample r n => bilinearFrobenius r n p.1.1 p.2) :=
    (frobeniusEquivEuclidean r r).symm.continuous.measurable.comp
      (measurable_random_bilinearFlat r n (fun p : P => p.1) measurable_fst)
  have hBS : Measurable (fun p : P × BilinearSample r n => bilinearScaled d r n p.1.1 p.2) :=
    hB.const_smul (Real.sqrt (r:ℝ)/Real.sqrt d)
  have hS : MeasurableSet S := by
    apply measurableSet_le
      ((continuous_spectralNuclear r r).measurable.comp
        (hBS.sub (measurable_snd.comp (measurable_snd.comp measurable_fst))))
    exact (((measurable_fst.comp (measurable_snd.comp measurable_fst)).const_mul (1/1024:ℝ)).mul_const
      ((r:ℝ)^(3/2:ℝ))).div_const (Real.sqrt d)
  have hb : ∀ᵐ ω ∂μ, (μ.map G) {g | (Z ω,g) ∈ S} ≤ ENNReal.ofReal (Real.exp (-(r*r:ℕ))) := by
    rw [hLaw]
    filter_upwards [hu] with ω hω
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    exact paper_scaled_nuclear_small_ball r n hr hθ0 hθ (u ω) hω.1 hd
      hω.2.1 hω.2.2 (C ω)
  exact GaussianConditionalBound.condExp_event_le m μ hm Z G
    (humeas.prodMk (hσmeas.prodMk hCmeas)) hG hind S hS _ (Real.exp_nonneg _) hb

#print axioms paper_conditional_scaled_nuclear_small_ball_sigmaField
end GaussianEllipsoid.SmallBall
