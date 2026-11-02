import PaperSigmaFieldSmallBall
import PaperScaledSmallBall

noncomputable section
open MeasureTheory ProbabilityTheory Finset GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.SmallBall

/-- Corollary 5.5 conditioned on any sigma-field independent of the Gaussian
drivers. Coefficients, their positive length, and the center can all be random
and measurable with respect to the conditioning sigma-field. -/
theorem paper_conditional_scaled_frobenius_small_ball_sigmaField
    {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (r n : ℕ) (hr : 0 < r) {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (G : Ω → BilinearSample r n) (hG : Measurable G)
    (hLaw : μ.map G = bilinearGaussianSampleLaw r n)
    (hind : Indep m (MeasurableSpace.comap G inferInstance) μ)
    (u : Ω → Fin n → ℝ) (σ : Ω → ℝ) (C : Ω → FrobeniusMatrix r r)
    (humeas : Measurable[m] u) (hσmeas : Measurable[m] σ) (hCmeas : Measurable[m] C)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t)
    (hu : ∀ᵐ ω ∂μ, 0 < σ ω ∧ (∑ i, (u ω i)^2 = (σ ω)^2) ∧
      Real.sqrt (r:ℝ)*‖u ω‖/σ ω ≤ θ) :
    μ[({ω | ‖bilinearScaled d r n (u ω) (G ω)-C ω‖ ≤
      t*σ ω*(r:ℝ)/Real.sqrt d}).indicator (1 : Ω → ℝ) | m] ≤ᵐ[μ]
        fun _ => (4*t)^(r*r) := by
  let P := (Fin n → ℝ) × ℝ × FrobeniusMatrix r r
  let Z : Ω → P := fun ω => (u ω,σ ω,C ω)
  let S : Set (P × BilinearSample r n) :=
    {p | ‖bilinearScaled d r n p.1.1 p.2-p.1.2.2‖ ≤
      t*p.1.2.1*(r:ℝ)/Real.sqrt d}
  have hB : Measurable (fun p : P × BilinearSample r n => bilinearFrobenius r n p.1.1 p.2) :=
    (frobeniusEquivEuclidean r r).symm.continuous.measurable.comp
      (measurable_random_bilinearFlat r n (fun p : P => p.1) measurable_fst)
  have hBS : Measurable (fun p : P × BilinearSample r n => bilinearScaled d r n p.1.1 p.2) :=
    hB.const_smul (Real.sqrt (r : ℝ) / Real.sqrt d)
  have hS : MeasurableSet S := by
    apply measurableSet_le
      ((hBS.sub (measurable_snd.comp (measurable_snd.comp measurable_fst))).norm)
    exact (((measurable_fst.comp (measurable_snd.comp measurable_fst)).const_mul t).mul_const _).div_const _
  have hb : ∀ᵐ ω ∂μ, (μ.map G) {g | (Z ω,g) ∈ S} ≤ ENNReal.ofReal ((4*t)^(r*r)) := by
    rw [hLaw]
    filter_upwards [hu] with ω hω
    apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*t)^(r*r))]
    exact paper_scaled_frobenius_small_ball r n hr hθ0 hθ (u ω) hω.1 hd ht
      hω.2.1 hω.2.2 (C ω)
  exact GaussianConditionalBound.condExp_event_le m μ hm Z G
    (humeas.prodMk (hσmeas.prodMk hCmeas)) hG hind S hS _ (by positivity) hb

#print axioms paper_conditional_scaled_frobenius_small_ball_sigmaField
end GaussianEllipsoid.SmallBall
