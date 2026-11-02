import PaperRetainedEntropy
import PaperGaussianCutoffSharp

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments BMGeometry BMSaddle
open scoped BigOperators
namespace UCEscape

/-- The manuscript's literal cutoff and threshold a=gamma/(2sqrt C1), now
with all dimension/nuisance/entropy calibration discharged and exponential failure. -/
theorem paper_gaussian_cutoff_margin {ε C₁ : ℝ} (hε : 0 < ε) (hC : 0 < C₁) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1/2 ∧ ∃ d₀ : ℕ,
      ∀ d n : ℕ, d₀ ≤ d → (n:ℝ) ≤ C₁*(d:ℝ)^2 →
      ∀ L : Submodule ℝ (Euclid n),
        (1/4+ε)*(d:ℝ)^2 ≤ (n:ℝ)-(Module.finrank ℝ L:ℝ) →
        ∃ G : Set (BMSaddle.Raw n d), MeasurableSet G ∧
          (rawSourceLaw n d).real Gᶜ ≤ Real.exp (-(paperRetainedGamma ε)^2*(d:ℝ)^2/4) ∧
          ∀ z ∈ G, ∀ A : Square d, A.PosSemidef → frobeniusNorm A = 1 →
            ∀ v : Euclid n, v ∈ L →
              θ ≤ (∑ i, PaperSmoothCutoff.loss (paperRetainedGamma ε/(2*Real.sqrt C₁))
                (UCNormalizedRows.gaussianRow A (z i)-v i))/(n:ℝ) := by
  obtain ⟨δ,θ,hδ,hδhalf,hθ,hθhalf,hθC,hbinary,hmargin,hslack,hent⟩ := paper_retained_parameters_with_entropy hε hC
  have hc := paperRetainedGamma_pos hε
  have hα : (0:ℝ) < 1/4+ε := by linarith
  have hβ : (0:ℝ) < 1/4+ε/2 := by linarith
  obtain ⟨d₀,hd₀⟩ := effective_aspect_numeric_calibration_eventually
    (1/4+ε) C₁ (1/4+ε/2) δ (paperRetainedGamma ε) θ
    hα hC hβ hδ hδhalf hc hθ (by linarith) hmargin hslack hent 1 (by norm_num)
  refine ⟨θ,hθ,hθhalf,d₀,?_⟩
  intro d n hd hn L hdim
  obtain ⟨hnpos,hdpos,hrpos,hbudget,hθk,hgap,hmean,hprob⟩ :=
    hd₀ d hd n (Module.finrank ℝ L) hdim hn
  obtain ⟨G,hG,htail,hgood⟩ := exists_gaussian_paper_cutoff_sharp_good_event
    hnpos hdpos hrpos L hbudget δ (paperRetainedGamma ε/(2*Real.sqrt C₁)) θ
    (paperRetainedGamma ε*d) (paperRetainedGamma ε*d)
    hδ.le (by linarith) (by positivity) (mul_pos hc (Nat.cast_pos.mpr hdpos)) hgap hθk hmean
  refine ⟨G,hG,htail.trans ?_,hgood⟩
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (paperRetainedGamma ε*(d:ℝ))]
end UCEscape
#print axioms UCEscape.paper_gaussian_cutoff_margin
