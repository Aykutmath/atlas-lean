import PaperRetainedEvent
import PaperRetainedEntropy

noncomputable section
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments BMGeometry BMSaddle
open scoped BigOperators
namespace UCEscape

/-- Corrected dimensionality statement: theta and the retained cardinality are
explicitly quantified, and the sufficiently-large dimension condition from
its source proof is exposed. Gamma is exactly the manuscript's formula. -/
theorem paper_dimensionality_corrected {ε C₁ : ℝ} (hε : 0 < ε) (hC : 0 < C₁) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1/2 ∧ θ*C₁ ≤ ε/2 ∧
      C₁*(-θ*Real.log θ-(1-θ)*Real.log (1-θ)) ≤ (paperRetainedGamma ε)^2/8 ∧ ∃ d₀ : ℕ,
      ∀ d n : ℕ, d₀ ≤ d → (n:ℝ) ≤ C₁*(d:ℝ)^2 →
      ∀ L : Submodule ℝ (Euclid n),
        (1/4+ε)*(d:ℝ)^2 ≤ (n:ℝ)-(Module.finrank ℝ L:ℝ) →
        ∃ G : Set (BMSaddle.Raw n d), MeasurableSet G ∧
          (rawSourceLaw n d).real Gᶜ ≤ Real.exp (-(paperRetainedGamma ε)^2*(d:ℝ)^2/4) ∧
          ∀ z ∈ G, ∀ A : Square d, A.PosSemidef → frobeniusNorm A = 1 →
            ∀ v : Euclid n, v ∈ L →
              ∀ J : Finset (Fin n), J.card = n-Nat.floor (θ*n) →
                paperRetainedGamma ε*d ≤ ‖retainedCoordinates J
                  (WithLp.toLp 2 (fun i => UCNormalizedRows.gaussianRow A (z i))-v)‖ := by
  obtain ⟨δ,θ,hδ,hδhalf,hθ,hθhalf,hθC,hbinary,hmargin,hslack,hent⟩ := paper_retained_parameters_with_entropy hε hC
  have hc := paperRetainedGamma_pos hε
  have hα : (0:ℝ) < 1/4+ε := by linarith
  have hβ : (0:ℝ) < 1/4+ε/2 := by linarith
  obtain ⟨d₀,hd₀⟩ := effective_aspect_numeric_calibration_eventually
    (1/4+ε) C₁ (1/4+ε/2) δ (paperRetainedGamma ε) θ
    hα hC hβ hδ hδhalf hc hθ (by linarith) hmargin hslack hent 1 (by norm_num)
  refine ⟨θ,hθ,hθhalf,hθC,hbinary,d₀,?_⟩
  intro d n hd hn L hdim
  obtain ⟨hnpos,hdpos,hrpos,hbudget,hθk,hgap,hmean,hprob⟩ :=
    hd₀ d hd n (Module.finrank ℝ L) hdim hn
  obtain ⟨G,hG,htail,hgood⟩ := exists_gaussian_retained_sharp_good_event
    hnpos hdpos hrpos L hbudget δ (paperRetainedGamma ε*d) (paperRetainedGamma ε*d)
    hδ.le (by linarith) (mul_pos hc (Nat.cast_pos.mpr hdpos)) hmean
  refine ⟨G,hG,htail.trans ?_,?_⟩
  · apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (paperRetainedGamma ε*(d:ℝ))]
  · intro z hz A hA hF v hv J hJ
    let D : deletedCoordinateSets n (Nat.floor (θ*n)) :=
      ⟨Jᶜ,by
        apply (mem_deletedCoordinateSets _ _ _).mpr
        rw [Finset.card_compl,hJ,Fintype.card_fin]
        omega⟩
    have hretain : retainedOfDeleted D=J := by
      ext i
      simp [retainedOfDeleted,D]
    simpa only [hretain] using hgood z hz A hA hF v hv D
end UCEscape
#print axioms UCEscape.paper_dimensionality_corrected
