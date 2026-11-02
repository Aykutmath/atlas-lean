import PaperGrowingRankCalibration

noncomputable section
namespace UCEscape

def paperRetainedGamma (ε : ℝ) : ℝ := (Real.sqrt (1/4+ε/2)-1/2)/4

theorem paperRetainedGamma_pos {ε : ℝ} (hε : 0 < ε) : 0 < paperRetainedGamma ε := by
  have h : (1/2:ℝ) < Real.sqrt (1/4+ε/2) := (Real.lt_sqrt (by norm_num)).mpr (by nlinarith)
  dsimp [paperRetainedGamma]
  linarith

/-- Numerical calibration with the paper's literal gamma(epsilon), independent
of the upper aspect bound; theta may depend on epsilon and C1. -/
theorem paper_retained_parameters {ε C₁ : ℝ} (hε : 0 < ε) (hC : 0 < C₁) :
    ∃ δ θ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < θ ∧ θ < 1/2 ∧
      θ*C₁ ≤ ε/2 ∧
      1/2+3*paperRetainedGamma ε ≤ (1-2*δ)*Real.sqrt (1/4+ε/2) ∧
      0 < (1/4+ε)-θ*C₁-(1/4+ε/2) ∧
      C₁*(θ*(1-Real.log θ)) ≤ δ^2*(1/4+ε/2)/16 := by
  let b : ℝ := 1/4+ε/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hg : (1/2:ℝ) < Real.sqrt b := (Real.lt_sqrt (by norm_num)).mpr (by dsimp [b]; nlinarith)
  let δ := (Real.sqrt b-1/2)/(16*Real.sqrt b)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 16*Real.sqrt b)).mpr
    linarith
  let η := min (ε/(4*C₁)) (min (δ^2*b/(16*C₁)) (1/4))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨θ,hθ,hθ1,hrate⟩ := exists_small_deletion_entropy η hη
  have hlog : Real.log θ ≤ 0 := Real.log_nonpos hθ.le hθ1
  have hθrate : θ ≤ θ*(1-Real.log θ) := by nlinarith
  have hsmall : θ ≤ ε/(4*C₁) := hθrate.trans (hrate.trans (min_le_left _ _))
  have hquarter : θ ≤ 1/4 := hθrate.trans (hrate.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hbudget := (le_div_iff₀ (by positivity : 0 < 4*C₁)).mp hsmall
  have hent := hrate.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hent' := (le_div_iff₀ (by positivity : 0 < 16*C₁)).mp hent
  refine ⟨δ,θ,hδ,hδhalf,hθ,by linarith,by nlinarith,?_,by nlinarith,?_⟩
  · have he : δ*(16*Real.sqrt b)=Real.sqrt b-1/2 := by dsimp [δ]; field_simp
    change 1/2+3*((Real.sqrt b-1/2)/4) ≤ (1-2*δ)*Real.sqrt b
    nlinarith
  · change C₁*(θ*(1-Real.log θ)) ≤ δ^2*b/16
    nlinarith
end UCEscape
#print axioms UCEscape.paper_retained_parameters
