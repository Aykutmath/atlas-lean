import PaperRetainedParameters

noncomputable section
namespace UCEscape

theorem paper_binary_entropy_upper {θ : ℝ} (hθ : θ < 1) :
    -θ*Real.log θ-(1-θ)*Real.log (1-θ) ≤ θ*(1-Real.log θ) := by
  have hp : 0 < 1-θ := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  have he : (1-θ)*(1-(1-θ)⁻¹) = -θ := by field_simp; ring
  rw [he] at hm
  linarith

/-- The numerical parameters also satisfy exactly the binary-entropy budget
written in the manuscript. -/
theorem paper_retained_parameters_with_entropy {ε C₁ : ℝ}
    (hε : 0 < ε) (hC : 0 < C₁) :
    ∃ δ θ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < θ ∧ θ < 1/2 ∧
      θ*C₁ ≤ ε/2 ∧
      C₁*(-θ*Real.log θ-(1-θ)*Real.log (1-θ)) ≤ (paperRetainedGamma ε)^2/8 ∧
      1/2+3*paperRetainedGamma ε ≤ (1-2*δ)*Real.sqrt (1/4+ε/2) ∧
      0 < (1/4+ε)-θ*C₁-(1/4+ε/2) ∧
      C₁*(θ*(1-Real.log θ)) ≤ δ^2*(1/4+ε/2)/16 := by
  obtain ⟨δ,θ,hδ,hδhalf,hθ,hθhalf,hθC,hm,hs,he⟩ := paper_retained_parameters hε hC
  refine ⟨δ,θ,hδ,hδhalf,hθ,hθhalf,hθC,?_,hm,hs,he⟩
  have hb : (0:ℝ) ≤ 1/4+ε/2 := by linarith
  have hc := paperRetainedGamma_pos hε
  have hds : δ*Real.sqrt (1/4+ε/2) ≤ paperRetainedGamma ε/2 := by
    dsimp [paperRetainedGamma] at hm ⊢
    nlinarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ δ*Real.sqrt (1/4+ε/2)) hds
  have hsqrt := Real.sq_sqrt hb
  have hbound : δ^2*(1/4+ε/2)/16 ≤ (paperRetainedGamma ε)^2/8 := by nlinarith
  exact (mul_le_mul_of_nonneg_left (paper_binary_entropy_upper (by linarith)) hC.le).trans (he.trans hbound)
end UCEscape
#print axioms UCEscape.paper_retained_parameters_with_entropy
