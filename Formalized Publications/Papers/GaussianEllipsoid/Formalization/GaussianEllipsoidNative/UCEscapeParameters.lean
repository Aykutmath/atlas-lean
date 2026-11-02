import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
namespace UCEscape

/-- A strict aspect gap above 1/4 supplies fixed positive escape parameters. -/
theorem exists_escape_parameters (β : ℝ) (hβ : 1/4 < β) :
    ∃ ε c : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧ 0 < c ∧
      1/2+3*c ≤ (1-2*ε)*Real.sqrt β := by
  have hβ0 : 0 < β := by linarith
  have hs0 : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  have hs : 1/2 < Real.sqrt β := by
    nlinarith [Real.sq_sqrt hβ0.le]
  let c := (Real.sqrt β-1/2)/12
  let ε := c/Real.sqrt β
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < ε := div_pos hc hs0
  have hehalf : ε ≤ 1/2 := by
    dsimp [ε]
    apply (div_le_iff₀ hs0).mpr
    dsimp [c]
    linarith
  refine ⟨ε,c,he,hehalf,hc,?_⟩
  have hemul : ε*Real.sqrt β = c := by
    dsimp [ε]
    exact div_mul_cancel₀ _ hs0.ne'
  dsimp [c] at hc ⊢
  dsimp [c] at hemul
  nlinarith

#print axioms exists_escape_parameters
end UCEscape
