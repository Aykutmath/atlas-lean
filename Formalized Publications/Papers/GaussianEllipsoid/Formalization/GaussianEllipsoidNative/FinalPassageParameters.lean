import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
Explicit numerical parameters for Section 11.
The transcendental and arithmetic conclusions in this file are unconditional.
Their use in MixedNormBound requires the independently proved sparse estimate
with mu = 2^(-30) and continuity event with L = 96.
-/

noncomputable section

namespace GaussianEllipsoidFinalPassage

def numericalEta : ℝ := (1 / 2 : ℝ) ^ 50
def numericalBeta : ℝ := 2 * numericalEta
def numericalDlog : ℝ := 1 + 2 * Real.log (1 / numericalEta)

theorem numerical_eta_range :
    0 < numericalEta ∧ numericalEta < 1 ∧ numericalEta ≤ 1 / 16 := by
  norm_num [numericalEta]

theorem numerical_beta_range :
    0 < numericalBeta ∧ numericalBeta ≤ 1 / 2 := by
  norm_num [numericalBeta, numericalEta]

theorem numerical_log_identity :
    Real.log (1 / numericalEta) = 50 * Real.log 2 := by
  unfold numericalEta
  rw [one_div, Real.log_inv, Real.log_pow]
  norm_num [Real.log_div]

theorem numerical_Dlog_identity :
    numericalDlog = 1 + 100 * Real.log 2 := by
  unfold numericalDlog
  rw [numerical_log_identity]
  ring

theorem numerical_Dlog_bounds :
    0 < numericalDlog ∧ numericalDlog ≤ 101 ∧ numericalDlog ≤ 128 := by
  rw [numerical_Dlog_identity]
  have hlogNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogUpper : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  constructor
  · linarith
  constructor <;> linarith

/-- Sparse mu = 2^-30 and Dlog ≤ 128 give cH ≥ 2^-37. -/
theorem numerical_head_coefficient {cH : ℝ}
    (hhead : (1 / 2 : ℝ) ^ 30 ≤ cH * numericalDlog) :
    (1 / 2 : ℝ) ^ 37 ≤ cH := by
  obtain ⟨hDpos, _, hDupper⟩ := numerical_Dlog_bounds
  have hcH : 0 ≤ cH := by
    by_contra h
    have hneg : cH * numericalDlog < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge h) hDpos
    norm_num at hhead
    linarith
  have hbound := mul_le_mul_of_nonneg_left hDupper hcH
  norm_num at hhead ⊢
  linarith

/-- Completely explicit absorption with eta = 2^-50 and L = 96. -/
theorem numerical_absorption {cH : ℝ}
    (hhead : (1 / 2 : ℝ) ^ 37 ≤ cH) :
    (1 / 2 : ℝ) ^ 39 ≤ cH * (1 - numericalBeta) - 96 * numericalBeta := by
  have hfactor : 0 ≤ 1 - numericalBeta := by
    norm_num [numericalBeta, numericalEta]
  have hbound := mul_le_mul_of_nonneg_right hhead hfactor
  norm_num [numericalBeta, numericalEta] at hbound ⊢
  linarith

theorem numerical_full_absorption {cH : ℝ}
    (hhead : (1 / 2 : ℝ) ^ 30 ≤ cH * numericalDlog) :
    (1 / 2 : ℝ) ^ 39 ≤ cH * (1 - numericalBeta) - 96 * numericalBeta :=
  numerical_absorption (numerical_head_coefficient hhead)

theorem numerical_final_constant_pos {cS : ℝ} (hcS : 0 < cS) :
    0 < min cS ((1 / 2 : ℝ) ^ 39) := by
  exact lt_min hcS (by norm_num)

end GaussianEllipsoidFinalPassage
