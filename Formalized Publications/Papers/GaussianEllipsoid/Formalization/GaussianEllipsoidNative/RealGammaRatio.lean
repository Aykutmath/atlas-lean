import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Tactic

noncomputable section
namespace GaussianMixedNormHelpers
/-- The real-shift Gamma-ratio bound used verbatim in paper Proposition 5.3.
Log convexity plus the Gamma recurrence proves the Jensen inequality for all
real s≥1, including half-integer powers in odd row dimensions. -/
theorem gamma_real_ratio_lower {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    y ^ s ≤ Real.Gamma (y+s) / Real.Gamma y := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsi : 0 < 1/s := by positivity
  have hsi1 : 1/s ≤ 1 := (div_le_one hs0).mpr hs
  have hconv := Real.convexOn_log_Gamma.2 hy (by linarith : 0 < y+s)
    (by linarith : 0 ≤ 1-1/s) hsi.le (by ring : (1-1/s)+(1/s)=1)
  have hid : (1-1/s)*y+(1/s)*(y+s) = y+1 := by field_simp; ring
  simp only [Function.comp_apply, smul_eq_mul] at hconv
  rw [hid, Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne'] at hconv
  have hlog : s*Real.log y ≤ Real.log (Real.Gamma (y+s)) - Real.log (Real.Gamma y) := by
    have hh := mul_le_mul_of_nonneg_left hconv hs0.le
    field_simp at hh
    nlinarith
  rw [Real.rpow_def_of_pos hy, mul_comm, ← Real.exp_log (div_pos
    (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos hy))]
  apply Real.exp_le_exp.mpr
  rwa [Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne'
    (Real.Gamma_pos_of_pos hy).ne']

theorem gamma_real_inverse_ratio_upper {y s : ℝ} (hy : 0 < y) (hs : 1 ≤ s) :
    Real.Gamma y / Real.Gamma (y+s) ≤ y ^ (-s) := by
  have h := gamma_real_ratio_lower hy hs
  have hpow := Real.rpow_pos_of_pos hy s
  have hG := Real.Gamma_pos_of_pos (show 0 < y+s by linarith)
  have hg := Real.Gamma_pos_of_pos hy
  rw [Real.rpow_neg hy.le]
  apply (div_le_iff₀ hG).mpr
  have hh := (le_div_iff₀ hg).mp h
  have hm := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hpow.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hpow.ne', one_mul] using hm

end GaussianMixedNormHelpers
#print axioms GaussianMixedNormHelpers.gamma_real_inverse_ratio_upper
