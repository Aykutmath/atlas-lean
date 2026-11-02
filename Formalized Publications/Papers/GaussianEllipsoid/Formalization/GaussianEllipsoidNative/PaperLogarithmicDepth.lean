import RetainedTailConstants
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth

/-- Literal paper depth with the numerical admissible choice T0=40. -/
def depth (K : ℝ) : ℕ := ⌈40+2*Real.log (Real.exp 1*K)/Real.log 2⌉₊

lemma depth_formula (K : ℝ) (hK : 1 ≤ K) :
    depth K=⌈40+2*(1+Real.log K)/Real.log 2⌉₊ := by
  unfold depth
  rw [Real.log_mul (Real.exp_ne_zero _) (by linarith : K≠0),Real.log_exp]

lemma depth_pos (K : ℝ) (hK : 1 ≤ K) : 0 < depth K := by
  rw [depth_formula K hK]
  have hlog := Real.log_nonneg hK
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : (0:ℝ)<40+2*(1+Real.log K)/Real.log 2 := by positivity
  exact Nat.ceil_pos.mpr h

lemma depth_le_linear (K : ℝ) (hK : 1 ≤ K) : (depth K:ℝ)≤48*K := by
  rw [depth_formula K hK]
  have hlog := Real.log_nonneg hK
  have h2 := half_le_log_two
  have h2pos : 0 < Real.log 2 := by linarith
  have hx : 0 ≤ 40+2*(1+Real.log K)/Real.log 2 := by positivity
  have hc := Nat.ceil_lt_add_one hx
  have hd : 2*(1+Real.log K)/Real.log 2 ≤ 4*(1+Real.log K) := by
    apply (div_le_iff₀ h2pos).mpr
    nlinarith
  have hlogup := Real.log_le_sub_one_of_pos (show 0<K by linarith)
  linarith

lemma retention_error_scaled_logarithmic (K : ℝ) (hK : 1 ≤ K) :
    (8*(1/2:ℝ)^(depth K))*K^2 ≤ (1/2:ℝ)^37 := by
  have hKpos : 0<K := by linarith
  have h2pos : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hceil : 40+2*(1+Real.log K)/Real.log 2 ≤ (depth K:ℝ) := by
    rw [depth_formula K hK]
    exact Nat.le_ceil _
  have hprod := (mul_le_mul_of_nonneg_right hceil h2pos.le)
  have hden : (2*(1+Real.log K)/Real.log 2)*Real.log 2=2*(1+Real.log K) :=
    div_mul_cancel₀ _ h2pos.ne'
  rw [add_mul,hden] at hprod
  have hp (m : ℕ) : (1/2:ℝ)^m=Real.exp (-(m:ℝ)*Real.log 2) := by
    rw [show -(m:ℝ)*Real.log 2=(m:ℝ)*(-Real.log 2) by ring,Real.exp_nat_mul]
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  have hKsq : K^2=Real.exp (2*Real.log K) := by
    simpa only [Nat.cast_ofNat,Real.exp_log hKpos] using (Real.exp_nat_mul (Real.log K) 2).symm
  rw [hp,hKsq]
  have he : -(depth K:ℝ)*Real.log 2+2*Real.log K ≤ -(40:ℝ)*Real.log 2 := by linarith
  calc
    8*Real.exp (-(depth K:ℝ)*Real.log 2)*Real.exp (2*Real.log K) =
        8*Real.exp (-(depth K:ℝ)*Real.log 2+2*Real.log K) := by rw [Real.exp_add]; ring
    _ ≤ 8*Real.exp (-(40:ℝ)*Real.log 2) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by norm_num)
    _ = (1/2:ℝ)^37 := by
      have h40 := hp 40
      norm_num only [Nat.cast_ofNat] at h40
      rw [← h40]
      norm_num

#print axioms retention_error_scaled_logarithmic
end GaussianEllipsoidCandidate.PaperLogarithmicDepth
