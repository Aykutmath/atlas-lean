import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Explicit conversion of the independently proved real-Gaussian moment tail
into the constant-threshold and exponential form used in manuscript line 2750. -/
noncomputable section
namespace AHHGaussian

theorem normalized_four_tail_threshold (h K : ℕ) (hh : 0 < h) :
    (4 * (2048 : ℝ) * (h + K * h : ℕ)^2) / (h : ℝ)^2 =
      8192 * (1 + (K : ℝ))^2 := by
  have hn : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  push_cast
  field_simp
  ring

/-- A fixed aspect bound is covered by a fixed integer K, uniformly in both
sample size and local dimension.  The witness is chosen before n and h. -/
theorem aspect_integer_cover (A : ℝ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ n h : ℕ, (n : ℝ) ≤ A * (h : ℝ)^2 → n ≤ (K*h)^2 := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max A 1)
  have hAK : A < (K : ℝ) := (le_max_left A 1).trans_lt hK
  have hK1 : (1 : ℝ) < K := (le_max_right A 1).trans_lt hK
  have hA2 : A ≤ (K : ℝ)^2 := by nlinarith
  refine ⟨K, by exact_mod_cast hK1.le, ?_⟩
  intro n h hn
  have hb : (n : ℝ) ≤ ((K : ℝ) * (h : ℝ))^2 := by
    calc
      (n : ℝ) ≤ A * (h : ℝ)^2 := hn
      _ ≤ (K : ℝ)^2 * (h : ℝ)^2 := mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  exact_mod_cast hb

/-- Exact exponent: the logarithmic loss is explicit rather than a hidden
asymptotic premise. -/
theorem four_gaussian_error_eq_exp (h : ℕ) (hh : 0 < h) :
    4 * (h : ℝ)^2 / (2 : ℝ)^h =
      Real.exp (-Real.log 2 * h + 2 * Real.log h + Real.log 4) := by
  have hr : (0 : ℝ) < h := by exact_mod_cast hh
  rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  have h1 : Real.exp (-Real.log 2 * (h : ℝ)) = ((2 : ℝ)^h)⁻¹ := by
    rw [show -Real.log 2 * (h : ℝ) = -((h : ℝ) * Real.log 2) by ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have h2 : Real.exp (2 * Real.log (h : ℝ)) = (h : ℝ)^2 := by
    rw [show (2 : ℝ) * Real.log (h : ℝ) = (2 : ℕ) * Real.log (h : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hr]
  rw [h1, h2]
  ring

/-- Literal exp(-c h + O(log h)) with c=log 2>0 and remainder ≤4 log h
for every h≥2. -/
theorem four_gaussian_error_le_exp (h : ℕ) (hh : 2 ≤ h) :
    4 * (h : ℝ)^2 / (2 : ℝ)^h ≤
      Real.exp (-Real.log 2 * h + 4 * Real.log h) := by
  rw [four_gaussian_error_eq_exp h (by omega)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log (2 : ℝ) ≤ Real.log (h : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hh)
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [hl4]
  linarith

/-- Explicit floor-dimension conversion for the source choice h=⌊d/2⌋. -/
theorem half_dimension_error_le_exp (d : ℕ) (hd : 4 ≤ d) :
    4 * (d/2 : ℕ)^2 / (2 : ℝ)^(d/2) ≤
      Real.exp (-(Real.log 2 / 2) * d + 4 * Real.log d + Real.log 2) := by
  have hh : 2 ≤ d/2 := by omega
  apply (four_gaussian_error_le_exp (d/2) hh).trans
  apply Real.exp_le_exp.mpr
  have hlog : Real.log ((d/2 : ℕ) : ℝ) ≤ Real.log (d : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < d/2 by omega))
      (by exact_mod_cast Nat.div_le_self d 2)
  have hfloor : (d : ℝ) ≤ 2 * ((d/2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show d ≤ 2 * (d/2) + 1 by omega)
  have hc : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  nlinarith

/-- Eventual dimensions automatically enter the h≥2 range required above. -/
theorem half_dimension_eventually_ge_two :
    ∀ᶠ d : ℕ in Filter.atTop, 2 ≤ d / 2 := by
  filter_upwards [Filter.eventually_ge_atTop 4] with d hd
  omega

theorem exponential_decay_constant_positive : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

#print axioms normalized_four_tail_threshold
#print axioms aspect_integer_cover
#print axioms four_gaussian_error_eq_exp
#print axioms four_gaussian_error_le_exp
#print axioms half_dimension_error_le_exp
end AHHGaussian
