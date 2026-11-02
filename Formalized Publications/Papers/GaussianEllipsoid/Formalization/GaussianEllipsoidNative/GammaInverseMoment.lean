import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

noncomputable section
open Finset MeasureTheory Set

namespace GaussianMixedNormHelpers

/-- Exact integer-shift Gamma identity, proved directly from the Gamma recurrence. -/
theorem gamma_add_nat_eq_prod {y : ℝ} (hy : 0 < y) (s : ℕ) :
    Real.Gamma (y + s) = Real.Gamma y * ∏ k ∈ Finset.range s, (y + k) := by
  induction s with
  | zero => simp
  | succ s ih =>
      rw [Nat.cast_succ, ← add_assoc, Real.Gamma_add_one (by positivity : y + (s : ℝ) ≠ 0),
        ih, Finset.prod_range_succ]
      ring

/-- Jensen-free Gamma-ratio lower bound for integer shape increment. -/
theorem gamma_ratio_ge_pow {y : ℝ} (hy : 0 < y) (s : ℕ) :
    y ^ s ≤ Real.Gamma (y + s) / Real.Gamma y := by
  rw [gamma_add_nat_eq_prod hy]
  rw [mul_div_cancel_left₀ _ (ne_of_gt (Real.Gamma_pos_of_pos hy))]
  calc
    y ^ s = ∏ _k ∈ Finset.range s, y := by simp
    _ ≤ ∏ k ∈ Finset.range s, (y + k) := by
      apply Finset.prod_le_prod
      · intro k hk; exact hy.le
      · intro k hk; exact le_add_of_nonneg_right (Nat.cast_nonneg _)

/-- The reciprocal form used in negative Wishart determinant moments. -/
theorem gamma_inverse_ratio_le {y : ℝ} (hy : 0 < y) (s : ℕ) :
    Real.Gamma y / Real.Gamma (y + s) ≤ 1 / y ^ s := by
  have hG : 0 < Real.Gamma (y + s) := Real.Gamma_pos_of_pos (by positivity)
  have hg : 0 < Real.Gamma y := Real.Gamma_pos_of_pos hy
  have hp : 0 < y ^ s := pow_pos hy _
  apply (div_le_div_iff₀ hG hp).2
  have h := (le_div_iff₀ hg).1 (gamma_ratio_ge_pow hy s)
  simpa [mul_comm] using h

/-- A positive-shape gamma density at unit scale, written as a real integrand. -/
def gammaKernel (α x : ℝ) : ℝ :=
  (Real.Gamma α)⁻¹ * (x ^ (α - 1) * Real.exp (-x))

theorem gammaKernel_integral_eq_one {α : ℝ} (hα : 0 < α) :
    (∫ x : ℝ in Ioi 0, gammaKernel α x) = 1 := by
  unfold gammaKernel
  rw [integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hα (show (0 : ℝ) < 1 by norm_num)
  simp only [one_mul, one_div, inv_one, Real.one_rpow, one_mul] at h
  rw [h, inv_mul_cancel₀ (ne_of_gt (Real.Gamma_pos_of_pos hα))]

/-- Exact inverse moment integral. The integrand is an actual gamma density,
not an assumed moment or a replacement probabilistic premise. -/
theorem gammaKernel_negative_nat_moment {y : ℝ} (hy : 0 < y) (s : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) * gammaKernel (y + s) x) =
      Real.Gamma y / Real.Gamma (y + s) := by
  have hfun : Set.EqOn
      (fun x : ℝ => x ^ (-(s : ℝ)) * gammaKernel (y + s) x)
      (fun x : ℝ => (Real.Gamma (y + s))⁻¹ * (x ^ (y - 1) * Real.exp (-x)))
      (Ioi 0) := by
    intro x hx
    have hpow : x ^ (-(s : ℝ)) * x ^ (y + s - 1) = x ^ (y - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    unfold gammaKernel
    calc
      _ = (Real.Gamma (y + s))⁻¹ *
          ((x ^ (-(s : ℝ)) * x ^ (y + s - 1)) * Real.exp (-x)) := by ring
      _ = _ := by rw [hpow]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hy (show (0 : ℝ) < 1 by norm_num)
  simp only [one_mul, one_div, inv_one, Real.one_rpow, one_mul] at h
  rw [h]
  ring

/-- Uniform negative integer moment bound at every positive residual shape. -/
theorem gammaKernel_negative_nat_moment_le {y : ℝ} (hy : 0 < y) (s : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) * gammaKernel (y + s) x) ≤ 1 / y ^ s := by
  rw [gammaKernel_negative_nat_moment hy]
  exact gamma_inverse_ratio_le hy s


/-- Shape-parametrized chi-square density: the degrees of freedom are twice α. -/
def chiSquareKernel (α x : ℝ) : ℝ :=
  (2 ^ α * Real.Gamma α)⁻¹ * (x ^ (α - 1) * Real.exp (-(x / 2)))

theorem chiSquareKernel_integral_eq_one {α : ℝ} (hα : 0 < α) :
    (∫ x : ℝ in Ioi 0, chiSquareKernel α x) = 1 := by
  unfold chiSquareKernel
  rw [integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hα (show (0 : ℝ) < 1 / 2 by norm_num)
  norm_num only [one_div_div] at h
  have hf : (fun x : ℝ => x ^ (α - 1) * Real.exp (-(x / 2))) =
      (fun x : ℝ => x ^ (α - 1) * Real.exp (-(1 / 2 * x))) := by
    ext x
    congr 2
    ring
  rw [hf, h]
  exact inv_mul_cancel₀ (mul_ne_zero
    (ne_of_gt (Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) α))
    (ne_of_gt (Real.Gamma_pos_of_pos hα)))

/-- Exact chi-square inverse integer moment, proved by the Gamma integral. -/
theorem chiSquareKernel_negative_nat_moment {y : ℝ} (hy : 0 < y) (s : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) * chiSquareKernel (y + s) x) =
      ((2 : ℝ) ^ s)⁻¹ * (Real.Gamma y / Real.Gamma (y + s)) := by
  have hfun : Set.EqOn
      (fun x : ℝ => x ^ (-(s : ℝ)) * chiSquareKernel (y + s) x)
      (fun x : ℝ => (2 ^ (y + s) * Real.Gamma (y + s))⁻¹ *
        (x ^ (y - 1) * Real.exp (-(1 / 2 * x))))
      (Ioi 0) := by
    intro x hx
    have hpow : x ^ (-(s : ℝ)) * x ^ (y + s - 1) = x ^ (y - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    dsimp only [chiSquareKernel]
    rw [show x / 2 = 1 / 2 * x by ring]
    calc
      _ = (2 ^ (y + s) * Real.Gamma (y + s))⁻¹ *
          ((x ^ (-(s : ℝ)) * x ^ (y + s - 1)) * Real.exp (-(1 / 2 * x))) := by ring
      _ = _ := by rw [hpow]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hy (show (0 : ℝ) < 1 / 2 by norm_num)
  norm_num only [one_div_div] at h
  rw [h]
  rw [Real.rpow_add (show (0 : ℝ) < 2 by norm_num), Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ y ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp

/-- In the Bartlett product, residual shape k/2 contributes at most k^(-s). -/
theorem chiSquareKernel_negative_nat_moment_le {k : ℝ} (hk : 0 < k) (s : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) * chiSquareKernel (k / 2 + s) x) ≤
      1 / k ^ s := by
  rw [chiSquareKernel_negative_nat_moment (by linarith : 0 < k / 2)]
  calc
    _ ≤ ((2 : ℝ) ^ s)⁻¹ * (1 / (k / 2) ^ s) :=
      mul_le_mul_of_nonneg_left (gamma_inverse_ratio_le (by linarith : 0 < k / 2) s)
        (by positivity)
    _ = _ := by
      rw [div_pow]
      field_simp


/-- The full Bartlett inverse-moment product, before the final exponential
factorial estimate. This is exactly the factor product for even dimension r=2s. -/
theorem chiSquareKernel_negative_nat_product_le (r s : ℕ) :
    (∏ k ∈ Finset.range r,
      (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) *
        chiSquareKernel (((k : ℝ) + 1) / 2 + s) x)) ≤
      1 / ((r.factorial : ℝ) ^ s) := by
  have hprod : (∏ k ∈ Finset.range r, ((k : ℝ) + 1)) = (r.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial r
  calc
    _ ≤ ∏ k ∈ Finset.range r, 1 / (((k : ℝ) + 1) ^ s) := by
      apply Finset.prod_le_prod
      · intro k hk
        rw [chiSquareKernel_negative_nat_moment (by positivity : 0 < ((k : ℝ) + 1) / 2)]
        positivity
      · intro k hk
        exact chiSquareKernel_negative_nat_moment_le (by positivity) s
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const_one, Finset.prod_pow, hprod]


/-- The elementary exponential-series term supplies the required factorial
estimate with no Stirling asymptotics. -/
theorem scaled_factorial_ratio_le (r : ℕ) :
    (2 * (r : ℝ)) ^ r / (r.factorial : ℝ) ≤ (2 * Real.exp 1) ^ r := by
  calc
    _ = (2 : ℝ) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by rw [mul_pow]; ring
    _ ≤ (2 : ℝ) ^ r * Real.exp (r : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (r : ℝ) (Nat.cast_nonneg r) r)
        (by positivity)
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul]
      simp

/-- Final inverse-determinant factor bound after scaling W=(2r)⁻¹GGᵀ.
When r=2s, the exponent r*s is r²/2 as required by the small-ball calculation. -/
theorem scaled_chiSquareKernel_negative_nat_product_le (r s : ℕ) :
    (2 * (r : ℝ)) ^ (r * s) *
      (∏ k ∈ Finset.range r,
        (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) *
          chiSquareKernel (((k : ℝ) + 1) / 2 + s) x)) ≤
      (2 * Real.exp 1) ^ (r * s) := by
  calc
    _ ≤ (2 * (r : ℝ)) ^ (r * s) * (1 / (r.factorial : ℝ) ^ s) :=
      mul_le_mul_of_nonneg_left (chiSquareKernel_negative_nat_product_le r s)
        (by positivity)
    _ = ((2 * (r : ℝ)) ^ r / (r.factorial : ℝ)) ^ s := by
      rw [div_pow, ← pow_mul]
      ring
    _ ≤ ((2 * Real.exp 1) ^ r) ^ s :=
      pow_le_pow_left₀ (by positivity) (scaled_factorial_ratio_le r) s
    _ = _ := by rw [pow_mul]

end GaussianMixedNormHelpers
