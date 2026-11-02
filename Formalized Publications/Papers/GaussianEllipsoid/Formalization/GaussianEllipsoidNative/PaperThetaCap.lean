import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-! Reconstructed from preserved consumer interfaces on 2026-10-03.
This is new source, not a recovered original. -/
noncomputable section
namespace GaussianEllipsoid.SmallBall

theorem paper_theta_sq_lt_half {θ : ℝ} (hθ0 : 0 < θ)
    (hθ : θ < 1 / Real.sqrt 2) : θ^2 < (1/2 : ℝ) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsq : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hm : θ * Real.sqrt 2 < 1 := (lt_div_iff₀ hs).mp hθ
  have hp : 0 < θ * Real.sqrt 2 := mul_pos hθ0 hs
  have hpow : (θ * Real.sqrt 2)^2 < 1^2 := by nlinarith
  rw [mul_pow, hsq] at hpow
  nlinarith

theorem squared_coordinate_cap_of_paper_theta {r n : ℕ} (hr : 0 < r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1 / Real.sqrt 2)
    (z : Fin n → ℝ) (hz : Real.sqrt (r : ℝ) * ‖z‖ ≤ θ) :
    ∀ i, (z i)^2 ≤ (2 * (r : ℝ))⁻¹ := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  intro i
  have hi : |z i| ≤ ‖z‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  have hprod := (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)).trans hz
  have hsq := pow_le_pow_left₀
    (by positivity : 0 ≤ Real.sqrt (r : ℝ) * |z i|) hprod 2
  rw [mul_pow, Real.sq_sqrt hrR.le, sq_abs] at hsq
  have hhalf := paper_theta_sq_lt_half hθ0 hθ
  rw [inv_eq_one_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mpr
  nlinarith

end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.paper_theta_sq_lt_half
#print axioms GaussianEllipsoid.SmallBall.squared_coordinate_cap_of_paper_theta
