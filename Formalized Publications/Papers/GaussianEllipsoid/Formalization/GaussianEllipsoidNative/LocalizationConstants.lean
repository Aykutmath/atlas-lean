import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GaussianEllipsoid.Localized

/-- The even row dimension loses less than two coordinates from d/2. -/
theorem even_rows_bounds (d : ℕ) (hd : 12 ≤ d) :
    0 < 2*(d/4) ∧ 2*(2*(d/4)) ≤ d ∧ d ≤ 3*(2*(d/4)) := by omega

/-- Conservative constant retaining the paper's 1280 after even-dimension
rounding. The only ratio needed is d/r≤3. -/
theorem dimension_three_halves_le {d r : ℝ} (hd : 0 ≤ d) (hr : 0 < r)
    (hdr : d ≤ 3*r) : (3/2:ℝ)*d*Real.sqrt d ≤ 8*r*Real.sqrt r := by
  have hsr := Real.sqrt_nonneg r
  have hsd := Real.sqrt_nonneg d
  have hs : Real.sqrt d ≤ (16/9:ℝ)*Real.sqrt r := by
    apply (sq_le_sq₀ hsd (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hd, Real.sq_sqrt hr.le]
    nlinarith
  have hh := mul_le_mul hdr hs hsd (by positivity : 0 ≤ 3*r)
  nlinarith

theorem localized_probability_base_le {c β σ d r : ℝ}
    (hc : 0 < c) (hβ : 0 < β) (hβσ : β ≤ σ) (hd : 0 ≤ d)
    (hr : 0 < r) (hdr : d ≤ 3*r) :
    160*((3*c/2)*d)*Real.sqrt d/(σ*r*Real.sqrt r) ≤ 1280*c/β := by
  have hσ : 0 < σ := lt_of_lt_of_le hβ hβσ
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  apply (div_le_iff₀ (by positivity : 0 < σ*r*Real.sqrt r)).mpr
  have hnum := mul_le_mul_of_nonneg_left (dimension_three_halves_le hd hr hdr)
    (by positivity : 0 ≤ 160*c)
  calc
    160*((3*c/2)*d)*Real.sqrt d ≤ 1280*c*(r*Real.sqrt r) := by nlinarith
    _ = (1280*c/β)*(β*(r*Real.sqrt r)) := by field_simp <;> ring
    _ ≤ (1280*c/β)*(σ*(r*Real.sqrt r)) := by gcongr
    _ = (1280*c/β)*(σ*r*Real.sqrt r) := by ring

end GaussianEllipsoid.Localized
#print axioms GaussianEllipsoid.Localized.localized_probability_base_le
