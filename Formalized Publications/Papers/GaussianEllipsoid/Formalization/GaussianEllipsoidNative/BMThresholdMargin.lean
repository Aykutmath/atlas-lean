import BMWidthAsymptotic

noncomputable section
open scoped Topology
open Filter
namespace BMGeometry

/-- Width supplies a fixed affine radius and a macroscopic expectation-Gordon margin
for every density strictly below 1/4. No Gordon inequality is assumed or reproved here. -/
theorem exists_condition_radius_margin {α : ℝ} (hα : 0 ≤ α) (hquarter : α < 1/4) :
    ∃ κ R c : ℝ, 1 ≤ κ ∧ 0 < R ∧ 0 < c ∧
      ∀ᶠ d : ℕ in atTop, ∀ n : ℕ, (n:ℝ) ≤ α*(d:ℝ)^2 →
        Real.sqrt ((n:ℝ)*(1+(R⁻¹)^2)) + c*d ≤ conditionedWidth d κ := by
  have hsα : (Real.sqrt α)^2 = α := Real.sq_sqrt hα
  have hsαnn := Real.sqrt_nonneg α
  have hsαhalf : Real.sqrt α < 1/2 := by nlinarith
  let ε : ℝ := (1/2-Real.sqrt α)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  let R : ℝ := 1+Real.sqrt α/ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hRε : Real.sqrt α ≤ ε*R := by dsimp [R]; field_simp; nlinarith
  have hquot : Real.sqrt α / R ≤ ε := (div_le_iff₀ hR).mpr hRε
  obtain ⟨κ,hκ,hwidth⟩ := exists_conditionNumber_eventually_width_lower hε
  refine ⟨κ,R,ε,hκ,hR,hε,?_⟩
  filter_upwards [hwidth, eventually_ge_atTop (1:ℕ)] with d hdwidth hd1
  intro n hn
  have hd : (0:ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ)<1) hd1)
  have hw : ((1/2:ℝ)-ε)*d < conditionedWidth d κ := (lt_div_iff₀ hd).mp hdwidth
  have hroot : Real.sqrt ((n:ℝ)*(1+(R⁻¹)^2)) ≤ (Real.sqrt α+ε)*d := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have h1 := mul_le_mul_of_nonneg_right hn (show 0 ≤ 1+(R⁻¹)^2 by positivity)
    have h2 : α*(R⁻¹)^2 ≤ ε^2 := by
      have hh := pow_le_pow_left₀ (div_nonneg hsαnn hR.le) hquot 2
      rw [div_pow, hsα] at hh
      simpa only [div_eq_mul_inv, inv_pow] using hh
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg (d:ℝ))
    have h4 := mul_nonneg (mul_nonneg hsαnn hε.le) (sq_nonneg (d:ℝ))
    nlinarith
  have hεeq : (1/2:ℝ)-Real.sqrt α = 4*ε := by dsimp [ε]; ring
  have hgap := mul_nonneg hε.le hd.le
  nlinarith

end BMGeometry
