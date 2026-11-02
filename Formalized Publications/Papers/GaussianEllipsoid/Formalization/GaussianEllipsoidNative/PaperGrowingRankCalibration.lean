import UCGaussianAspectCalibration

noncomputable section
open MeasureTheory ProbabilityTheory
namespace UCEscape

/-- Effective dimension calibration, uniform over growing nuisance rank M. -/
theorem effective_aspect_numeric_calibration_eventually (αm αp β ε c θ : ℝ)
    (hαm : 0 < αm) (hαp : 0 < αp) (hβ : 0 < β)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hc : 0 < c)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmargin : 1 / 2 + 3 * c ≤ (1 - 2 * ε) * Real.sqrt β)
    (hslack : 0 < αm - θ * αp - β)
    (hent : αp * (θ * (1 - Real.log θ)) ≤ ε^2 * β / 16)
    (q : ℝ) (hq : 0 < q) :
    ∃ D : ℕ, ∀ d ≥ D, ∀ n M : ℕ,
      αm * (d : ℝ)^2 ≤ (n:ℝ)-(M:ℝ) → (n : ℝ) ≤ αp * (d : ℝ)^2 →
      let k := Nat.floor (θ * n)
      let r := n - M - k
      0 < n ∧ 0 < d ∧ 0 < r ∧ r + M + k ≤ n ∧
      θ * (n : ℝ) ≤ (k : ℝ) + 1 ∧
      (c / (2 * Real.sqrt αp)) * Real.sqrt n < c * d ∧
      c * d + c * d ≤
        (1 - ε) * Real.sqrt r *
          (1 - ((deletedCoordinateSets n k).card : ℝ) * Real.exp (-ε^2 * (r : ℝ) / 8)) -
        Real.sqrt ((d : ℝ) * (d + 1) / 4) ∧
      Real.pi^2 / (8 * (c * d)^2) ≤ q := by
  obtain ⟨Dcard, hDcard⟩ := real_budget_eventually_quadratic (-Real.log ε)
    (ε^2 * β / 16) (by positivity)
  obtain ⟨Dlin, hDlin⟩ := exists_nat_gt (1 / (4 * c))
  obtain ⟨Dprob, hDprob⟩ := real_budget_eventually_quadratic
    (Real.pi^2 / (8 * c^2 * q)) 1 (by norm_num)
  refine ⟨1 + Dcard + Dlin + Dprob, ?_⟩
  intro d hd n M heffective hnhi
  have hnlo : αm*(d:ℝ)^2 ≤ n := heffective.trans (sub_le_self _ (Nat.cast_nonneg M))
  let k := Nat.floor (θ * n)
  let r := n - M - k
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos
  have hk : (k : ℝ) ≤ θ * n := Nat.floor_le (by positivity)
  have hbudget : (M:ℝ)+(k:ℝ)+β*(d:ℝ)^2 ≤ n := by
    have hh := mul_le_mul_of_nonneg_left hnhi hθ.le
    have hg := mul_nonneg hslack.le (sq_nonneg (d:ℝ))
    nlinarith
  have hMk : M+k ≤ n := by
    have hh : (M:ℝ)+(k:ℝ) ≤ n := by nlinarith [mul_nonneg hβ.le (sq_nonneg (d:ℝ))]
    exact_mod_cast hh
  have hr : β * (d : ℝ)^2 ≤ (r : ℝ) := by
    have hM : M ≤ n := by omega
    have hk' : k ≤ n-M := by omega
    dsimp [r]
    rw [Nat.cast_sub hk', Nat.cast_sub hM]
    linarith
  have hrpos : 0 < r := by
    have hp : (0 : ℝ) < r := (mul_pos hβ (sq_pos_of_pos hdR)).trans_le hr
    exact_mod_cast hp
  have hnpos : 0 < n := by
    have hp : (0 : ℝ) < n := (mul_pos hαm (sq_pos_of_pos hdR)).trans_le hnlo
    exact_mod_cast hp
  have hdim : r + M + k ≤ n := by dsimp [r]; omega
  have hθk : θ * (n : ℝ) ≤ (k : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hsαp : 0 < Real.sqrt αp := Real.sqrt_pos.mpr hαp
  have hsn : Real.sqrt n ≤ Real.sqrt αp * (d : ℝ) := by
    have h := Real.sqrt_le_sqrt hnhi
    rw [Real.sqrt_mul hαp.le, Real.sqrt_sq hdR.le] at h
    exact h
  have ha : 0 ≤ c / (2 * Real.sqrt αp) := by positivity
  have hgap : (c / (2 * Real.sqrt αp)) * Real.sqrt n < c * d := by
    have hm := mul_le_mul_of_nonneg_left hsn ha
    have heq : (c / (2 * Real.sqrt αp)) * (Real.sqrt αp * (d : ℝ)) = c * d / 2 := by
      field_simp
    rw [heq] at hm
    nlinarith [mul_pos hc hdR]
  have hlin : 1 / 4 ≤ c * (d : ℝ) := by
    have hdc : (Dlin : ℝ) ≤ d := by exact_mod_cast (show Dlin ≤ d by omega)
    have hx : 1 / (4 * c) ≤ (d : ℝ) := le_of_lt (hDlin.trans_le hdc)
    have hm := (div_le_iff₀ (show 0 < 4 * c by positivity)).mp hx
    nlinarith
  have hcard := deleted_card_exponential_le αp β ε θ hβ.le hε hθ hθ1 hnhi hr hk hent
    (hDcard d (by omega))
  have hm := retained_gaussian_mean_margin β ε c hβ.le hε.le hεhalf hr hmargin hlin hcard
  have hprob : Real.pi^2 / (8 * (c * d)^2) ≤ q := by
    have hlarge : Real.pi^2 / (8 * c^2 * q) ≤ (d : ℝ)^2 := by
      simpa using hDprob d (by omega)
    have hm := (div_le_iff₀ (show 0 < 8 * c^2 * q by positivity)).mp hlarge
    apply (div_le_iff₀ (show 0 < 8 * (c * (d : ℝ))^2 by positivity)).mpr
    nlinarith
  exact ⟨hnpos, hdpos, hrpos, hdim, hθk, hgap, hm, hprob⟩


#print axioms effective_aspect_numeric_calibration_eventually
end UCEscape
