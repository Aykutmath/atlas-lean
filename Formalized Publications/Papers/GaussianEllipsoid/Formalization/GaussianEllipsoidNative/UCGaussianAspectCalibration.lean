import UCDeletedGaussianMean
import UCEscapeParameters
import UCRetainedDimension
import UCEscapeMacroscopic
import UCGaussianLossEvent

noncomputable section
open MeasureTheory ProbabilityTheory
namespace UCEscape

/-- A real-valued budget is eventually dominated by a positive quadratic rate. -/
theorem real_budget_eventually_quadratic (B γ : ℝ) (hγ : 0 < γ) :
    ∃ D : ℕ, ∀ d ≥ D, B ≤ γ * (d : ℝ)^2 := by
  obtain ⟨D, hD⟩ := fixed_rank_eventually_negligible (Nat.ceil B) γ hγ
  exact ⟨D, fun d hd => (Nat.le_ceil B).trans (hD d hd)⟩

/-- Aspect-ratio constants leave strictly positive room for nuisance dimensions,
small coordinate deletion, and the PSD Gaussian width. -/
theorem exists_aspect_escape_constants (αm αp : ℝ)
    (hαm : 1 / 4 < αm) (hαp : αm ≤ αp) :
    ∃ β ε c θ : ℝ,
      1 / 4 < β ∧ β < αm ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧ 0 < c ∧
      0 < θ ∧ θ ≤ 1 ∧
      1 / 2 + 3 * c ≤ (1 - 2 * ε) * Real.sqrt β ∧
      0 < αm - θ * αp - β ∧
      αp * (θ * (1 - Real.log θ)) ≤ ε ^ 2 * β / 16 := by
  let β := (αm + 1 / 4) / 2
  have hβ : 1 / 4 < β := by dsimp [β]; linarith
  have hβα : β < αm := by dsimp [β]; linarith
  have hβ0 : 0 < β := by linarith
  have hαp0 : 0 < αp := by linarith
  obtain ⟨ε, c, hε, hεhalf, hc, hmargin⟩ := exists_escape_parameters β hβ
  let η := min ((αm - β) / (2 * αp)) (ε ^ 2 * β / (16 * αp))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨θ, hθ, hθ1, hrate⟩ := exists_small_deletion_entropy η hη
  have hlog : Real.log θ ≤ 0 := Real.log_nonpos hθ.le hθ1
  have hθrate : θ ≤ θ * (1 - Real.log θ) := by nlinarith
  have hbudget : θ * (1 - Real.log θ) ≤ (αm - β) / (2 * αp) :=
    hrate.trans (min_le_left _ _)
  have hentropy : θ * (1 - Real.log θ) ≤ ε ^ 2 * β / (16 * αp) :=
    hrate.trans (min_le_right _ _)
  refine ⟨β, ε, c, θ, hβ, hβα, hε, hεhalf, hc, hθ, hθ1, hmargin, ?_, ?_⟩
  · have hb := (le_div_iff₀ (show 0 < 2 * αp by positivity)).mp hbudget
    nlinarith [mul_le_mul_of_nonneg_right hθrate hαp0.le]
  · have he := (le_div_iff₀ (show 0 < 16 * αp by positivity)).mp hentropy
    nlinarith

/-- The actual deletion-family exponential factor is eventually small under
numerical aspect and entropy budgets. -/
theorem deleted_card_exponential_le {n d r k : ℕ}
    (αp β ε θ : ℝ) (hβ : 0 ≤ β) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hn : (n : ℝ) ≤ αp * (d : ℝ)^2)
    (hr : β * (d : ℝ)^2 ≤ r) (hk : (k : ℝ) ≤ θ * n)
    (hent : αp * (θ * (1 - Real.log θ)) ≤ ε^2 * β / 16)
    (hlarge : -Real.log ε ≤ (ε^2 * β / 16) * (d : ℝ)^2) :
    ((deletedCoordinateSets n k).card : ℝ) * Real.exp (-ε^2 * (r : ℝ) / 8) ≤ ε := by
  have hlog : Real.log θ ≤ 0 := Real.log_nonpos hθ.le hθ1
  have hrate : 0 ≤ θ * (1 - Real.log θ) := mul_nonneg hθ.le (by linarith)
  have hnc := mul_le_mul_of_nonneg_right hn hrate
  have hec := mul_le_mul_of_nonneg_right hent (sq_nonneg (d : ℝ))
  have hr' := mul_le_mul_of_nonneg_left hr (sq_nonneg ε)
  have hexp : (n : ℝ) * θ * (1 - Real.log θ) - ε^2 * (r : ℝ) / 8 ≤ Real.log ε := by
    nlinarith
  calc
    _ ≤ Real.exp ((n : ℝ) * θ * (1 - Real.log θ)) *
        Real.exp (-ε^2 * (r : ℝ) / 8) :=
      mul_le_mul_of_nonneg_right (deletedCoordinateSets_card_le_exp n k θ hθ hθ1 hk)
        (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * θ * (1 - Real.log θ) - ε^2 * (r : ℝ) / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr hexp
    _ = ε := Real.exp_log hε

/-- Numerical conversion of retained norm mean to a two-sided linear escape margin. -/
theorem retained_gaussian_mean_margin {d r k n : ℕ}
    (β ε c : ℝ) (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hεhalf : ε ≤ 1 / 2)
    (hr : β * (d : ℝ)^2 ≤ r)
    (hmargin : 1 / 2 + 3 * c ≤ (1 - 2 * ε) * Real.sqrt β)
    (hdlarge : 1 / 4 ≤ c * (d : ℝ))
    (hcard : ((deletedCoordinateSets n k).card : ℝ) *
      Real.exp (-ε^2 * (r : ℝ) / 8) ≤ ε) :
    c * (d : ℝ) + c * (d : ℝ) ≤
      (1 - ε) * Real.sqrt r *
        (1 - ((deletedCoordinateSets n k).card : ℝ) * Real.exp (-ε^2 * (r : ℝ) / 8)) -
      Real.sqrt ((d : ℝ) * (d + 1) / 4) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hs : Real.sqrt β * (d : ℝ) ≤ Real.sqrt (r : ℝ) := by
    have h := Real.sqrt_le_sqrt hr
    rw [Real.sqrt_mul hβ, Real.sqrt_sq hd0] at h
    exact h
  have hw : Real.sqrt ((d : ℝ) * (d + 1) / 4) ≤ (d : ℝ) / 2 + 1 / 4 := by
    have hnon : 0 ≤ (d : ℝ) * (d + 1) / 4 := by positivity
    nlinarith [Real.sq_sqrt hnon, Real.sqrt_nonneg ((d : ℝ) * (d + 1) / 4)]
  have hcoeff : 0 ≤ 1 - 2 * ε := by linarith
  have hmean : (1 - 2 * ε) * Real.sqrt r ≤
      (1 - ε) * Real.sqrt r *
        (1 - ((deletedCoordinateSets n k).card : ℝ) * Real.exp (-ε^2 * (r : ℝ) / 8)) := by
    have h := mul_le_mul_of_nonneg_left (sub_le_sub_left hcard 1)
      (mul_nonneg (by linarith : 0 ≤ 1 - ε) (Real.sqrt_nonneg (r : ℝ)))
    nlinarith [mul_nonneg (sq_nonneg ε) (Real.sqrt_nonneg (r : ℝ))]
  have hdim := mul_le_mul_of_nonneg_right hmargin hd0
  have hnorm := mul_le_mul_of_nonneg_left hs hcoeff
  nlinarith

/-- Full numerical calibration uniform over the sample-size aspect interval.
Only the eventual dimension cutoff depends on the fixed nuisance rank M and
requested failure mass q; all loss/escape/deletion constants are fixed earlier. -/
theorem aspect_numeric_calibration_eventually (αm αp β ε c θ : ℝ)
    (hαm : 0 < αm) (hαp : 0 < αp) (hβ : 0 < β)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hc : 0 < c)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hmargin : 1 / 2 + 3 * c ≤ (1 - 2 * ε) * Real.sqrt β)
    (hslack : 0 < αm - θ * αp - β)
    (hent : αp * (θ * (1 - Real.log θ)) ≤ ε^2 * β / 16)
    (M : ℕ) (q : ℝ) (hq : 0 < q) :
    ∃ D : ℕ, ∀ d ≥ D, ∀ n : ℕ,
      αm * (d : ℝ)^2 ≤ n → (n : ℝ) ≤ αp * (d : ℝ)^2 →
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
  obtain ⟨Ddim, hDdim⟩ := fixed_rank_eventually_negligible M (αm - θ * αp - β) hslack
  obtain ⟨Dcard, hDcard⟩ := real_budget_eventually_quadratic (-Real.log ε)
    (ε^2 * β / 16) (by positivity)
  obtain ⟨Dlin, hDlin⟩ := exists_nat_gt (1 / (4 * c))
  obtain ⟨Dprob, hDprob⟩ := real_budget_eventually_quadratic
    (Real.pi^2 / (8 * c^2 * q)) 1 (by norm_num)
  refine ⟨1 + Ddim + Dcard + Dlin + Dprob, ?_⟩
  intro d hd n hnlo hnhi
  let k := Nat.floor (θ * n)
  let r := n - M - k
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos
  have hk : (k : ℝ) ≤ θ * n := Nat.floor_le (by positivity)
  have hMk := retained_rank_ge n d M k αm αp β θ hβ.le hθ.le hnlo hnhi hk
    (hDdim d (by omega))
  have hr : β * (d : ℝ)^2 ≤ (r : ℝ) := hMk.2
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

/-- Uniform-aspect actual Gaussian bounded-loss good event. The positive constants
a, theta, c depend only on the fixed aspect interval; the dimension cutoff may
depend on the fixed nuisance-rank bound and the requested positive failure mass. -/
theorem exists_uniform_aspect_gaussian_loss_good_event (αm αp : ℝ)
    (hαm : 1 / 4 < αm) (hαp : αm ≤ αp) :
    ∃ a θ c : ℝ, 0 < a ∧ 0 < θ ∧ 0 < c ∧
      ∀ M : ℕ, ∀ q : ℝ, 0 < q → ∃ D : ℕ,
        ∀ d ≥ D, ∀ n : ℕ,
          αm * (d : ℝ)^2 ≤ n → (n : ℝ) ≤ αp * (d : ℝ)^2 →
          ∀ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), Module.finrank ℝ L ≤ M →
          ∃ G : Set (BMSaddle.Raw n d), MeasurableSet G ∧
            (BMSaddle.rawSourceLaw n d).real Gᶜ ≤ Real.pi^2 / (8 * (c * d)^2) ∧
            (BMSaddle.rawSourceLaw n d).real Gᶜ ≤ q ∧
            ∀ z ∈ G, ∀ A : GaussianEllipsoid.Square d,
              A.PosSemidef → GaussianEllipsoid.frobeniusNorm A = 1 →
              ∀ v : EuclideanSpace ℝ (Fin n), v ∈ L →
                θ * BMClippedL1Bridge.smoothLoss a ≤
                  (∑ i, BMClippedL1Bridge.smoothLoss
                    (GaussianEllipsoid.UCNormalizedRows.gaussianRow A (z i) - v i)) / (n : ℝ) := by
  obtain ⟨β, ε, c, θ, hβ, hβα, hε, hεhalf, hc, hθ, hθ1, hmargin, hslack, hent⟩ :=
    exists_aspect_escape_constants αm αp hαm hαp
  have hαm0 : 0 < αm := by linarith
  have hαp0 : 0 < αp := by linarith
  have hβ0 : 0 < β := by linarith
  let a := c / (2 * Real.sqrt αp)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a, θ, c, ha, hθ, hc, ?_⟩
  intro M q hq
  obtain ⟨D, hD⟩ := aspect_numeric_calibration_eventually αm αp β ε c θ hαm0 hαp0 hβ0
    hε hεhalf hc hθ hθ1 hmargin hslack hent M q hq
  refine ⟨D, ?_⟩
  intro d hd n hnlo hnhi L hL
  obtain ⟨hnpos, hdpos, hrpos, hdim, hθk, hgap, hmean, hprob⟩ := hD d hd n hnlo hnhi
  let k := Nat.floor (θ * n)
  let r := n - M - k
  have hdimL : r + Module.finrank ℝ L + k ≤ n := by dsimp [r, k]; omega
  obtain ⟨G, hG, htail, hfloor⟩ := exists_gaussian_loss_good_event (r := r) (k := k)
    hnpos hdpos hrpos L hdimL ε a θ (c * d) (c * d) hε.le (by linarith) ha.le
    (mul_pos hc (Nat.cast_pos.mpr hdpos)) hgap hθk hmean
  exact ⟨G, hG, htail, htail.trans hprob, hfloor⟩

#print axioms exists_uniform_aspect_gaussian_loss_good_event
#print axioms exists_aspect_escape_constants
#print axioms deleted_card_exponential_le
#print axioms aspect_numeric_calibration_eventually
end UCEscape
