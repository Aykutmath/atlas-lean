import BMSaddleStatistic

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid BMGeometry GaussianTensorMoments GaussianMixedNormHelpers MeasureTheory ProbabilityTheory
namespace BMSaddle

abbrev sampleLaw (n d : ℕ) := euclideanGaussianLaw (EntryIndex n d)

def statisticMean (n d : ℕ) (κ R : ℝ) : ℝ := ∫ X, statistic n d κ R X ∂sampleLaw n d

theorem statistic_continuous {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    Continuous (statistic n d κ R) := (statistic_lipschitz hn hd hκ R).continuous

theorem statistic_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    Integrable (statistic n d κ R) (sampleLaw n d) :=
  GaussianVariance.lipschitz_integrable (statistic_lipschitz hn hd hκ R)

theorem statistic_sq_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    Integrable (fun X => (statistic n d κ R X)^2) (sampleLaw n d) :=
  GaussianVariance.lipschitz_sq_integrable (statistic_lipschitz hn hd hκ R)

/-- The actual saddle statistic obeys a dimension-independent Gaussian variance bound. -/
theorem statistic_variance_le {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    variance (statistic n d κ R) (sampleLaw n d) ≤ Real.pi^2/8 :=
  GaussianVariance.lipschitz_gaussian_variance_le (statistic_lipschitz hn hd hκ R)

theorem statistic_centered_sq_le {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    (∫ X, (statistic n d κ R X-statisticMean n d κ R)^2 ∂sampleLaw n d) ≤ Real.pi^2/8 := by
  have h := statistic_variance_le hn hd hκ R
  rw [variance_eq_integral (statistic_continuous hn hd hκ R).measurable.aemeasurable] at h
  exact h

theorem statistic_centered_sq_integrable {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (R : ℝ) :
    Integrable (fun X => (statistic n d κ R X-statisticMean n d κ R)^2) (sampleLaw n d) := by
  have hc : LipschitzWith 1 (fun X => statistic n d κ R X-statisticMean n d κ R) := by
    apply LipschitzWith.of_dist_le_mul
    intro X Y
    simp only [NNReal.coe_one,one_mul,Real.dist_eq,sub_sub_sub_cancel_right]
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using (statistic_lipschitz hn hd hκ R).dist_le_mul X Y
  exact GaussianVariance.lipschitz_sq_integrable hc

/-- Chebyshev at a macroscopic positive mean; even the nonpositive event is controlled. -/
theorem statistic_nonpositive_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ R c : ℝ}
    (hκ : 1 ≤ κ) (hc : 0 < c) (hmean : c*d ≤ statisticMean n d κ R) :
    (sampleLaw n d).real {X | statistic n d κ R X ≤ 0} ≤ Real.pi^2/(8*c^2*(d:ℝ)^2) := by
  have hd' : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hcd : 0 < c*(d:ℝ) := mul_pos hc hd'
  have hsub : {X | statistic n d κ R X ≤ 0} ⊆
      {X | (c*(d:ℝ))^2 ≤ (statistic n d κ R X-statisticMean n d κ R)^2} := by
    intro X hX
    change statistic n d κ R X ≤ 0 at hX
    change (c*(d:ℝ))^2 ≤ (statistic n d κ R X-statisticMean n d κ R)^2
    have hgap : c*(d:ℝ) ≤ statisticMean n d κ R-statistic n d κ R X := by linarith
    have hsq := pow_le_pow_left₀ hcd.le hgap 2
    nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun X => sq_nonneg (statistic n d κ R X-statisticMean n d κ R))
    (statistic_centered_sq_integrable hn hd hκ R) ((c*(d:ℝ))^2)
  have hmul := mul_le_mul_of_nonneg_left (measureReal_mono (μ := sampleLaw n d) hsub) (sq_nonneg (c*(d:ℝ)))
  have hvar := statistic_centered_sq_le hn hd hκ R
  have hbound : (sampleLaw n d).real {X | statistic n d κ R X ≤ 0} ≤ (Real.pi^2/8)/(c*(d:ℝ))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hcd)).mpr
    nlinarith
  convert hbound using 1 <;> field_simp <;> ring

theorem statistic_negative_tail {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {κ R c : ℝ}
    (hκ : 1 ≤ κ) (hc : 0 < c) (hmean : c*d ≤ statisticMean n d κ R) :
    (sampleLaw n d).real {X | statistic n d κ R X < 0} ≤ Real.pi^2/(8*c^2*(d:ℝ)^2) :=
  (measureReal_mono (μ := sampleLaw n d) (show {X | statistic n d κ R X < 0} ⊆ {X | statistic n d κ R X ≤ 0}
    from by
      intro X h
      change statistic n d κ R X < 0 at h
      change statistic n d κ R X ≤ 0
      exact h.le)).trans (statistic_nonpositive_tail hn hd hκ hc hmean)

/-- The numerical consequence of expected Gordon after the auxiliary drift-norm estimate.
The exact comparison boundary is defined in BMGordonAuxiliaryMean and implies this proposition. -/
def ExpectedGordonLower (n d : ℕ) (κ R : ℝ) : Prop :=
  conditionedWidth d κ - Real.sqrt ((n:ℝ)*(1+(R⁻¹)^2)) ≤ statisticMean n d κ R

end BMSaddle
