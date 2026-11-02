import BMSaddleRawModel
import BMGordonAuxiliaryMean

noncomputable section
set_option synthInstance.maxSize 1024
open scoped Topology ENNReal
open GaussianEllipsoid BMGeometry GaussianTensorMoments GaussianMixedNormHelpers MeasureTheory ProbabilityTheory Filter
namespace BMSaddle

/-- The sole unproved analytic boundary in this packet. This is precisely the expected
Gordon comparison for the concrete attained min-max statistic and independent standard Gaussian laws. -/
def ExpectedGordonPrinciple : Prop :=
  ∀ n d : ℕ, 0 < n → 0 < d → ∀ κ R : ℝ, 1 ≤ κ → 0 < R → ExpectedGordonComparison n d κ R

theorem saddle_tail_error_tendsto (c : ℝ) :
    Tendsto (fun d : ℕ => Real.pi^2/(8*c^2*(d:ℝ)^2)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat.pow 2).const_mul (Real.pi^2/(8*c^2))
  convert! h using 1
  · funext d
    simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,one_mul]
    ring
  · simp

/-- Actual conditioned-cone failure vanishes from an eventual macroscopic mean bound.
This theorem contains no comparison assumption and records every dimension/count guard. -/
theorem actualCone_failure_tendsto_zero_of_mean_margin (n : ℕ → ℕ) {κ R c : ℝ}
    (hκ : 1 ≤ κ) (hR : 0 < R) (hc : 0 < c)
    (hn : ∀ᶠ d : ℕ in atTop, 0 < n d)
    (hmean : ∀ᶠ d : ℕ in atTop, c*d ≤ statisticMean (n d) d κ R) :
    Tendsto (fun d => (rawSourceLaw (n d) d).real
      {z | ¬BMSpectralBridge.actualConeFeasible (n d) d κ R z}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ (saddle_tail_error_tendsto c)
  filter_upwards [hn,hmean,eventually_gt_atTop 0] with d hnD hmD hd
  exact actualCone_failure_le_mean_tail hnD hd hκ hR hc hmD

/-- Integration theorem for the pending comparison: all geometry, width, variance,
Chebyshev, exact-law transport and BM scaling are discharged. It is deliberately conditional
on ExpectedGordonPrinciple, which has no proof in this packet. -/
theorem exists_actualCone_failure_tendsto_zero_of_expectedGordon
    (hG : ExpectedGordonPrinciple) (n : ℕ → ℕ) {α : ℝ} (hα : 0 ≤ α) (hαquarter : α < 1/4)
    (hn : ∀ᶠ d : ℕ in atTop, 0 < n d)
    (haspect : ∀ᶠ d : ℕ in atTop, (n d : ℝ) ≤ α*(d:ℝ)^2) :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 < R ∧
      Tendsto (fun d => (rawSourceLaw (n d) d).real
        {z | ¬BMSpectralBridge.actualConeFeasible (n d) d κ R z}) atTop (𝓝 0) := by
  obtain ⟨κ,R,c,hκ,hR,hc,hmargin⟩ := exists_condition_radius_margin hα hαquarter
  refine ⟨κ,R,hκ,hR,actualCone_failure_tendsto_zero_of_mean_margin n hκ hR hc hn ?_⟩
  filter_upwards [hn,haspect,hmargin,eventually_gt_atTop 0] with d hnD haD hmD hd
  have hg := expectedGordonLower_of_comparison (hG (n d) d hnD hd κ R hκ hR)
  have hm := hmD (n d) haD
  unfold ExpectedGordonLower at hg
  linarith

/-- Equivalent success-probability output on the literal original adapter law. -/
theorem exists_actualCone_probability_tendsto_one_of_expectedGordon
    (hG : ExpectedGordonPrinciple) (n : ℕ → ℕ) {α : ℝ} (hα : 0 ≤ α) (hαquarter : α < 1/4)
    (hn : ∀ᶠ d : ℕ in atTop, 0 < n d)
    (haspect : ∀ᶠ d : ℕ in atTop, (n d : ℝ) ≤ α*(d:ℝ)^2) :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 < R ∧
      Tendsto (fun d => (rawSourceLaw (n d) d).real
        {z | BMSpectralBridge.actualConeFeasible (n d) d κ R z}) atTop (𝓝 1) := by
  obtain ⟨κ,R,hκ,hR,hfail⟩ := exists_actualCone_failure_tendsto_zero_of_expectedGordon hG n hα hαquarter hn haspect
  refine ⟨κ,R,hκ,hR,?_⟩
  letI : ∀ d, IsProbabilityMeasure (rawSourceLaw (n d) d) := fun d => inferInstance
  exact BMSpectralBridge.probability_tendsto_one_of_failure_tendsto_zero
    (fun d => rawSourceLaw (n d) d)
    (fun d => {z | BMSpectralBridge.actualConeFeasible (n d) d κ R z}) hfail

end BMSaddle
