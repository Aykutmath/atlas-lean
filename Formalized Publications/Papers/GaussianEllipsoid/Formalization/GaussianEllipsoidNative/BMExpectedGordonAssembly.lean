import BMStrictLimsup
import BMSaddleFeasibilityAssembly

/-!
# Full original BM approximate-fitting interface from the exact expected Gordon comparison

The sole hypothesis is BMSaddle.ExpectedGordonPrinciple, the comparison of
actual Gaussian expectations for the concrete attained min-max statistic.
This file does not prove that comparison. All consequences through Gaussian
feasibility, universality, every r < 4/3, trace normalization and arbitrary
strict-limsup sample schedules are proved by the imported concrete results.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open scoped ENNReal BigOperators InnerProductSpace

namespace BMBoxRiskAssembly

/-- The feasibility-statistic source is literally the original independent
full-entry Gaussian adapter-row source, with n rows and d² coordinates each. -/
theorem rawSourceLaw_eq_actual (n d : ℕ) :
    BMSaddle.rawSourceLaw n d =
      Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d))) := rfl

/-- Definitional expansion of the only pending analytic comparison. This
makes both genuine Gaussian laws and the actual saddle statistic explicit. -/
theorem expectedGordonPrinciple_iff_explicit :
    BMSaddle.ExpectedGordonPrinciple ↔
      ∀ n d : ℕ, 0 < n → 0 < d → ∀ κ R : ℝ, 1 ≤ κ → 0 < R →
        BMGeometry.conditionedWidth d κ -
          (∫ h : GaussianEllipsoid.Euclid n,
            ‖h-R⁻¹ • BMSaddle.ones n‖ ∂euclideanGaussianLaw (Fin n)) ≤
          ∫ X : BMSaddle.Sample n d,
            sInf ((fun u : GaussianEllipsoid.Euclid n =>
              BMGeometry.conditionedSupport d κ (BMSaddle.combine X u) -
                ⟪u,BMSaddle.ones n⟫_ℝ/R) '' Metric.sphere 0 1)
            ∂euclideanGaussianLaw (BMSaddle.EntryIndex n d) := Iff.rfl

/-- A positive subcritical ratio admits a strict deterministic upper gap
α=(a+1/4)/2, eventually on every positive dimension. -/
theorem eventual_subcritical_quadratic_bound_of_ratio
    (N : ℕ → ℕ) {a : ℝ} (ha : 0 < a) (haquarter : a < 1/4)
    (hlim : Tendsto (fun d => (N d:ℝ)/(d:ℝ)^2) atTop (nhds a)) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1/4 ∧
      ∀ᶠ d : ℕ in atTop, (N d:ℝ) ≤ α*(d:ℝ)^2 := by
  let α : ℝ := (a+1/4)/2
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hαquarter : α < 1/4 := by dsimp [α]; linarith
  have hagap : a < α := by dsimp [α]; linarith
  refine ⟨α,hα,hαquarter,?_⟩
  have he : ∀ᶠ d : ℕ in atTop, (N d:ℝ)/(d:ℝ)^2 < α :=
    (tendsto_order.1 hlim).2 α hagap
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with d hd hdim
  have hdR : 0 < (d:ℝ) := Nat.cast_pos.mpr hdim
  exact ((div_lt_iff₀ (sq_pos_of_pos hdR)).mp hd).le

/-- The exact expected Gaussian comparison discharges the entire actual
proportional cone-feasibility input, including its original source law. -/
theorem proportionalGaussianConeInput_of_expectedGordon
    (hG : BMSaddle.ExpectedGordonPrinciple) : ProportionalGaussianConeInput := by
  intro N hN a ha haquarter hlim
  obtain ⟨α,hα,hαquarter,haspect⟩ :=
    eventual_subcritical_quadratic_bound_of_ratio N ha haquarter hlim
  obtain ⟨κ,R,hκ,hR,hfail⟩ :=
    BMSaddle.exists_actualCone_failure_tendsto_zero_of_expectedGordon hG N hα hαquarter
      (Eventually.of_forall hN) haspect
  refine ⟨κ,R,hκ,?_⟩
  simpa only [rawSourceLaw_eq_actual] using hfail

/-- Complete original quantifier order from only the pending expected Gordon
principle: positive counts and strict ENNReal limsup below 1/4, with one fixed
positive spectral box for every 1 ≤ r < 4/3. -/
theorem bmApproximateFitting_of_expectedGordon
    (hG : BMSaddle.ExpectedGordonPrinciple) :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMminRiskAllR n lo hi :=
  bmApproximateFitting_of_gaussian_cone (proportionalGaussianConeInput_of_expectedGordon hG)

/-- Fully expanded original BM physical real-power infimum-risk formula.
No cone-feasibility, universality, moment, regularity, or sample-window
hypothesis remains beyond the exact expected Gordon comparison. -/
theorem bmApproximateFitting_original_formula_of_expectedGordon
    (hG : BMSaddle.ExpectedGordonPrinciple) :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
        ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
          Tendsto (fun d => (coordinateSampleLaw d (n d)).real
            {x | ε < sInf {t : ℝ | ∃ S ∈ BMRescaling.spectralBox d lo hi,
              t = (1/(n d:ℝ))*∑ i,
                |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^r}})
            atTop (nhds 0) :=
  bmApproximateFitting_original_formula_of_gaussian_cone
    (proportionalGaussianConeInput_of_expectedGordon hG)

end BMBoxRiskAssembly
