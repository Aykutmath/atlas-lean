import BMGordonSoftMinMaxApprox
import BMGordonSoftMinMaxDeriv
import BMGordonAffineInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMRowInterpolation MvPolynomial Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMGordonSoftMinMax
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  (μ : Measure Ω) [IsFiniteMeasure μ]

theorem continuous_minMax : Continuous (minMax : (I × J → ℝ) → ℝ) := by
  apply Continuous.finset_inf'_apply
  intro i hi
  apply Continuous.finset_sup'_apply
  intro j hj
  exact continuous_apply (i,j)

theorem continuous_softMinMax_forExpectation (β : ℝ) (hβ : β ≠ 0) :
    Continuous (softMinMax β : (I × J → ℝ) → ℝ) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_softMinMax β hβ x).continuousAt

/-- Gaussian integrability requires only the integrability of finitely many coordinates. -/
theorem minMax_integrable (x : Ω → I × J → ℝ) (hc : Continuous x)
    (hx : ∀ a, Integrable (fun ω => x ω a) μ) :
    Integrable (fun ω => minMax (x ω)) μ := by
  have henv : Integrable (fun ω => ∑ a, ‖x ω a‖) μ :=
    integrable_finset_sum _ (fun a _ => (hx a).norm)
  apply henv.mono' (continuous_minMax.comp hc).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using! abs_minMax_le_sum_abs (x ω)

theorem softMinMax_integrable (β : ℝ) (hβ : 0 < β)
    (x : Ω → I × J → ℝ) (hc : Continuous x)
    (hx : ∀ a, Integrable (fun ω => x ω a) μ) :
    Integrable (fun ω => softMinMax β (x ω)) μ := by
  have henv : Integrable (fun ω => ∑ a, ‖x ω a‖) μ :=
    integrable_finset_sum _ (fun a _ => (hx a).norm)
  apply ((henv.add (integrable_const (Real.log (Fintype.card I : ℝ)/β))).add
    (integrable_const (Real.log (Fintype.card J : ℝ)/β))).mono'
      ((continuous_softMinMax_forExpectation β (ne_of_gt hβ)).comp hc).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using! abs_softMinMax_le_sum_abs_add_logs β hβ (x ω)

/-- Uniform deterministic approximation also bounds the error of actual expectations. -/
theorem expected_softMinMax_bounds [IsProbabilityMeasure μ] (β : ℝ) (hβ : 0 < β)
    (x : Ω → I × J → ℝ) (hc : Continuous x)
    (hx : ∀ a, Integrable (fun ω => x ω a) μ) :
    (∫ ω, minMax (x ω) ∂μ) - Real.log (Fintype.card I : ℝ)/β ≤
      (∫ ω, softMinMax β (x ω) ∂μ) ∧
    (∫ ω, softMinMax β (x ω) ∂μ) ≤
      (∫ ω, minMax (x ω) ∂μ) + Real.log (Fintype.card J : ℝ)/β := by
  have hi := minMax_integrable μ x hc hx
  have hs := softMinMax_integrable μ β hβ x hc hx
  constructor
  · have h := integral_mono (hi.sub (integrable_const _)) hs
      (fun ω => (minMax_sub_log_card_le_softMinMax_le β hβ (x ω)).1)
    simpa only [Pi.sub_apply, integral_sub hi (integrable_const _), integral_const,
      probReal_univ, one_smul] using h
  · have h := integral_mono hs (hi.add (integrable_const _))
      (fun ω => (minMax_sub_log_card_le_softMinMax_le β hβ (x ω)).2)
    simpa only [Pi.add_apply, integral_add hi (integrable_const _), integral_const,
      probReal_univ, one_smul] using h

/-- Zero-temperature passage for expectations of the actual smooth minmax. -/
theorem tendsto_expected_softMinMax [IsProbabilityMeasure μ]
    (x : Ω → I × J → ℝ) (hc : Continuous x)
    (hx : ∀ a, Integrable (fun ω => x ω a) μ) :
    Tendsto (fun β : ℝ => ∫ ω, softMinMax β (x ω) ∂μ) atTop
      (nhds (∫ ω, minMax (x ω) ∂μ)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun β : ℝ => (∫ ω, minMax (x ω) ∂μ)-Real.log (Fintype.card I : ℝ)/β)
    (h := fun β : ℝ => (∫ ω, minMax (x ω) ∂μ)+Real.log (Fintype.card J : ℝ)/β)
  · simpa only [sub_zero] using! tendsto_const_nhds.sub
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  · simpa only [add_zero] using! tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with β hβ
    exact (expected_softMinMax_bounds μ β hβ x hc hx).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with β hβ
    exact (expected_softMinMax_bounds μ β hβ x hc hx).2

end BMGordonSoftMinMax
