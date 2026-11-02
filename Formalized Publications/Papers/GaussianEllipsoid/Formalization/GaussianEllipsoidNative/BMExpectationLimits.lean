import BMFiniteGroundState
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open Filter MeasureTheory

namespace BMExpectationLimits

/-- The two limits are taken in the correct order: dimension first for every
fixed inverse temperature, then inverse temperature tends to infinity. -/
theorem tendsto_zero_of_temperature_comparison (f : ℕ → ℝ) (C : ℝ)
    (hf : ∀ d, 0 ≤ f d) (hC : 0 ≤ C)
    (hcompare : ∀ β : ℝ, 0 < β → ∃ e : ℕ → ℝ,
      Tendsto e atTop (nhds 0) ∧ ∀ᶠ d in atTop, f d ≤ e d+C/β) :
    Tendsto f atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let β := 4*(C+1)/ε
  have hβ : 0 < β := div_pos (by positivity) hε
  have hsmall : C/β < ε/2 := by
    apply (div_lt_iff₀ hβ).2
    have he : ε/2*β = 2*(C+1) := by dsimp [β]; field_simp; ring
    rw [he]
    linarith
  obtain ⟨e,he,hfe⟩ := hcompare β hβ
  have hnear : ∀ᶠ d in atTop, e d < ε/2 := he.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hfe,hnear] with d hfd hed
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hf d)]
  linarith

/-- Expectation-only universality suffices to transfer a zero minimum risk. -/
theorem tendsto_zero_of_expectation_comparison (a b : ℕ → ℝ)
    (hgap : Tendsto (fun d => a d-b d) atTop (nhds 0))
    (hb : Tendsto b atTop (nhds 0)) : Tendsto a atTop (nhds 0) := by
  simpa only [sub_add_cancel,add_zero] using hgap.add hb

/-- An absolute expectation comparison has the same zero-limit consequence. -/
theorem tendsto_zero_of_abs_expectation_comparison (a b : ℕ → ℝ)
    (hgap : Tendsto (fun d => |a d-b d|) atTop (nhds 0))
    (hb : Tendsto b atTop (nhds 0)) : Tendsto a atTop (nhds 0) := by
  apply tendsto_zero_of_expectation_comparison a b _ hb
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hgap

/-- Markov converts vanishing nonnegative expected risk to vanishing failure
probability, including dimension-dependent sample spaces and probability laws. -/
theorem probability_risk_ge_tendsto_zero
    {Ω : ℕ → Type*} [∀ d, MeasurableSpace (Ω d)]
    (μ : (d : ℕ) → Measure (Ω d)) (R : (d : ℕ) → Ω d → ℝ)
    (hR : ∀ d x, 0 ≤ R d x) (hI : ∀ d, Integrable (R d) (μ d))
    (hmean : Tendsto (fun d => ∫ x, R d x ∂μ d) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => (μ d).real {x | ε ≤ R d x}) atTop (nhds 0) := by
  apply squeeze_zero (fun d => ENNReal.toReal_nonneg) (fun d => ?_)
    (by simpa only [zero_div] using hmean.div_const ε)
  apply (le_div_iff₀ hε).2
  simpa only [mul_comm] using!
    mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall (hR d)) (hI d) ε

/-- A bounded risk is controlled in expectation by any threshold and its bad
event. This is the boundedness step from Gaussian feasibility in probability. -/
theorem bounded_risk_expectation_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : Ω → ℝ)
    (hRm : Measurable R) (hI : Integrable R μ) {M δ : ℝ}
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hR : ∀ x, R x ≤ M) :
    (∫ x, R x ∂μ) ≤ δ+M*μ.real {x | δ ≤ R x} := by
  let E := {x | δ ≤ R x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hRm
  have hi : Integrable (E.indicator (fun _ => M)) μ := (integrable_const M).indicator hE
  have hp (x : Ω) : R x ≤ δ+E.indicator (fun _ => M) x := by
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      linarith [hR x]
    · rw [Set.indicator_of_notMem hx]
      have : R x < δ := lt_of_not_ge hx
      linarith
  have h := integral_mono hI ((integrable_const δ).add hi) hp
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_const δ) hi,integral_indicator hE] at h
  simpa [E,integral_const,smul_eq_mul,mul_comm] using h

/-- Bounded nonnegative risk converging to zero in probability also converges
in expectation; no distribution-universality theorem is required. -/
theorem bounded_risk_expectation_tendsto_zero
    {Ω : ℕ → Type*} [∀ d, MeasurableSpace (Ω d)]
    (μ : (d : ℕ) → Measure (Ω d)) [∀ d, IsProbabilityMeasure (μ d)]
    (R : (d : ℕ) → Ω d → ℝ) (hRm : ∀ d, Measurable (R d))
    (hI : ∀ d, Integrable (R d) (μ d)) {M : ℝ} (hM : 0 ≤ M)
    (hR : ∀ d x, 0 ≤ R d x ∧ R d x ≤ M)
    (hprob : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun d => (μ d).real {x | δ ≤ R d x}) atTop (nhds 0)) :
    Tendsto (fun d => ∫ x, R d x ∂μ d) atTop (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε/2 := by linarith
  have hp := (hprob (ε/2) hδ).const_mul M
  have hp' : Tendsto (fun d => M*(μ d).real {x | ε/2 ≤ R d x}) atTop (nhds 0) := by
    simpa only [mul_zero] using hp
  have hn : ∀ᶠ d in atTop, M*(μ d).real {x | ε/2 ≤ R d x} < ε/2 :=
    hp'.eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with d hd
  have hb := bounded_risk_expectation_le (μ d) (R d) (hRm d) (hI d) hM hδ.le
    (fun x => (hR d x).2)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun x => (hR d x).1)]
  linarith

#print axioms probability_risk_ge_tendsto_zero
#print axioms bounded_risk_expectation_tendsto_zero
#print axioms tendsto_zero_of_temperature_comparison
#print axioms tendsto_zero_of_abs_expectation_comparison
end BMExpectationLimits
