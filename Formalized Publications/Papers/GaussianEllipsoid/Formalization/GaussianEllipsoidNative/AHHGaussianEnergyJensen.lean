import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
Weighted Cauchy--Schwarz bounds for the Fisher-information part of a
Gaussian semigroup proof.  These lemmas hold for an arbitrary measure:
no Gaussian, finite-measure, or probability hypothesis is required.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace AHHGaussianEnergyJensen

/-- The pointwise tangent inequality for the quadratic-over-linear energy. -/
theorem tangent_sq_div {f g a : ℝ} (hf : 0 < f) :
    2 * a * g - a ^ 2 * f ≤ g ^ 2 / f := by
  have h : 0 ≤ (g - a * f) ^ 2 / f := div_nonneg (sq_nonneg _) hf.le
  have he : (g - a * f) ^ 2 / f = g ^ 2 / f - 2 * a * g + a ^ 2 * f := by
    field_simp
    ring
  rw [he] at h
  linarith

/-- Integrated tangent inequality, with only the three natural integrability
hypotheses.  Strict positivity of the weight is needed almost everywhere. -/
theorem integral_tangent_sq_div {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (a : ℝ)
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (henergy : Integrable (fun x => g x ^ 2 / f x) μ) :
    2 * a * (∫ x, g x ∂μ) - a ^ 2 * (∫ x, f x ∂μ) ≤
      ∫ x, g x ^ 2 / f x ∂μ := by
  have hle : (fun x => 2 * a * g x - a ^ 2 * f x) ≤ᵐ[μ]
      (fun x => g x ^ 2 / f x) := by
    filter_upwards [hfpos] with x hx
    exact tangent_sq_div hx
  have hi := integral_mono_ae ((hg.const_mul (2 * a)).sub (hf.const_mul (a ^ 2)))
    henergy hle
  simpa only [Pi.sub_apply, integral_sub (hg.const_mul (2 * a)) (hf.const_mul (a ^ 2)),
    integral_const_mul] using hi

/-- Weighted integral Cauchy--Schwarz in the form used to contract
Fisher information under a Markov kernel. -/
theorem integral_sq_div_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ)
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (henergy : Integrable (fun x => g x ^ 2 / f x) μ)
    (hmean : 0 < ∫ x, f x ∂μ) :
    (∫ x, g x ∂μ) ^ 2 / (∫ x, f x ∂μ) ≤
      ∫ x, g x ^ 2 / f x ∂μ := by
  have hi := integral_tangent_sq_div μ f g
    ((∫ x, g x ∂μ) / (∫ x, f x ∂μ)) hfpos hf hg henergy
  have he :
      2 * ((∫ x, g x ∂μ) / (∫ x, f x ∂μ)) * (∫ x, g x ∂μ) -
          ((∫ x, g x ∂μ) / (∫ x, f x ∂μ)) ^ 2 * (∫ x, f x ∂μ) =
        (∫ x, g x ∂μ) ^ 2 / (∫ x, f x ∂μ) := by
    field_simp
    ring
  rwa [he] at hi

/-- Coordinatewise weighted Cauchy--Schwarz, summed over any finite set.
This is the finite-dimensional gradient-energy version of `integral_sq_div_le`. -/
theorem sum_integral_sq_div_le {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (f : α → ℝ) (g : ι → α → ℝ)
    (hfpos : ∀ᵐ x ∂μ, 0 < f x) (hf : Integrable f μ)
    (hg : ∀ i ∈ s, Integrable (g i) μ)
    (henergy : ∀ i ∈ s, Integrable (fun x => g i x ^ 2 / f x) μ)
    (hmean : 0 < ∫ x, f x ∂μ) :
    (∑ i ∈ s, (∫ x, g i x ∂μ) ^ 2) / (∫ x, f x ∂μ) ≤
      ∫ x, (∑ i ∈ s, g i x ^ 2) / f x ∂μ := by
  simp_rw [Finset.sum_div]
  rw [integral_finsetSum s henergy]
  exact Finset.sum_le_sum fun i hi =>
    integral_sq_div_le μ f (g i) hfpos hf (hg i hi) (henergy i hi) hmean

/-- A positive lower bound makes the energy of bounded continuous functions
integrable against every finite measure. -/
theorem boundedContinuous_integrable_energy {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f g : α →ᵇ ℝ) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ f x) :
    Integrable (fun x => g x ^ 2 / f x) μ := by
  apply (integrable_const (‖g‖ ^ 2 / c)).mono'
  · exact ((g.continuous.measurable.pow_const 2).div f.continuous.measurable).aestronglyMeasurable
  filter_upwards with x
  have hfx : 0 < f x := hc.trans_le (hcf x)
  have hgsq : g x ^ 2 ≤ ‖g‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg (g x)) (norm_nonneg g)).2 (g.norm_coe_le_norm x)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hfx.le)]
  exact div_le_div₀ (sq_nonneg _) hgsq hc (hcf x)

/-- The probability-measure specialization requires only bounded continuous
functions and a uniform strictly positive lower bound on the weight. -/
theorem boundedContinuous_integral_sq_div_le {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f g : α →ᵇ ℝ) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ f x) :
    (∫ x, g x ∂μ) ^ 2 / (∫ x, f x ∂μ) ≤
      ∫ x, g x ^ 2 / f x ∂μ := by
  have hmean : 0 < ∫ x, f x ∂μ := by
    apply hc.trans_le
    simpa using integral_mono (integrable_const c) (f.integrable μ) hcf
  exact integral_sq_div_le μ f g (Filter.Eventually.of_forall fun x => hc.trans_le (hcf x))
    (f.integrable μ) (g.integrable μ)
    (boundedContinuous_integrable_energy μ f g hc hcf) hmean

#print axioms tangent_sq_div
#print axioms integral_tangent_sq_div
#print axioms integral_sq_div_le
#print axioms sum_integral_sq_div_le
#print axioms boundedContinuous_integrable_energy
#print axioms boundedContinuous_integral_sq_div_le

end AHHGaussianEnergyJensen
