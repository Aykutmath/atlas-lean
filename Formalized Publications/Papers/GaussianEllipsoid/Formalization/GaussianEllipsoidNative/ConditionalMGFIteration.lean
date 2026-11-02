import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaussianEllipsoidCandidate

/-- One predictable-product integration step. Nonnegative Lebesgue integrals
avoid assuming integrability of the accumulated exponential in advance. -/
theorem lintegral_predictable_product_le {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [SFinite μ] (κ : Kernel Ω Ξ) [IsSFiniteKernel κ]
    (F : Ω → ℝ≥0∞) (G : Ω × Ξ → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (c : ℝ≥0∞)
    (hconditional : ∀ᵐ x ∂μ, (∫⁻ y, G (x,y) ∂κ x) ≤ c) :
    (∫⁻ p, F p.1 * G p ∂(μ ⊗ₘ κ)) ≤ c * ∫⁻ x, F x ∂μ := by
  have hm : Measurable (fun p : Ω × Ξ => F p.1 * G p) := by fun_prop
  rw [Measure.lintegral_compProd hm]
  calc
    (∫⁻ x, ∫⁻ y, F x * G (x,y) ∂κ x ∂μ)
        = ∫⁻ x, F x * (∫⁻ y, G (x,y) ∂κ x) ∂μ := by
      apply lintegral_congr
      intro x
      exact lintegral_const_mul (F x) (by fun_prop)
    _ ≤ ∫⁻ x, F x * c ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hconditional] with x hx
      exact mul_le_mul_right hx _
    _ = c * ∫⁻ x, F x ∂μ := by rw [lintegral_mul_const c hF, mul_comm]

/-- Finite evolution of a law by measurable transition kernels. -/
noncomputable def iterKernel {Ω : Type*} [MeasurableSpace Ω]
    (K₀ : Kernel Unit Ω) (step : ℕ → Kernel Ω Ω) : ℕ → Kernel Unit Ω
  | 0 => K₀
  | n+1 => step n ∘ₖ iterKernel K₀ step n

/-- Iterating conditional nonnegative bounds needs no bounded increments,
no product-integrability assumption, and no independence between steps. -/
theorem conditional_kernel_product_iteration {Ω : Type*} [MeasurableSpace Ω]
    (K₀ : Kernel Unit Ω) (step : ℕ → Kernel Ω Ω)
    (Z : ℕ → Ω → ℝ≥0∞) (hZ : ∀ n, Measurable (Z n)) (c : ℕ → ℝ≥0∞)
    (hinit : (∫⁻ ω, Z 0 ω ∂K₀ ()) ≤ 1)
    (hstep : ∀ n, ∀ᵐ ω ∂iterKernel K₀ step n (),
      (∫⁻ ω', Z (n+1) ω' ∂step n ω) ≤ c n * Z n ω)
    (n : ℕ) :
    (∫⁻ ω, Z n ω ∂iterKernel K₀ step n ()) ≤ ∏ i ∈ Finset.range n, c i := by
  induction n with
  | zero => simpa [iterKernel] using hinit
  | succ n ih =>
    change (∫⁻ ω, Z (n+1) ω ∂(step n ∘ₖ iterKernel K₀ step n) ()) ≤ _
    rw [Kernel.lintegral_comp _ _ _ (hZ (n+1))]
    calc
      (∫⁻ ω, ∫⁻ ω', Z (n+1) ω' ∂step n ω ∂iterKernel K₀ step n ())
          ≤ ∫⁻ ω, c n * Z n ω ∂iterKernel K₀ step n () := lintegral_mono_ae (hstep n)
      _ = c n * ∫⁻ ω, Z n ω ∂iterKernel K₀ step n () := lintegral_const_mul (c n) (hZ n)
      _ ≤ c n * ∏ i ∈ Finset.range n, c i := mul_le_mul_right ih _
      _ = ∏ i ∈ Finset.range (n+1), c i := by rw [Finset.prod_range_succ, mul_comm]

/-- Exact exponential specialization of the conditional kernel iteration.
The hypothesis is required only at the chosen t, so a finite MGF radius is
fully supported; no global sub-Gaussian assertion is smuggled in. -/
theorem conditional_kernel_exponential_iteration {Ω : Type*} [MeasurableSpace Ω]
    (K₀ : Kernel Unit Ω) (step : ℕ → Kernel Ω Ω)
    (S : ℕ → Ω → ℝ) (hS : ∀ n, Measurable (S n)) (v : ℕ → ℝ) (t : ℝ)
    (hinit : (∫⁻ ω, ENNReal.ofReal (Real.exp (t * S 0 ω)) ∂K₀ ()) ≤ 1)
    (hstep : ∀ n, ∀ᵐ ω ∂iterKernel K₀ step n (),
      (∫⁻ ω', ENNReal.ofReal (Real.exp (t * S (n+1) ω')) ∂step n ω) ≤
        ENNReal.ofReal (Real.exp (t^2 * v n)) * ENNReal.ofReal (Real.exp (t * S n ω)))
    (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (t * S n ω)) ∂iterKernel K₀ step n ()) ≤
      ENNReal.ofReal (Real.exp (t^2 * ∑ i ∈ Finset.range n, v i)) := by
  have hh := conditional_kernel_product_iteration K₀ step
    (fun n ω => ENNReal.ofReal (Real.exp (t * S n ω)))
    (fun n => by fun_prop) (fun n => ENNReal.ofReal (Real.exp (t^2 * v n))) hinit hstep n
  have heq : (∏ i ∈ Finset.range n, ENNReal.ofReal (Real.exp (t^2 * v i))) =
      ENNReal.ofReal (Real.exp (t^2 * ∑ i ∈ Finset.range n, v i)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.exp_nonneg (t^2 * v i))]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
  exact hh.trans_eq heq

#print axioms lintegral_predictable_product_le
#print axioms conditional_kernel_product_iteration
#print axioms conditional_kernel_exponential_iteration

end GaussianEllipsoidCandidate
