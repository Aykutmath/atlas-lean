import ConditionalMGFIteration
import MultiscaleMGF

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GaussianEllipsoidCandidate

/-- A finite nonnegative exponential integral proves its own Bochner
integrability; it need not be assumed before conditional iteration. -/
theorem integrable_exp_of_lintegral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) (t C : ℝ)
    (hbound : (∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ) ≤ ENNReal.ofReal C) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have hm : Measurable (fun ω => Real.exp (t * X ω)) := by fun_prop
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => Real.exp_nonneg _)).2
  exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top

/-- Transfer the nonnegative exponential integral bound to the real MGF. -/
theorem mgf_le_of_lintegral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) (t C : ℝ) (hC : 0 ≤ C)
    (hbound : (∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂μ) ≤ ENNReal.ofReal C) :
    mgf X μ t ≤ C := by
  have hm : Measurable (fun ω => Real.exp (t * X ω)) := by fun_prop
  unfold mgf
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => Real.exp_nonneg _) hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hC hbound

/-- Full finite-radius conditional-kernel Chernoff estimate. The Gaussian
analysis only has to supply the measurable one-step conditional bounds;
all tower iteration, integrability, optimization, and final tail conversion
are proved here. No almost-sure increment bound is assumed. -/
theorem lower_tail_of_conditional_kernel_mgf {Ω : Type*} [MeasurableSpace Ω]
    (K₀ : Kernel Unit Ω) (step : ℕ → Kernel Ω Ω)
    (S : ℕ → Ω → ℝ) (hS : ∀ k, Measurable (S k)) (v : ℕ → ℝ)
    (n : ℕ) [IsFiniteMeasure (iterKernel K₀ step n ())]
    (V b x : ℝ) (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x)
    (hvar : (∑ i ∈ Finset.range n, v i) ≤ V)
    (hinit : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((-lam) * S 0 ω)) ∂K₀ ()) ≤ 1)
    (hstep : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b → ∀ k,
      ∀ᵐ ω ∂iterKernel K₀ step k (),
        (∫⁻ ω', ENNReal.ofReal (Real.exp ((-lam) * S (k+1) ω')) ∂step k ω) ≤
          ENNReal.ofReal (Real.exp (lam^2 * v k)) *
            ENNReal.ofReal (Real.exp ((-lam) * S k ω))) :
    (iterKernel K₀ step n ()).real {ω | S n ω ≤ -x} ≤
      Real.exp (-(1 / 4 : ℝ) * min (x^2 / V) (x / b)) := by
  have hlin : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      (∫⁻ ω, ENNReal.ofReal (Real.exp ((-lam) * S n ω)) ∂iterKernel K₀ step n ()) ≤
        ENNReal.ofReal (Real.exp (lam^2 * V)) := by
    intro lam hlam hlammax
    have hc := conditional_kernel_exponential_iteration K₀ step S hS v (-lam)
      (hinit lam hlam hlammax) (by simpa only [neg_sq] using hstep lam hlam hlammax) n
    apply hc.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simpa only [neg_sq] using mul_le_mul_of_nonneg_left hvar (sq_nonneg lam)
  apply lower_tail_of_mgf_radius (iterKernel K₀ step n ()) (S n) V b x hV hb hx
  · intro lam hlam hlammax
    exact integrable_exp_of_lintegral_bound _ _ (hS n) (-lam) _ (hlin lam hlam hlammax)
  · intro lam hlam hlammax
    exact mgf_le_of_lintegral_bound _ _ (hS n) (-lam) _ (Real.exp_nonneg _) (hlin lam hlam hlammax)

#print axioms integrable_exp_of_lintegral_bound
#print axioms mgf_le_of_lintegral_bound
#print axioms lower_tail_of_conditional_kernel_mgf

end GaussianEllipsoidCandidate
