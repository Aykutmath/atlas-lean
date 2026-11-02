import AHHComplexSpectral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHAlgebraBridges

/-- Integrable PSD trace moments imply norm integrability and the exact Jensen
expectation-to-moment bound, without assuming integrability of the norm. -/
theorem complex_expectation_pow_le_trace_moment
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (M : Ω → Matrix ι ι ℂ)
    (hM : AEStronglyMeasurable M μ) (hPSD : ∀ ω, (M ω).PosSemidef)
    (m : ℕ) (hm : 1 ≤ m)
    (htrace : Integrable (fun ω => (Matrix.trace (M ω ^ m)).re) μ) :
    Integrable (fun ω => ‖cMatrixCLM (M ω)‖) μ ∧
      (∫ ω, ‖cMatrixCLM (M ω)‖ ∂μ) ^ m ≤
        ∫ ω, (Matrix.trace (M ω ^ m)).re ∂μ := by
  let f : Ω → ℝ := fun ω => ‖cMatrixCLM (M ω)‖
  have hfmeas : AEStronglyMeasurable f μ :=
    continuous_cMatrixCLM_norm.comp_aestronglyMeasurable hM
  have hfnn (ω : Ω) : 0 ≤ f ω := norm_nonneg _
  have hpow (ω : Ω) : f ω ^ m ≤ (Matrix.trace (M ω ^ m)).re :=
    complex_posSemidef_norm_pow_le_trace (M ω) (hPSD ω) m
  have hpowi : Integrable (fun ω => f ω ^ m) μ :=
    htrace.mono_nonneg (hfmeas.pow m) (ae_of_all _ (fun ω => pow_nonneg (hfnn ω) m))
      (ae_of_all _ hpow)
  have hsmall (ω : Ω) : f ω ≤ 1 + f ω ^ m := by
    by_cases h : f ω ≤ 1
    · linarith [pow_nonneg (hfnn ω) m]
    · have hp := le_self_pow₀ (le_of_lt (lt_of_not_ge h)) (by omega : m ≠ 0)
      linarith
  have hfi : Integrable f μ :=
    ((integrable_const (1 : ℝ)).add hpowi).mono_nonneg hfmeas (ae_of_all _ hfnn)
      (ae_of_all _ hsmall)
  refine ⟨hfi, ?_⟩
  have hj := (convexOn_pow m : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ m)).map_integral_le
    (continuous_pow m).continuousOn isClosed_Ici (ae_of_all _ hfnn) hfi hpowi
  exact hj.trans (integral_mono hpowi htrace hpow)

end AHHAlgebraBridges
