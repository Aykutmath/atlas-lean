import RegularizedGramBound
import RealDeterminantPowers
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory Matrix Finset Set

namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The regularized moment integrand is continuous in the sample entries. -/
theorem continuous_regularized_det_neg_rpow {ε : ℝ} (hε : 0 < ε)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun g : κ → ι → ℝ => (regularizedGram ε g w).det ^ (-s)) := by
  have hdet : Continuous (fun g : κ → ι → ℝ => (regularizedGram ε g w).det) := by
    apply Continuous.matrix_det
    unfold regularizedGram weightedGram
    fun_prop
  apply hdet.rpow_const
  intro g
  exact Or.inl (ne_of_gt (regularizedGram_posDef hε g hw).det_pos)

/-- The deterministic positive-ridge bound gives genuine integrability for
any finite sample measure, independent of any Gaussian identities. -/
theorem integrable_regularized_det_neg_rpow
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun g : κ → ι → ℝ => (regularizedGram ε g w).det ^ (-s)) μ := by
  apply (integrable_const ((ε ^ Fintype.card ι) ^ (-s))).mono'
    (continuous_regularized_det_neg_rpow hε hw s hs).aestronglyMeasurable
  filter_upwards [] with g
  have hn : 0 ≤ (regularizedGram ε g w).det ^ (-s) :=
    le_of_lt (Real.rpow_pos_of_pos (regularizedGram_posDef hε g hw).det_pos _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact Real.rpow_le_rpow_of_nonpos (pow_pos hε _)
    (det_scalar_add_posSemidef_ge (weightedGram_posSemidef g hw) hε.le) (neg_nonpos.mpr hs)

/-- Regularized inverse determinant expectation, with integrability proved above. -/
def regularizedRealMoment (μ : Measure (κ → ι → ℝ)) (ε : ℝ) (s : ℝ) (w : κ → ℝ) : ℝ :=
  ∫ g, (regularizedGram ε g w).det ^ (-s) ∂μ

/-- Integrating the genuine matrix line-convexity inequality preserves the
pairwise convexity required for finite capped-simplex rounding. -/
theorem pairwiseConvex_regularizedRealMoment (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (a b : ℝ) (s : ℝ) (hs : 0 ≤ s) :
    PairwiseConvex a b (regularizedRealMoment μ ε s) := by
  intro w hw i j hij
  refine ⟨convex_transfer_domain a b w i j, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hmix := convex_transfer_domain a b w i j hx hy hp hq hpq
  have hIx := integrable_regularized_det_neg_rpow μ hε (fun k => (hx.1 k).1) s hs
  have hIy := integrable_regularized_det_neg_rpow μ hε (fun k => (hy.1 k).1) s hs
  have hIm := integrable_regularized_det_neg_rpow μ hε (fun k => (hmix.1 k).1) s hs
  have hpoint : ∀ g : κ → ι → ℝ,
      (regularizedGram ε g (transfer w i j (p • x + q • y))).det ^ (-s) ≤
      p * (regularizedGram ε g (transfer w i j x)).det ^ (-s) +
      q * (regularizedGram ε g (transfer w i j y)).det ^ (-s) := by
    intro g
    exact (pairwiseConvex_regularized_det_neg_rpow hε g a b s hs w hw i j hij).2
      hx hy hp hq hpq
  have hle := integral_mono hIm ((hIx.const_mul p).add (hIy.const_mul q)) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hIx.const_mul p) (hIy.const_mul q), integral_const_mul,
    integral_const_mul] at hle
  simpa only [regularizedRealMoment, smul_eq_mul] using hle


end GaussianEllipsoid.CappedSimplex
