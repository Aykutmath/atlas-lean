import RegularizedGramBound
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory Matrix Finset Set

namespace GaussianEllipsoid.CappedSimplex
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The regularized moment integrand is continuous in the sample entries. -/
theorem continuous_regularized_det_neg_nat_zpow {ε : ℝ} (hε : 0 < ε)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℕ) :
    Continuous (fun g : κ → ι → ℝ => (regularizedGram ε g w).det ^ (-(s : ℤ))) := by
  have hdet : Continuous (fun g : κ → ι → ℝ => (regularizedGram ε g w).det) := by
    apply Continuous.matrix_det
    unfold regularizedGram weightedGram
    fun_prop
  apply hdet.zpow₀
  intro g
  exact Or.inl (ne_of_gt (regularizedGram_posDef hε g hw).det_pos)

/-- The deterministic positive-ridge bound gives genuine integrability for
any finite sample measure, independent of any Gaussian identities. -/
theorem integrable_regularized_det_neg_nat_zpow
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {w : κ → ℝ} (hw : ∀ k, 0 ≤ w k) (s : ℕ) :
    Integrable (fun g : κ → ι → ℝ => (regularizedGram ε g w).det ^ (-(s : ℤ))) μ := by
  apply (integrable_const ((ε ^ Fintype.card ι) ^ (-(s : ℤ)))).mono'
    (continuous_regularized_det_neg_nat_zpow hε hw s).aestronglyMeasurable
  filter_upwards [] with g
  have hn : 0 ≤ (regularizedGram ε g w).det ^ (-(s : ℤ)) :=
    le_of_lt (zpow_pos (regularizedGram_posDef hε g hw).det_pos _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact regularized_det_neg_nat_zpow_le hε g hw s

/-- Regularized inverse determinant expectation, with integrability proved above. -/
def regularizedMoment (μ : Measure (κ → ι → ℝ)) (ε : ℝ) (s : ℕ) (w : κ → ℝ) : ℝ :=
  ∫ g, (regularizedGram ε g w).det ^ (-(s : ℤ)) ∂μ

/-- Integrating the genuine matrix line-convexity inequality preserves the
pairwise convexity required for finite capped-simplex rounding. -/
theorem pairwiseConvex_regularizedMoment (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (a b : ℝ) (s : ℕ) :
    PairwiseConvex a b (regularizedMoment μ ε s) := by
  intro w hw i j hij
  refine ⟨convex_transfer_domain a b w i j, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hmix := convex_transfer_domain a b w i j hx hy hp hq hpq
  have hIx := integrable_regularized_det_neg_nat_zpow μ hε (fun k => (hx.1 k).1) s
  have hIy := integrable_regularized_det_neg_nat_zpow μ hε (fun k => (hy.1 k).1) s
  have hIm := integrable_regularized_det_neg_nat_zpow μ hε (fun k => (hmix.1 k).1) s
  have hpoint : ∀ g : κ → ι → ℝ,
      (regularizedGram ε g (transfer w i j (p • x + q • y))).det ^ (-(s : ℤ)) ≤
      p * (regularizedGram ε g (transfer w i j x)).det ^ (-(s : ℤ)) +
      q * (regularizedGram ε g (transfer w i j y)).det ^ (-(s : ℤ)) := by
    intro g
    exact (pairwiseConvex_regularized_det_neg_nat_zpow hε g a b s w hw i j hij).2
      hx hy hp hq hpq
  have hle := integral_mono hIm ((hIx.const_mul p).add (hIy.const_mul q)) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hIx.const_mul p) (hIy.const_mul q), integral_const_mul,
    integral_const_mul] at hle
  simpa only [regularizedMoment, smul_eq_mul] using hle

/-- The expectation-level capped extremizer, with all determinant convexity
and integrability obligations discharged. No Gaussianity is needed until
one identifies the expectations for equal-cardinality subsets. -/
theorem regularizedMoment_le_uniform_subset
    (μ : Measure (κ → ι → ℝ)) [IsFiniteMeasure μ]
    {ε : ℝ} (hε : 0 < ε) (s m : ℕ) (hm : 0 < m)
    {w : κ → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1) :
    ∃ S : Finset κ, S.card = m ∧
      regularizedMoment μ ε s w ≤
        regularizedMoment μ ε s (fun i => if i ∈ S then (m : ℝ)⁻¹ else 0) := by
  exact exists_reciprocal_cap_subset_ge_of_pairwise m hm _
    (pairwiseConvex_regularizedMoment μ hε _ _ s) hw

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.regularizedMoment_le_uniform_subset
