import RegularizedGramConvex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Set Matrix
namespace GaussianEllipsoid.CappedSimplex

/-- Negative real powers are convex on the positive half-line. -/
theorem convexOn_neg_rpow (s : ℝ) (hs : 0 ≤ s) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-s)) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hm : 0 < p * x + q * y := (convex_Ioi (0 : ℝ)) hx hy hp hq hpq
  have hl := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2 hx hy hp hq hpq
  simp only [smul_eq_mul] at hl ⊢
  rw [Real.rpow_def_of_pos hm, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
  have he : Real.exp (Real.log (p * x + q * y) * (-s)) ≤
      Real.exp (p * (Real.log x * (-s)) + q * (Real.log y * (-s))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) (neg_nonpos.mpr hs)]
  exact he.trans (convexOn_exp.2 (mem_univ _) (mem_univ _) hp hq hpq)

/-- Positive concave functions composed with a negative real power are convex. -/
theorem convexOn_neg_rpow_of_concave {I : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ I f) (hpos : ∀ x ∈ I, 0 < f x) (s : ℝ) (hs : 0 ≤ s) :
    ConvexOn ℝ I (fun x => f x ^ (-s)) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy p q hp hq hpq
  have hxpos := hpos x hx
  have hypos := hpos y hy
  have hmixpos : 0 < p * f x + q * f y :=
    (convex_Ioi (0 : ℝ)) hxpos hypos hp hq hpq
  have hconc := hf.2 hx hy hp hq hpq
  have hpow := Real.rpow_le_rpow_of_nonpos hmixpos hconc (neg_nonpos.mpr hs)
  exact hpow.trans ((convexOn_neg_rpow s hs).2 hxpos hypos hp hq hpq)

theorem convexOn_det_rankTwo_neg_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosDef) (u v : ι → ℝ)
    {I : Set ℝ} (hI : Convex ℝ I)
    (hpos : ∀ t ∈ I, (A + t • (Matrix.vecMulVec u u - Matrix.vecMulVec v v)).PosDef)
    (s : ℝ) (hs : 0 ≤ s) :
    ConvexOn ℝ I (fun t =>
      (Matrix.det (A + t • (Matrix.vecMulVec u u - Matrix.vecMulVec v v))) ^ (-s)) := by
  simp_rw [det_rankTwo_update hA u v]
  apply convexOn_neg_rpow_of_concave _ _ s hs
  · exact (concaveOn_quadratic _ _ _ (rankTwo_quadratic_coefficient_nonneg hA u v)).subset
      (Set.subset_univ _) hI
  · intro t ht
    rw [← det_rankTwo_update hA u v t]
    exact (hpos t ht).det_pos

theorem pairwiseConvex_regularized_det_neg_rpow
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {ε : ℝ} (hε : 0 < ε) (g : κ → ι → ℝ) (a b s : ℝ) (hs : 0 ≤ s) :
    PairwiseConvex a b (fun w => (Matrix.det (regularizedGram ε g w)) ^ (-s)) := by
  intro w hw i j _
  have hA : (regularizedGram ε g w).PosDef :=
    regularizedGram_posDef hε g (fun k => (hw.1 k).1)
  simp only [regularizedGram_transfer]
  apply convexOn_det_rankTwo_neg_rpow hA (g i) (g j)
    (convex_transfer_domain a b w i j) _ s hs
  intro t ht
  rw [← regularizedGram_transfer]
  exact regularizedGram_posDef hε g (fun k => (ht.1 k).1)

#print axioms pairwiseConvex_regularized_det_neg_rpow
end GaussianEllipsoid.CappedSimplex
