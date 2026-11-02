import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-! Standard Gaussian scalar tails used by the rectangular matrix net bound.
These are actual probability inequalities for the Gaussian law, with no assumed
tail or assumed Gaussian integrability estimate. -/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace GaussianTensorMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}

/-- A centered Gaussian has its exact variance as sub-Gaussian parameter. -/
theorem hasSubgaussianMGF_of_centered_gaussian {v : ℝ≥0}
    (hX : μ.map X = gaussianReal 0 v) : HasSubgaussianMGF X v μ := by
  constructor
  · intro t
    apply mgf_pos_iff.mp
    rw [mgf_gaussianReal hX t]
    exact Real.exp_pos _
  · intro t
    rw [mgf_gaussianReal hX t]
    simp

/-- Negating a sub-Gaussian preserves its parameter. -/
theorem hasSubgaussianMGF_neg {v : ℝ≥0}
    (hX : HasSubgaussianMGF X v μ) : HasSubgaussianMGF (-X) v μ := by
  constructor
  · intro t
    simpa only [Pi.neg_apply, mul_neg, neg_mul] using hX.integrable_exp_mul (-t)
  · intro t
    rw [mgf_neg]
    simpa only [neg_sq] using hX.mgf_le (-t)

/-- The elementary Gaussian upper tail, with its explicit numerical constant. -/
theorem gaussian_upper_tail (hX : μ.map X = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ exp (-(t ^ 2) / 2) := by
  simpa using (hasSubgaussianMGF_of_centered_gaussian hX).measure_ge_le ht

/-- The two-sided scalar Gaussian tail needed for the sphere-net union bound. -/
theorem gaussian_abs_tail (hX : μ.map X = gaussianReal 0 1)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-(t ^ 2) / 2) := by
  have hsg := hasSubgaussianMGF_of_centered_gaussian hX
  have hp := hsg.measure_ge_le ht
  have hn := (hasSubgaussianMGF_neg hsg).measure_ge_le ht
  have hset : {ω | t ≤ |X ω|} = {ω | t ≤ X ω} ∪ {ω | t ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ -X ω}) ≤
        μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ -X ω} := measureReal_union_le _ _
    _ ≤ 2 * exp (-(t ^ 2) / 2) := by
      simpa only [NNReal.coe_one, mul_one, Pi.neg_apply, two_mul] using add_le_add hp hn

#print axioms hasSubgaussianMGF_of_centered_gaussian
#print axioms gaussian_abs_tail

end GaussianTensorMoments
