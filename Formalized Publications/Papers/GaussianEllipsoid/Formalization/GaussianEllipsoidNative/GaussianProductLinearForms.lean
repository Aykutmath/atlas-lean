import GaussianScalarTail
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! The standard finite product Gaussian law, coordinate independence, and
sub-Gaussian bounds for normalized linear forms under that actual law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators

namespace GaussianTensorMoments

variable {ι : Type*} [Fintype ι]

/-- Actual iid standard Gaussian law on a finite coordinate vector. -/
def gaussianProductLaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance gaussianProductLaw_probability : IsProbabilityMeasure (gaussianProductLaw ι) := by
  unfold gaussianProductLaw
  infer_instance

/-- Each coordinate has the standard normal marginal, proved from the product law. -/
theorem gaussianProductLaw_coordinate (i : ι) :
    (gaussianProductLaw ι).map (fun x => x i) = gaussianReal 0 1 := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have heq : (fun x : ι → ℝ => x i) ⁻¹' s =
      Set.univ.pi (fun j : ι => if j=i then s else Set.univ) := by
    ext x
    simp
  rw [heq, gaussianProductLaw, Measure.pi_pi]
  simp_rw [apply_ite]
  simp

/-- The coordinate family is independent under the explicitly defined product law. -/
theorem gaussianProductLaw_iIndepFun :
    iIndepFun (fun i : ι => fun x : ι → ℝ => x i) (gaussianProductLaw ι) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).2
  simp_rw [gaussianProductLaw_coordinate]
  simpa [gaussianProductLaw] using (Measure.map_id (gaussianProductLaw ι))

/-- A scaled coordinate has its exact squared coefficient as variance. -/
theorem gaussianProductLaw_scaled_coordinate (i : ι) (c : ℝ) :
    (gaussianProductLaw ι).map (fun x => c*x i) =
      gaussianReal 0 ⟨c^2, sq_nonneg c⟩ := by
  have hcomp : (fun x : ι → ℝ => c*x i) =
      (fun z : ℝ => c*z) ∘ (fun x => x i) := rfl
  rw [hcomp, ← Measure.map_map (measurable_const_mul c) (measurable_pi_apply i),
    gaussianProductLaw_coordinate, gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  rfl

/-- Finite normalized linear forms of iid standard Gaussians have parameter one. -/
theorem gaussianProductLaw_linear_subGaussian (w : ι → ℝ)
    (hw : ∑ i, (w i)^2 = 1) :
    HasSubgaussianMGF (fun x : ι → ℝ => ∑ i, w i*x i) 1
      (gaussianProductLaw ι) := by
  classical
  let c : ι → ℝ≥0 := fun i => NNReal.mk ((w i)^2) (sq_nonneg _)
  have hc : ∑ i, c i = 1 := by
    apply NNReal.coe_injective
    simpa [c] using hw
  have hi : iIndepFun (fun i : ι => fun x : ι → ℝ => w i*x i)
      (gaussianProductLaw ι) :=
    gaussianProductLaw_iIndepFun.comp (fun i z => w i*z)
      (fun i => measurable_const_mul (w i))
  have hsub (i : ι) : HasSubgaussianMGF (fun x : ι → ℝ => w i*x i) (c i)
      (gaussianProductLaw ι) :=
    hasSubgaussianMGF_of_centered_gaussian (gaussianProductLaw_scaled_coordinate i (w i))
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hi
    (s := Finset.univ) (fun i _ => hsub i)
  simpa [hc] using hsum

/-- Two-sided normalized linear-form tail under the concrete finite product law. -/
theorem gaussianProductLaw_linear_abs_tail (w : ι → ℝ)
    (hw : ∑ i, (w i)^2 = 1) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianProductLaw ι).real {x | t ≤ |∑ i, w i*x i|} ≤
      2*exp (-(t^2)/2) := by
  let X : (ι → ℝ) → ℝ := fun x => ∑ i, w i*x i
  have hsg : HasSubgaussianMGF X 1 (gaussianProductLaw ι) :=
    gaussianProductLaw_linear_subGaussian w hw
  have hp := hsg.measure_ge_le ht
  have hn := (hasSubgaussianMGF_neg hsg).measure_ge_le ht
  have hset : {x | t ≤ |X x|} = {x | t ≤ X x} ∪ {x | t ≤ -X x} := by
    ext x
    simp [le_abs]
  change (gaussianProductLaw ι).real {x | t ≤ |X x|} ≤ _
  rw [hset]
  calc
    _ ≤ (gaussianProductLaw ι).real {x | t ≤ X x} +
        (gaussianProductLaw ι).real {x | t ≤ -X x} := measureReal_union_le _ _
    _ ≤ _ := by
      simpa only [NNReal.coe_one, mul_one, Pi.neg_apply, two_mul] using add_le_add hp hn

#print axioms gaussianProductLaw_coordinate
#print axioms gaussianProductLaw_iIndepFun
#print axioms gaussianProductLaw_linear_abs_tail

end GaussianTensorMoments
