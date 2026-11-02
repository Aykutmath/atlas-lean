import RadialGaussianIntegral
import GaussianProductLinearForms
import PiWithDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianTensorMoments
open scoped ENNReal NNReal BigOperators

namespace GaussianMixedNormHelpers

/-- A measure-preserving measurable equivalence transports its density exactly. -/
theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (he : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = ν.withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  simpa only [e.symm_apply_apply] using
    he.setLIntegral_comp_preimage_emb e.measurableEmbedding (fun y => f (e.symm y)) s

/-- Actual iid standard Gaussian law has the product of its scalar densities. -/
theorem gaussianProductLaw_eq_withDensity {ι : Type*} [Fintype ι] :
    gaussianProductLaw ι = (volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  unfold gaussianProductLaw
  simp only [gaussianReal, one_ne_zero, if_false, gaussianPDF]
  exact GaussianProductDensity.pi_withDensity_ofReal (fun _ : ι => (volume : Measure ℝ))
    (fun _ => gaussianPDFReal 0 1) (fun _ => integrable_gaussianPDFReal 0 1)
    (fun _ => gaussianPDFReal_nonneg 0 1)

def gaussianDensityConstant (ι : Type*) [Fintype ι] : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι

/-- Product Gaussian density in exact Euclidean norm form. -/
theorem gaussianProductDensity_eq_radial {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) :
    (∏ i, gaussianPDFReal 0 1 (x i)) =
      gaussianDensityConstant ι * Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2) := by
  classical
  have hn : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp only [Real.norm_eq_abs, sq_abs]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, hn]
  unfold gaussianDensityConstant
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Standard Gaussian law in the Euclidean-space realization. -/
def euclideanGaussianLaw (ι : Type*) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  (gaussianProductLaw ι).map (MeasurableEquiv.toLp 2 (ι → ℝ))

theorem euclideanGaussianLaw_eq_withDensity {ι : Type*} [Fintype ι] :
    euclideanGaussianLaw ι = (volume : Measure (EuclideanSpace ℝ ι)).withDensity
      (fun x => ENNReal.ofReal (gaussianDensityConstant ι *
        Real.exp (-(1 / 2 : ℝ) * ‖x‖ ^ 2))) := by
  unfold euclideanGaussianLaw
  rw [gaussianProductLaw_eq_withDensity,
    map_withDensity_equiv (MeasurableEquiv.toLp 2 (ι → ℝ)) _ _
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).symm]
  congr 1
  funext x
  congr 1
  exact gaussianProductDensity_eq_radial x

end GaussianMixedNormHelpers
