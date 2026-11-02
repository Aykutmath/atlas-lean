/- Newly reconstructed analytic support, 2026-10-03. Not recovered original bytes.
   Reindexing and exact strict-tail transport, with no concentration premise. -/
import GaussianLipschitzConcentration

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianLipschitzConcentration

namespace GaussianFiniteIndexConcentration
variable {ι : Type*} [Fintype ι]

def flattenIso : EuclideanSpace ℝ (Fin (Fintype.card ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι).symm

theorem flattenIso_preserving : MeasurePreserving (flattenIso (ι := ι))
    (euclideanGaussianLaw (Fin (Fintype.card ι))) (euclideanGaussianLaw ι) := by
  have hraw : MeasurePreserving
      (fun x : Fin (Fintype.card ι) → ℝ => fun i : ι => x (Fintype.equivFin ι i))
      (gaussianProductLaw (Fin (Fintype.card ι))) (gaussianProductLaw ι) := by
    convert! measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1)
      (Fintype.equivFin ι).symm using 1
    ext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h := (BMQuadraticSpectral.coordinates_preserving (ι := ι)).symm.comp
    (hraw.comp (BMQuadraticSpectral.coordinates_preserving (ι := Fin (Fintype.card ι))))
  exact h

theorem integral_preserving {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {p : α → β} (hp : MeasurePreserving p μ ν)
    {f : β → ℝ} (hf : AEStronglyMeasurable f ν) :
    (∫ x, f (p x) ∂μ) = ∫ y, f y ∂ν := by
  have hm : AEStronglyMeasurable f (Measure.map p μ) := by rwa [hp.map_eq]
  have hh := (integral_map hp.measurable.aemeasurable hm).symm
  rwa [hp.map_eq] at hh

theorem nonnegative_lipschitz_laplace {f : EuclideanSpace ℝ ι → ℝ}
    (hf : LipschitzWith 1 f) (hpos : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, Real.exp (t*((∫ y, f y ∂euclideanGaussianLaw ι)-f x))
      ∂euclideanGaussianLaw ι) ≤ Real.exp (t^2/2) := by
  have hl : LipschitzWith 1 (fun x => f (flattenIso (ι := ι) x)) := by
    simpa only [one_mul] using! hf.comp (flattenIso (ι := ι)).lipschitz
  have h := nonnegative_lipschitz_laplace_fin hl (fun x => hpos _) ht
  have hm := integral_preserving (flattenIso_preserving (ι := ι)) hf.continuous.aestronglyMeasurable
  rw [hm] at h
  have he := integral_preserving (flattenIso_preserving (ι := ι))
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub hf.continuous))).aestronglyMeasurable :
      AEStronglyMeasurable (fun x => Real.exp (t*((∫ y, f y ∂euclideanGaussianLaw ι)-f x)))
        (euclideanGaussianLaw ι))
  simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply] at he
  rwa [he] at h

/-- Sharp Gaussian concentration for the precise strict lower-tail event. -/
theorem nonnegative_lipschitz_strict_lower_tail {f : EuclideanSpace ℝ ι → ℝ}
    (hf : LipschitzWith 1 f) (hpos : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    (euclideanGaussianLaw ι).real {x | f x < (∫ y, f y ∂euclideanGaussianLaw ι)-t} ≤
      Real.exp (-t^2/2) := by
  let m := ∫ y, f y ∂euclideanGaussianLaw ι
  have hi : Integrable (fun x => Real.exp (t*(m-f x))) (euclideanGaussianLaw ι) := by
    apply (integrable_const (Real.exp (t*m))).mono'
    · exact (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub hf.continuous))).aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        nlinarith [hpos x]
  exact GaussianLaplaceTail.strict_lower_tail_of_laplace_bound _ f m t ht hi
    (nonnegative_lipschitz_laplace hf hpos ht)

#print axioms nonnegative_lipschitz_strict_lower_tail
end GaussianFiniteIndexConcentration
