import UCPSDGaussianMinimum
import GaussianVarianceBound

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianTensorMoments GaussianMixedNormHelpers MeasureTheory
namespace UCEscape
open BMGeometry

lemma psdMinimumEuclidean_lipschitz {d : ℕ} (hd : 0 < d) :
    LipschitzWith 1 (fun z : EuclideanSpace ℝ (Fin d × Fin d) =>
      psdMinimum d ((frobeniusEquivEuclidean d d).symm z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := (psdMinimum_lipschitz hd).dist_le_mul
    ((frobeniusEquivEuclidean d d).symm x) ((frobeniusEquivEuclidean d d).symm y)
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub,
    LinearIsometryEquiv.norm_map] using h

theorem psdMinimumRaw_integrable {d : ℕ} (hd : 0 < d) :
    Integrable (psdMinimumRaw d) (gaussianProductLaw (Fin d × Fin d)) := by
  have hi : Integrable (fun z : EuclideanSpace ℝ (Fin d × Fin d) =>
      psdMinimum d ((frobeniusEquivEuclidean d d).symm z))
      (euclideanGaussianLaw (Fin d × Fin d)) :=
    GaussianVariance.lipschitz_integrable (psdMinimumEuclidean_lipschitz hd)
  rw [euclideanGaussianLaw] at hi
  have h := (integrable_map_measure
    (psdMinimumEuclidean_lipschitz hd).continuous.aestronglyMeasurable
    (MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).measurable.aemeasurable).mp hi
  exact h

theorem mean_psdMinimum_ge_neg_width {d : ℕ} (hd : 0 < d) :
    -psdWidth d ≤ ∫ x, psdMinimumRaw d x ∂gaussianProductLaw (Fin d × Fin d) := by
  have hm := gaussianProductLaw_neg_preserving (Fin d × Fin d)
  have hi : Integrable (fun x => gaussianPSDSupportRaw d (-x))
      (gaussianProductLaw (Fin d × Fin d)) :=
    (hm.integrable_comp (gaussianPSDSupportRaw_continuous d).aestronglyMeasurable).mpr
      (gaussianPSDSupportRaw_integrable d)
  have he : (∫ x, gaussianPSDSupportRaw d (-x) ∂gaussianProductLaw (Fin d × Fin d)) = psdWidth d := by
    have h := integral_map (μ := gaussianProductLaw (Fin d × Fin d)) hm.measurable.aemeasurable
      (f := gaussianPSDSupportRaw d) (gaussianPSDSupportRaw_continuous d).aestronglyMeasurable
    rw [hm.map_eq] at h
    exact h.symm
  have h := integral_mono hi.neg (psdMinimumRaw_integrable hd)
    (neg_support_le_psdMinimum hd)
  simp only [Pi.neg_apply] at h
  rw [integral_neg, he] at h
  exact h

theorem mean_psdMinimum_lower {d : ℕ} (hd : 0 < d) :
    -Real.sqrt ((d : ℝ)*(d+1)/4) ≤
      ∫ x, psdMinimumRaw d x ∂gaussianProductLaw (Fin d × Fin d) := by
  exact (neg_le_neg (psdWidth_le_sqrt d)).trans (mean_psdMinimum_ge_neg_width hd)

#print axioms psdMinimumRaw_integrable
#print axioms mean_psdMinimum_lower
end UCEscape
