import GaussianQuadraticSpectral

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace
namespace BMQuadraticSpectral

/-- Exact transport of the quadratic gauge event, before any estimate. -/
theorem normalizedQuadratic_gauge_event_eq {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) (t : ℝ) :
    (euclideanGaussianLaw (Fin d))
      {x | t < min ((normalizedQuadratic T x)^2) (Real.sqrt d * |normalizedQuadratic T x|)/16} =
    (gaussianProductLaw (Fin d))
      {z | t < min ((GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight hT) z)^2)
        (Real.sqrt d * |GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight hT) z|)/16} := by
  exact (normalizedQuadratic_identDistrib hT).measure_mem_eq
    (show MeasurableSet {s : ℝ | t < min (s^2) (Real.sqrt d * |s|)/16} from
      measurableSet_lt measurable_const (by fun_prop))

/-- Actual centered self-adjoint quadratic gauge tail under the genuine Euclidean Gaussian law. -/
theorem normalizedQuadratic_gauge_tail_ennreal {d : ℕ} (hd : 0 < d)
    {T : Euclid d →L[ℝ] Euclid d} (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (euclideanGaussianLaw (Fin d))
      {x | t < min ((normalizedQuadratic T x)^2) (Real.sqrt d * |normalizedQuadratic T x|)/16} ≤
      ENNReal.ofReal (2*Real.exp (-t)) := by
  rw [normalizedQuadratic_gauge_event_eq hT]
  exact GaussianEllipsoidCandidate.centeredDiagonal_gauge_tail_ennreal (eigenWeight hT)
    (Nat.cast_pos.mpr hd) (eigenWeight_abs_le hT hN) (sum_eigenWeight_sq_le hd hT hN) ht

/-- The same actual gauge tail in real measure. -/
theorem normalizedQuadratic_gauge_tail {d : ℕ} (hd : 0 < d)
    {T : Euclid d →L[ℝ] Euclid d} (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (euclideanGaussianLaw (Fin d)).real
      {x | t < min ((normalizedQuadratic T x)^2) (Real.sqrt d * |normalizedQuadratic T x|)/16} ≤
      2*Real.exp (-t) := by
  unfold Measure.real
  rw [normalizedQuadratic_gauge_event_eq hT]
  exact GaussianEllipsoidCandidate.centeredDiagonal_gauge_tail (eigenWeight hT)
    (Nat.cast_pos.mpr hd) (eigenWeight_abs_le hT hN) (sum_eigenWeight_sq_le hd hT hN) ht

/-- The corresponding two-sided tail for the actual normalized quadratic form. -/
theorem normalizedQuadratic_abs_tail {d : ℕ} (hd : 0 < d)
    {T : Euclid d →L[ℝ] Euclid d} (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) :
    (euclideanGaussianLaw (Fin d)).real {x | t ≤ |normalizedQuadratic T x|} ≤
      2*Real.exp (-min (t^2) (t * Real.sqrt d)/16) := by
  have he := (normalizedQuadratic_identDistrib hT).measure_mem_eq
    (show MeasurableSet {s : ℝ | t ≤ |s|} from measurableSet_le measurable_const continuous_abs.measurable)
  simp only [Set.preimage_setOf_eq] at he
  unfold Measure.real
  rw [he]
  exact GaussianEllipsoidCandidate.centeredDiagonal_normalized_abs_tail (eigenWeight hT)
    (Nat.cast_pos.mpr hd) (eigenWeight_abs_le hT hN) (sum_eigenWeight_sq_le hd hT hN) ht

#print axioms normalizedQuadratic_gauge_tail_ennreal
#print axioms normalizedQuadratic_gauge_tail
#print axioms normalizedQuadratic_abs_tail
end BMQuadraticSpectral
