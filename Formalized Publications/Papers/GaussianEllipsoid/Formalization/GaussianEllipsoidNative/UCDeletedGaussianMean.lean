import UCMinimumExpectation
import UCDeletedFrames

noncomputable section
open MeasureTheory ProbabilityTheory
namespace UCEscape

/-- Gaussian minimum projection mean with the actual small-deletion entropy
already discharged by the finite powerset count. -/
theorem deletedFrames_expectation_lower {n r k : ℕ}
    (U : deletedCoordinateSets n k →
      EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε t : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht : 0 < t) (ht1 : t ≤ 1) (hk : (k : ℝ) ≤ t * n) :
    (1 - ε) * Real.sqrt r *
        (1 - Real.exp ((n : ℝ) * t * (1 - Real.log t) - ε ^ 2 * (r : ℝ) / 8)) ≤
      ∫ x, projectedNormMinimum n r U x ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply projectedNormMinimum_expectation_lower_of_card_le_exp n r U ε
    ((n : ℝ) * t * (1 - Real.log t)) hε hε1
  simpa only [Fintype.card_coe] using deletedCoordinateSets_card_le_exp n k t ht ht1 hk

#print axioms deletedFrames_expectation_lower
#print axioms smoothLoss_average_lower_of_projectedEscape
end UCEscape
