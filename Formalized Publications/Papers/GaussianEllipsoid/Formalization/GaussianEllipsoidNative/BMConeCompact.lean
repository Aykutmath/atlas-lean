import BMAffineFeasibility

noncomputable section
open GaussianEllipsoid
namespace BMGeometry

def conditionedUnitFrobenius (d : ℕ) (κ : ℝ) : Set (HMat d) :=
  {S | frobeniusOperator S ∈ conditionCone d κ} ∩ Metric.sphere 0 1

theorem conditionedUnitFrobenius_compact (d : ℕ) (κ : ℝ) : IsCompact (conditionedUnitFrobenius d κ) :=
  (isCompact_sphere (0 : HMat d) 1).inter_left
    ((isClosed_conditionCone d κ).preimage (continuous_frobeniusOperator d d))

theorem conditionedUnit_eq_image (d : ℕ) (κ : ℝ) :
    conditionedUnit d κ = frobeniusOperator '' conditionedUnitFrobenius d κ := by
  ext T
  constructor
  · intro hT
    refine ⟨operatorFrobenius T, ⟨?_,?_⟩, frobeniusOperator_operatorFrobenius T⟩
    · change frobeniusOperator (operatorFrobenius T) ∈ conditionCone d κ
      simpa only [frobeniusOperator_operatorFrobenius] using hT.1
    · simpa only [Metric.mem_sphere, dist_zero_right] using hT.2
  · rintro ⟨S,hS,rfl⟩
    refine ⟨hS.1,?_⟩
    simpa only [operatorFrobenius_frobeniusOperator, Metric.mem_sphere, dist_zero_right] using hS.2

theorem conditionedUnit_compact (d : ℕ) (κ : ℝ) : IsCompact (conditionedUnit d κ) := by
  rw [conditionedUnit_eq_image]
  exact (conditionedUnitFrobenius_compact d κ).image (continuous_frobeniusOperator d d)

end BMGeometry
