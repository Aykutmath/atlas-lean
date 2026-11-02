import BMFullEntryWidth
import BMConditionCone

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianTensorMoments MeasureTheory
namespace UCEscape
open BMGeometry

def psdUnit (d : ℕ) : Set (HMat d) :=
  {S | IsPSD (frobeniusOperator S)} ∩ Metric.sphere 0 1

theorem psdUnit_compact (d : ℕ) : IsCompact (psdUnit d) :=
  (isCompact_sphere (0 : HMat d) 1).inter_left
    ((isClosed_isPSD d).preimage (continuous_frobeniusOperator d d))

theorem psdUnit_nonempty {d : ℕ} (hd : 0 < d) : (psdUnit d).Nonempty := by
  obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd (show (1:ℝ) ≤ 1 from le_rfl)
  refine ⟨operatorFrobenius S, ?_, ?_⟩
  · change IsPSD (frobeniusOperator (operatorFrobenius S))
    simpa only [frobeniusOperator_operatorFrobenius] using hS.1.1
  · simpa only [Metric.mem_sphere, dist_zero_right] using hS.2

/-- Full-entry isonormal testing of a PSD unit matrix is bounded by the
positive spectral Frobenius support, with no operator-norm loss. -/
theorem fullEntry_pairing_le_psdSupport {d : ℕ} (S : HMat d)
    (hS : S ∈ psdUnit d) (x : (Fin d × Fin d) → ℝ) :
    ⟪(frobeniusEquivEuclidean d d).symm ((WithLp.equiv 2 _).symm x), S⟫_ℝ ≤
      gaussianPSDSupportRaw d x := by
  let T := isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)
  have hsym := hS.1.1
  have hsNorm : ‖S‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hS.2
  have hn : ‖operatorFrobenius (frobeniusOperator S)‖ ≤ 1 := by
    simpa only [operatorFrobenius_frobeniusOperator] using hsNorm.le
  have hp := psd_unitBall_support_le T (isotropicSymmetricOp_symmetric d _) hS.1 hn
  rw [operatorFrobenius_frobeniusOperator] at hp
  change _ ≤ ‖operatorFrobenius (positivePart T _)‖
  convert hp using 1
  rw [isotropicSymmetricOp_frobenius]
  simpa only [operatorFrobenius_frobeniusOperator] using
    (symmetrization_pairing ((frobeniusEquivEuclidean d d).symm ((WithLp.equiv 2 _).symm x))
      (frobeniusOperator S) hsym).symm

#print axioms psdUnit_compact
#print axioms psdUnit_nonempty
#print axioms fullEntry_pairing_le_psdSupport
end UCEscape
