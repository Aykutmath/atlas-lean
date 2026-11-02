import PaperActualConditionalMGF
import CanonicalMultiscaleLaw
import PrefixWitnessDecomposition

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid GaussianEllipsoid.ProjectedClusters BMGeometry
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- The manuscript's X_k = <Z_{<k}, B V_k> is exactly the normalized scalar
observable used by the conditional determinant theorem, not merely equal in law. -/
theorem source_bilinear_pairing_eq {N n h d : ℕ} (e : Fin n ↪ Fin N)
    (z : GaussianEntries N h × GaussianEntries N h) (v : Fin n → ℝ)
    (W : Euclid h →L[ℝ] Euclid h) :
    ⟪operatorFrobenius W,gaussianBilinearOperator n h d (selectSample e z)
      ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) v)⟫_ℝ =
    (Real.sqrt (d:ℝ))⁻¹ *∑ i,v i*⟪(sourceDriverRows e z i).1,
      W (sourceDriverRows e z i).2⟫_ℝ := by
  rw [← scaled_bilinearSynthesis_tensorToCanonicalRows,operatorFrobenius_real_smul,
    real_inner_comm,real_inner_smul_left,inner_bilinearSynthesis]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact real_inner_comm _ _

#print axioms source_bilinear_pairing_eq
end GaussianEllipsoidCandidate
