import AllRowsBilinearSmallBall
import GaussianBilinearSmallBall

/-! Reconstructed adaptation of preserved even-row transfer proofs.
New source; verification pending the all-row Frobenius prerequisite. -/
noncomputable section
open MeasureTheory Finset GaussianMixedNormHelpers GaussianTensorMoments
namespace GaussianEllipsoid.SmallBall

/-- Real-valued probability form of the actual Frobenius small-ball theorem. -/
theorem gaussian_bilinear_frobenius_smallball_real_all_rows (r n : ℕ)
    (hr : 0 < r) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) {t : ℝ} (ht : 0 < t) :
    (bilinearGaussianSampleLaw r n).real
      {p | ‖bilinearFrobenius r n z p - M‖ ≤ t * Real.sqrt (r : ℝ)} ≤
      (4 * t) ^ (r * r) := by
  have h := gaussian_bilinear_frobenius_smallball_all_rows r n hr z hzsum hzcap
    (frobeniusEquivEuclidean r r M) ht
  have hnorm : ∀ p, ‖bilinearFrobenius r n z p - M‖ =
      ‖bilinearFlat r n z p - frobeniusEquivEuclidean r r M‖ := by
    intro p
    rw [← (frobeniusEquivEuclidean r r).norm_map (bilinearFrobenius r n z p - M), map_sub]
    simp only [bilinearFrobenius, LinearIsometryEquiv.apply_symm_apply]
  have heq : {p | ‖bilinearFrobenius r n z p - M‖ ≤ t * Real.sqrt (r : ℝ)} =
      {p | ‖bilinearFlat r n z p - frobeniusEquivEuclidean r r M‖ ≤ t * Real.sqrt (r : ℝ)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    rw [hnorm]
  rw [heq]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

/-- Actual arbitrary-center nuclear small ball, proved from the Gaussian law,
full capped determinant moment, exact density calculation, and actual C256 cover. -/
theorem gaussian_bilinear_nuclear_smallball_all_rows (r n : ℕ)
    (hr : 0 < r) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) {ν : ℝ} (hν : 0 < ν) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearFrobenius r n z p - M) ≤ ν * r} ≤
      (160 * ν) ^ (r * r) := by
  exact nuclear_smallball_polynomial (bilinearGaussianSampleLaw r n) r hr
    (bilinearFrobenius r n z)
    (fun C t ht => gaussian_bilinear_frobenius_smallball_real_all_rows r n hr z hzsum hzcap C ht)
    M hν

/-- Conservative fixed-radius endpoint used by every multiscale driver block. -/
theorem gaussian_bilinear_nuclear_smallball_unit_all_rows (r n : ℕ)
    (hr : 0 < r) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearFrobenius r n z p - M) ≤ (r : ℝ) / 1024} ≤
      Real.exp (-(r * r : ℕ)) := by
  exact nuclear_smallball_unit_exp (bilinearGaussianSampleLaw r n) r hr
    (bilinearFrobenius r n z)
    (fun C t ht => gaussian_bilinear_frobenius_smallball_real_all_rows r n hr z hzsum hzcap C ht) M

end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_nuclear_smallball_unit_all_rows
