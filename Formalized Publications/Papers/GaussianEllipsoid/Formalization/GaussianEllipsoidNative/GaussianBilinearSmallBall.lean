import BilinearSmallBallCore
import GaussianCappedMoment
import FrobeniusCoordinates
import NuclearSmallBallTransfer

noncomputable section
open MeasureTheory Finset
open GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.CappedSimplex
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall

instance frobeniusMatrixMeasurableSpace (r q : ℕ) : MeasurableSpace (FrobeniusMatrix r q) :=
  borel (FrobeniusMatrix r q)

instance frobeniusMatrixBorelSpace (r q : ℕ) : BorelSpace (FrobeniusMatrix r q) := ⟨rfl⟩

instance bilinearGaussianSampleLaw_probability (r n : ℕ) :
    IsProbabilityMeasure (bilinearGaussianSampleLaw r n) := by
  unfold bilinearGaussianSampleLaw
  letI : ∀ i : Fin n, IsProbabilityMeasure (gaussianProductLaw (Fin r)) :=
    fun _ => gaussianProductLaw_probability
  letI : ∀ i : Fin n, SigmaFinite (gaussianProductLaw (Fin r)) := fun _ => inferInstance
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))) :=
    Measure.pi.instIsProbabilityMeasure _
  letI : IsProbabilityMeasure (euclideanGaussianLaw (Fin n × Fin r)) := by
    unfold euclideanGaussianLaw
    exact Measure.isProbabilityMeasure_map (MeasurableEquiv.toLp 2 ((Fin n × Fin r) → ℝ)).measurable.aemeasurable
  infer_instance

/-- The actual arbitrary-center Frobenius small ball in every positive even
row dimension. There is no determinant-moment, law-equality, or density premise. -/
theorem gaussian_bilinear_frobenius_smallball_even (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2 * s) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : EuclideanSpace ℝ (Fin r × Fin r)) {t : ℝ} (ht : 0 < t) :
    bilinearGaussianSampleLaw r n {p | ‖bilinearFlat r n z p - M‖ ≤ t * Real.sqrt (r : ℝ)} ≤
      ENNReal.ofReal ((4 * t) ^ (r * r)) := by
  apply bilinear_frobenius_smallball_of_moment r n s hr hrs z _ M ht
  exact gaussian_capped_even_extended_moment r s hr hrs
    ⟨(fun i => ⟨sq_nonneg _, hzcap i⟩), hzsum⟩

/-- The same actual bilinear observation in the genuine Frobenius matrix space. -/
def bilinearFrobenius (r n : ℕ) (z : Fin n → ℝ) (p : BilinearSample r n) :
    FrobeniusMatrix r r := (frobeniusEquivEuclidean r r).symm (bilinearFlat r n z p)

/-- Coordinate sanity check: this is exactly r^(-1/2)Σz_i g_i k_iᵀ. -/
theorem bilinearFrobenius_entry (r n : ℕ) (z : Fin n → ℝ) (p : BilinearSample r n)
    (a b : Fin r) :
    frobeniusToMatrix (bilinearFrobenius r n z p) a b =
      (Real.sqrt (r : ℝ))⁻¹ * ∑ i, z i * p.1 i a * p.2 (i, b) := by
  rw [← frobeniusEquivEuclidean_apply]
  unfold bilinearFrobenius
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact matrixCLM_bilinearDriver_apply _ z p.1 p.2 a b

theorem measurable_bilinearFrobenius (r n : ℕ) (z : Fin n → ℝ) :
    Measurable (bilinearFrobenius r n z) :=
  (frobeniusEquivEuclidean r r).symm.continuous.measurable.comp (measurable_bilinearFlat r n z)

/-- Real-valued probability form of the actual Frobenius small-ball theorem. -/
theorem gaussian_bilinear_frobenius_smallball_real_even (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2 * s) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) {t : ℝ} (ht : 0 < t) :
    (bilinearGaussianSampleLaw r n).real
      {p | ‖bilinearFrobenius r n z p - M‖ ≤ t * Real.sqrt (r : ℝ)} ≤
      (4 * t) ^ (r * r) := by
  have h := gaussian_bilinear_frobenius_smallball_even r n s hr hrs z hzsum hzcap
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
theorem gaussian_bilinear_nuclear_smallball_even (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2 * s) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) {ν : ℝ} (hν : 0 < ν) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearFrobenius r n z p - M) ≤ ν * r} ≤
      (160 * ν) ^ (r * r) := by
  exact nuclear_smallball_polynomial (bilinearGaussianSampleLaw r n) r hr
    (bilinearFrobenius r n z)
    (fun C t ht => gaussian_bilinear_frobenius_smallball_real_even r n s hr hrs z hzsum hzcap C ht)
    M hν

/-- Conservative fixed-radius endpoint used by every multiscale driver block. -/
theorem gaussian_bilinear_nuclear_smallball_unit_even (r n s : ℕ)
    (hr : 0 < r) (hrs : r = 2 * s) (z : Fin n → ℝ)
    (hzsum : ∑ i, (z i) ^ 2 = 1)
    (hzcap : ∀ i, (z i) ^ 2 ≤ (2 * (r : ℝ))⁻¹)
    (M : FrobeniusMatrix r r) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearFrobenius r n z p - M) ≤ (r : ℝ) / 1024} ≤
      Real.exp (-(r * r : ℕ)) := by
  exact nuclear_smallball_unit_exp (bilinearGaussianSampleLaw r n) r hr
    (bilinearFrobenius r n z)
    (fun C t ht => gaussian_bilinear_frobenius_smallball_real_even r n s hr hrs z hzsum hzcap C ht) M

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_frobenius_smallball_even
#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_nuclear_smallball_even
#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_nuclear_smallball_unit_even
