import BilinearCovariance
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix Finset
open GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.CappedSimplex
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall

abbrev BilinearSample (r n : ℕ) := (Fin n → Fin r → ℝ) × EuclideanSpace ℝ (Fin n × Fin r)

def bilinearGaussianSampleLaw (r n : ℕ) : Measure (BilinearSample r n) :=
  (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))).prod
    (euclideanGaussianLaw (Fin n × Fin r))

/-- Actual vectorized bilinear Gaussian observation. -/
def bilinearFlat (r n : ℕ) (z : Fin n → ℝ) (p : BilinearSample r n) :
    EuclideanSpace ℝ (Fin r × Fin r) :=
  matrixCLM (bilinearDriver (Real.sqrt (r : ℝ))⁻¹ z p.1) p.2

/-- Joint measurability follows from the explicit bilinear coordinate formula. -/
theorem measurable_bilinearFlat (r n : ℕ) (z : Fin n → ℝ) :
    Measurable (bilinearFlat r n z) := by
  let f : BilinearSample r n → (Fin r × Fin r → ℝ) :=
    fun p pq => (Real.sqrt (r : ℝ))⁻¹ * ∑ i, z i * p.1 i pq.1 * p.2 (i, pq.2)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro pq
    unfold f
    fun_prop
  have hm := (MeasurableEquiv.toLp 2 ((Fin r × Fin r) → ℝ)).measurable.comp hf
  have heq : bilinearFlat r n z = (MeasurableEquiv.toLp 2 ((Fin r × Fin r) → ℝ)) ∘ f := by
    funext p
    ext pq
    exact matrixCLM_bilinearDriver_apply _ z p.1 p.2 pq.1 pq.2
  rw [heq]
  exact hm

/-- All dimension and Gaussian-normalization factors cancel with their exact
finite powers. The final numerical constant uses exp(1)<11/4. -/
theorem bilinear_probability_constant_le (r k : ℕ) (hr : 0 < r)
    (hdim : r * r = 2 * k) (t : ℝ) :
    (Real.sqrt (r : ℝ)) ^ (r * r) * (2 * Real.exp 1) ^ k *
        (((t * Real.sqrt (r : ℝ)) ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) ≤
      (4 * t) ^ (r * r) := by
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hs : (Real.sqrt (r : ℝ)) ^ 2 = r := Real.sq_sqrt (le_of_lt hrR)
  have hkR : 2 * (k : ℝ) = (r : ℝ) * r := by exact_mod_cast hdim.symm
  have hfrac : (t * Real.sqrt (r : ℝ)) ^ 2 / (2 * (k : ℝ)) = t ^ 2 / r := by
    rw [mul_pow, hs, hkR]
    field_simp
  have hpow : (Real.sqrt (r : ℝ)) ^ (r * r) = (r : ℝ) ^ k := by
    rw [hdim, pow_mul, hs]
  have he : Real.exp (k : ℝ) = (Real.exp 1) ^ k := by
    simpa using Real.exp_nat_mul (1 : ℝ) k
  rw [hfrac, hpow, he, hdim, pow_mul]
  have hid : (r : ℝ) ^ k * (2 * Real.exp 1) ^ k *
      ((t ^ 2 / r) ^ k * (Real.exp 1) ^ k) = (2 * (Real.exp 1) ^ 2 * t ^ 2) ^ k := by
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  rw [hid]
  apply pow_le_pow_left₀ (by positivity)
  have heB : Real.exp 1 < 11 / 4 := Real.exp_one_lt_d9.trans (by norm_num)
  have heP : 0 < Real.exp 1 := Real.exp_pos _
  have hC : 2 * (Real.exp 1) ^ 2 ≤ 16 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hC (sq_nonneg t)
  nlinarith

/-- Composition lemma from an actual determinant moment to the actual bilinear
Gaussian small ball. Its determinant-moment premise is discharged by the separate
capped-Wishart theorem in the final wrapper, not added to MixedNormBound. -/
theorem bilinear_frobenius_smallball_of_moment (r n s : ℕ) (hr : 0 < r) (hs : r = 2 * s)
    (z : Fin n → ℝ)
    (hMoment : extendedMoment (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))) s
        (fun i => (z i) ^ 2) ≤ ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)))
    (M : EuclideanSpace ℝ (Fin r × Fin r)) {t : ℝ} (ht : 0 < t) :
    bilinearGaussianSampleLaw r n {p | ‖bilinearFlat r n z p - M‖ ≤ t * Real.sqrt (r : ℝ)} ≤
      ENNReal.ofReal ((4 * t) ^ (r * r)) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))
  let scale : ℝ := (Real.sqrt (r : ℝ))⁻¹
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hscale : 0 < scale := inv_pos.mpr (Real.sqrt_pos.mpr hrR)
  have hspos : 0 < s := by omega
  have hk : 0 < r * s := Nat.mul_pos hr hspos
  have hdim : r * r = 2 * (r * s) := by rw [hs]; ring
  have hcard : Fintype.card (Fin r × Fin r) = 2 * (r * s) := by simpa using hdim
  have hjoint : Measurable (fun p : BilinearSample r n =>
      matrixCLM (bilinearDriver scale z p.1) p.2 - M) :=
    (measurable_bilinearFlat r n z).sub measurable_const
  have h := joint_euclideanGaussian_rectangular_closedBall_le μ hcard hk
    (fun g => bilinearDriver scale z g) (fun _ => M)
    (R := t * Real.sqrt (r : ℝ)) (by positivity) hjoint
  have hJac : (∫⁻ g : Fin n → Fin r → ℝ, covarianceInverseJacobian (bilinearDriver scale z g) ∂μ) =
      ENNReal.ofReal ((Real.sqrt (r : ℝ)) ^ (r * r)) * extendedMoment μ s (fun i => (z i) ^ 2) := by
    simp_rw [covarianceInverseJacobian_bilinearDriver (ι := Fin r) (κ := Fin n)
      (s := s) (by simpa using hs) hscale]
    have hc : (ENNReal.ofReal (scale ^ (Fintype.card (Fin r) * Fintype.card (Fin r))))⁻¹ =
        ENNReal.ofReal ((Real.sqrt (r : ℝ)) ^ (r * r)) := by
      simp only [Fintype.card_fin, scale, inv_pow]
      rw [ENNReal.ofReal_inv_of_pos (pow_pos (Real.sqrt_pos.mpr hrR) _), inv_inv]
    rw [hc]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [hJac] at h
  have hMoment' : extendedMoment μ s (fun i => (z i) ^ 2) ≤
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := hMoment
  calc _ ≤ (ENNReal.ofReal ((Real.sqrt (r : ℝ)) ^ (r * r)) *
      extendedMoment μ s (fun i => (z i) ^ 2)) *
      ENNReal.ofReal (((t * Real.sqrt (r : ℝ)) ^ 2 / (2 * ((r * s : ℕ) : ℝ))) ^ (r * s) *
        Real.exp ((r * s : ℕ) : ℝ)) := h
    _ ≤ (ENNReal.ofReal ((Real.sqrt (r : ℝ)) ^ (r * r)) *
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s))) *
      ENNReal.ofReal (((t * Real.sqrt (r : ℝ)) ^ 2 / (2 * ((r * s : ℕ) : ℝ))) ^ (r * s) *
        Real.exp ((r * s : ℕ) : ℝ)) := mul_le_mul_left (mul_le_mul_right hMoment' _) _
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (bilinear_probability_constant_le r (r * s) hr hdim t)

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.bilinear_frobenius_smallball_of_moment
