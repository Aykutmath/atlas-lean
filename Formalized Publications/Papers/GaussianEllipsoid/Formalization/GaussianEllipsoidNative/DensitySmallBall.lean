import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

noncomputable section
open MeasureTheory MeasureTheory.Measure Metric Module
open scoped ENNReal

namespace GaussianEllipsoid.SmallBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A bounded density remains bounded after an invertible linear map, with
the exact determinant Jacobian. This is an inequality for actual measures. -/
theorem withDensity_linear_preimage_le (f : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hD : ∀ x, f x ≤ D) (T : E →ₗ[ℝ] E) (hT : LinearMap.det T ≠ 0) (S : Set E) :
    (volume.withDensity f) (T ⁻¹' S) ≤
      D * ENNReal.ofReal |(LinearMap.det T)⁻¹| * volume S := by
  have hle : volume.withDensity f ≤ D • (volume : Measure E) := by
    calc volume.withDensity f ≤ volume.withDensity (fun _ => D) :=
            withDensity_mono (Filter.Eventually.of_forall hD)
         _ = D • volume := withDensity_const D
  have h := hle (T ⁻¹' S)
  change (volume.withDensity f) (T ⁻¹' S) ≤ D * volume (T ⁻¹' S) at h
  rw [addHaar_preimage_linearMap volume hT S] at h
  simpa only [mul_assoc] using h

/-- Arbitrary-center small-ball bound for a bounded density in even dimension. -/
theorem withDensity_closedBall_le_of_dim_even [Nontrivial E]
    {k : ℕ} (hk : finrank ℝ E = 2 * k) (f : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hD : ∀ x, f x ≤ D) (c : E) (R : ℝ) :
    (volume.withDensity f) (closedBall c R) ≤
      D * (ENNReal.ofReal R) ^ (2 * k) * ENNReal.ofReal (Real.pi ^ k / (k.factorial : ℝ)) := by
  have hle : volume.withDensity f ≤ D • (volume : Measure E) := by
    calc volume.withDensity f ≤ volume.withDensity (fun _ => D) :=
            withDensity_mono (Filter.Eventually.of_forall hD)
         _ = D • volume := withDensity_const D
  have h := hle (closedBall c R)
  change (volume.withDensity f) (closedBall c R) ≤ D * volume (closedBall c R) at h
  rw [InnerProductSpace.volume_closedBall_of_dim_even hk c R, hk] at h
  simpa only [mul_assoc] using h

/-- Combining the Jacobian with the exact even-dimensional ball volume. -/
theorem withDensity_linear_closedBall_le_of_dim_even [Nontrivial E]
    {k : ℕ} (hk : finrank ℝ E = 2 * k) (f : E → ℝ≥0∞) (D : ℝ≥0∞)
    (hD : ∀ x, f x ≤ D) (T : E →ₗ[ℝ] E) (hT : LinearMap.det T ≠ 0)
    (c : E) (R : ℝ) :
    (volume.withDensity f) (T ⁻¹' closedBall c R) ≤
      D * ENNReal.ofReal |(LinearMap.det T)⁻¹| *
        ENNReal.ofReal R ^ (2 * k) * ENNReal.ofReal (Real.pi ^ k / (k.factorial : ℝ)) := by
  have h := withDensity_linear_preimage_le f D hD T hT (closedBall c R)
  rw [InnerProductSpace.volume_closedBall_of_dim_even hk c R, hk] at h
  simpa only [mul_assoc] using h

/-- Exact cancellation of Gaussian density normalization against ball volume. -/
theorem gaussian_density_ball_coefficient (k : ℕ) (ell R : ℝ) :
    (ell / (2 * Real.pi)) ^ k * R ^ (2 * k) * (Real.pi ^ k / (k.factorial : ℝ)) =
      (ell * R ^ 2 / 2) ^ k / (k.factorial : ℝ) := by
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  simp only [div_pow, mul_pow, pow_mul]
  field_simp <;> ring

/-- An exponential-series term replaces Stirling in the Gaussian ball estimate. -/
theorem gaussian_density_ball_coefficient_le {k : ℕ} (hk : 0 < k)
    {ell R : ℝ} (hell : 0 ≤ ell) :
    (ell / (2 * Real.pi)) ^ k * R ^ (2 * k) * (Real.pi ^ k / (k.factorial : ℝ)) ≤
      (ell * R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  rw [gaussian_density_ball_coefficient]
  calc (ell * R ^ 2 / 2) ^ k / (k.factorial : ℝ) =
      (ell * R ^ 2 / (2 * (k : ℝ))) ^ k * ((k : ℝ) ^ k / (k.factorial : ℝ)) := by
        rw [div_pow, div_pow]
        field_simp
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.pow_div_factorial_le_exp (k : ℝ) (le_of_lt hkR) k) (by positivity)


/-- The exact Gaussian coefficient estimate in extended nonnegative form. -/
theorem gaussian_density_ball_coefficient_ennreal_le {k : ℕ} (hk : 0 < k)
    {ell R : ℝ} (hell : 0 ≤ ell) (hR : 0 ≤ R) (Z : ℝ≥0∞) :
    (ENNReal.ofReal ((ell / (2 * Real.pi)) ^ k) * Z) *
        ENNReal.ofReal R ^ (2 * k) * ENNReal.ofReal (Real.pi ^ k / (k.factorial : ℝ)) ≤
      Z * ENNReal.ofReal ((ell * R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  have hC : 0 ≤ (ell / (2 * Real.pi)) ^ k := by positivity
  calc _ = Z * ENNReal.ofReal ((ell / (2 * Real.pi)) ^ k * R ^ (2 * k) * (Real.pi ^ k / (k.factorial : ℝ))) := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hR _)),
          ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hR]
        ac_rfl
    _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (gaussian_density_ball_coefficient_le hk hell)) Z

/-- Small balls for any actual density dominated by a Gaussian peak times an
extended factor. The center is completely arbitrary. -/
theorem withDensity_gaussian_closedBall_le [Nontrivial E]
    {k : ℕ} (hk : finrank ℝ E = 2 * k) (hkpos : 0 < k)
    (f : E → ℝ≥0∞) (Z : ℝ≥0∞) {ell R : ℝ} (hell : 0 ≤ ell) (hR : 0 ≤ R)
    (hD : ∀ x, f x ≤ ENNReal.ofReal ((ell / (2 * Real.pi)) ^ k) * Z) (c : E) :
    (volume.withDensity f) (closedBall c R) ≤
      Z * ENNReal.ofReal ((ell * R ^ 2 / (2 * (k : ℝ))) ^ k * Real.exp (k : ℝ)) := by
  exact (withDensity_closedBall_le_of_dim_even hk f _ hD c R).trans
    (gaussian_density_ball_coefficient_ennreal_le hkpos hell hR Z)

/-- The Gaussian-normalized radius gives the exact elementary sqrt(e) volume factor. -/
theorem gaussian_normalized_radius_coefficient {k : ℕ} (hk : 0 < k)
    {ell : ℝ} (hell : 0 < ell) (t : ℝ) :
    (ell * (t * Real.sqrt (2 * (k : ℝ) / ell)) ^ 2 / (2 * (k : ℝ))) ^ k *
        Real.exp (k : ℝ) = (Real.sqrt (Real.exp 1) * t) ^ (2 * k) := by
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hs : (Real.sqrt (2 * (k : ℝ) / ell)) ^ 2 = 2 * (k : ℝ) / ell :=
    Real.sq_sqrt (by positivity)
  have hb : ell * (t * Real.sqrt (2 * (k : ℝ) / ell)) ^ 2 / (2 * (k : ℝ)) = t ^ 2 := by
    rw [mul_pow, hs]
    field_simp
  rw [hb, pow_mul, mul_pow, Real.sq_sqrt (le_of_lt (Real.exp_pos 1))]
  rw [mul_pow, ← Real.exp_nat_mul]
  simp only [mul_one]
  ring

/-- Normalized arbitrary-center Gaussian-peak small-ball estimate, with
singular/extended factors retained rather than converted to real zero. -/
theorem withDensity_gaussian_normalized_closedBall_le [Nontrivial E]
    {k : ℕ} (hk : finrank ℝ E = 2 * k) (hkpos : 0 < k)
    (f : E → ℝ≥0∞) (Z : ℝ≥0∞) {ell t : ℝ} (hell : 0 < ell) (ht : 0 ≤ t)
    (hD : ∀ x, f x ≤ ENNReal.ofReal ((ell / (2 * Real.pi)) ^ k) * Z) (c : E) :
    (volume.withDensity f) (closedBall c (t * Real.sqrt (2 * (k : ℝ) / ell))) ≤
      Z * ENNReal.ofReal ((Real.sqrt (Real.exp 1) * t) ^ (2 * k)) := by
  have h := withDensity_gaussian_closedBall_le (R := t * Real.sqrt (2 * (k : ℝ) / ell))
    hk hkpos f Z (le_of_lt hell)
    (mul_nonneg ht (Real.sqrt_nonneg _)) hD c
  rw [gaussian_normalized_radius_coefficient hkpos hell] at h
  exact h

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.withDensity_linear_closedBall_le_of_dim_even
#print axioms GaussianEllipsoid.SmallBall.withDensity_gaussian_normalized_closedBall_le
