import AllDimensionGaussianSmallBall
import GaussianCappedRealMoment
import GaussianBilinearSmallBall

/-! Reconstructed all-row core. New source, not byte-exact source recovery.
Real exponent r/2 and singular extended determinants are retained throughout. -/
noncomputable section
open MeasureTheory Finset Matrix
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoid.CappedSimplex
namespace GaussianEllipsoid.SmallBall

theorem reconstructed_sqrt_det_bilinearDriver (r n : ℕ)
    {scale : ℝ} (hscale : 0 < scale) (z : Fin n → ℝ) (g : Fin n → Fin r → ℝ) :
    Real.sqrt (covariance (bilinearDriver scale z g)).det =
      scale^(r*r) * (weightedGram g (fun i => (z i)^2)).det^((r:ℝ)/2) := by
  have hD : 0 ≤ (weightedGram g (fun i => (z i)^2)).det :=
    posSemidef_det_nonneg (weightedGram_posSemidef g (fun i => sq_nonneg (z i)))
  rw [det_covariance_bilinearDriver]
  simp only [Fintype.card_fin]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [show (r:ℝ)*(1/2:ℝ) = (r:ℝ)/2 by ring,
    Real.mul_rpow (by positivity) hD]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (sq_nonneg scale),
    ← Real.rpow_natCast scale 2, ← Real.rpow_mul hscale.le,
    ← Real.rpow_natCast scale (r*r)]
  congr 1
  push_cast
  ring

theorem reconstructed_covarianceInverseJacobian_bilinearDriver (r n : ℕ) (hr : 0 < r)
    {scale : ℝ} (hscale : 0 < scale) (z : Fin n → ℝ) (g : Fin n → Fin r → ℝ) :
    covarianceInverseJacobian (bilinearDriver scale z g) =
      (ENNReal.ofReal (scale^(r*r)))⁻¹ *
        extendedRealDetInv ((r:ℝ)/2) (weightedGram g (fun i => (z i)^2)) := by
  have hD : 0 ≤ (weightedGram g (fun i => (z i)^2)).det :=
    posSemidef_det_nonneg (weightedGram_posSemidef g (fun i => sq_nonneg (z i)))
  have hp : 0 < scale^(r*r) := pow_pos hscale _
  rw [covarianceInverseJacobian, reconstructed_sqrt_det_bilinearDriver r n hscale,
    ENNReal.ofReal_mul hp.le]
  rw [← ENNReal.ofReal_rpow_of_nonneg hD (by positivity : 0 ≤ (r:ℝ)/2)]
  exact ENNReal.mul_inv (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hp))
    (Or.inl ENNReal.ofReal_ne_top)

/-- Exact cancellation of row normalization and the all-dimensional density
constant, followed only by the numerical inequality sqrt(2)*exp(1)<4. -/
theorem reconstructed_all_rows_probability_constant (r : ℕ) (hr : 0 < r)
    {t : ℝ} (ht : 0 < t) :
    (Real.sqrt (r:ℝ))^(r*r) * (2*Real.exp 1)^((r:ℝ)*((r:ℝ)/2)) *
      ((t*Real.sqrt (r:ℝ)/Real.sqrt ((r*r:ℕ):ℝ))^(r*r) *
        Real.exp (((r*r:ℕ):ℝ)/2)) ≤ (4*t)^(r*r) := by
  have hrR : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hs : (Real.sqrt (r:ℝ))^2 = r := Real.sq_sqrt hrR.le
  have hroot : Real.sqrt ((r*r:ℕ):ℝ) = r := by
    push_cast
    rw [← pow_two, Real.sqrt_sq hrR.le]
  have hmoment : (2*Real.exp 1)^((r:ℝ)*((r:ℝ)/2)) =
      (Real.sqrt (2*Real.exp 1))^(r*r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  have hexp : Real.exp (((r*r:ℕ):ℝ)/2) = (Real.sqrt (Real.exp 1))^(r*r) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      Real.exp_one_rpow]
    congr 1
    ring
  rw [hroot, hmoment, hexp, ← mul_pow, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have he : Real.exp 1 < 11/4 := Real.exp_one_lt_d9.trans (by norm_num)
  have hnum : Real.sqrt (2*Real.exp 1) * Real.sqrt (Real.exp 1) ≤ 4 := by
    have h1 := Real.sq_sqrt (show 0 ≤ 2*Real.exp 1 by positivity)
    have h2 := Real.sq_sqrt (Real.exp_nonneg 1)
    have hprod : (Real.sqrt (2*Real.exp 1) * Real.sqrt (Real.exp 1))^2 =
        2*(Real.exp 1)^2 := by rw [mul_pow, h1, h2]; ring
    have hp : 0 ≤ Real.sqrt (2*Real.exp 1) * Real.sqrt (Real.exp 1) := by positivity
    nlinarith [Real.exp_pos 1]
  have hid : Real.sqrt (r:ℝ) * Real.sqrt (2*Real.exp 1) *
      (t*Real.sqrt (r:ℝ)/(r:ℝ)*Real.sqrt (Real.exp 1)) =
      t*(Real.sqrt (2*Real.exp 1)*Real.sqrt (Real.exp 1)) := by
    calc
      _ = (t * Real.sqrt (2*Real.exp 1) * Real.sqrt (Real.exp 1)) *
          (Real.sqrt (r:ℝ))^2 / (r:ℝ) := by ring
      _ = _ := by rw [hs]; field_simp
  rw [hid]
  nlinarith

theorem gaussian_bilinear_frobenius_smallball_all_rows (r n : ℕ) (hr : 0 < r)
    (z : Fin n → ℝ) (hzsum : ∑ i, (z i)^2 = 1)
    (hzcap : ∀ i, (z i)^2 ≤ (2*(r:ℝ))⁻¹)
    (M : EuclideanSpace ℝ (Fin r × Fin r)) {t : ℝ} (ht : 0 < t) :
    bilinearGaussianSampleLaw r n {p | ‖bilinearFlat r n z p-M‖ ≤ t*Real.sqrt (r:ℝ)} ≤
      ENNReal.ofReal ((4*t)^(r*r)) := by
  let μ := Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin r))
  let scale : ℝ := (Real.sqrt (r:ℝ))⁻¹
  have hrR : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hscale : 0 < scale := inv_pos.mpr (Real.sqrt_pos.mpr hrR)
  have hjoint : Measurable (fun p : BilinearSample r n =>
      matrixCLM (bilinearDriver scale z p.1) p.2-M) :=
    (measurable_bilinearFlat r n z).sub measurable_const
  have h := joint_euclideanGaussian_rectangular_closedBall_le_all_dimensions μ
    (by simp; positivity : 0 < Fintype.card (Fin r × Fin r))
    (fun g => bilinearDriver scale z g) (fun _ => M)
    (R := t*Real.sqrt (r:ℝ)) (by positivity) hjoint
  have hJac : (∫⁻ g : Fin n → Fin r → ℝ,
      covarianceInverseJacobian (bilinearDriver scale z g) ∂μ) =
      ENNReal.ofReal ((Real.sqrt (r:ℝ))^(r*r)) *
        extendedRealMoment μ ((r:ℝ)/2) (fun i => (z i)^2) := by
    simp_rw [reconstructed_covarianceInverseJacobian_bilinearDriver r n hr hscale]
    have hc : (ENNReal.ofReal (scale^(r*r)))⁻¹ =
        ENNReal.ofReal ((Real.sqrt (r:ℝ))^(r*r)) := by
      simp only [scale, inv_pow]
      rw [ENNReal.ofReal_inv_of_pos (pow_pos (Real.sqrt_pos.mpr hrR) _), inv_inv]
    rw [hc, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rfl
  rw [hJac] at h
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have hMoment := gaussian_capped_real_moment r hr
    (w := fun i => (z i)^2) ⟨fun i => ⟨sq_nonneg _, hzcap i⟩, hzsum⟩
  calc
    _ ≤ (ENNReal.ofReal ((Real.sqrt (r:ℝ))^(r*r)) *
        extendedRealMoment μ ((r:ℝ)/2) (fun i => (z i)^2)) *
      ENNReal.ofReal ((t*Real.sqrt (r:ℝ)/Real.sqrt ((r*r:ℕ):ℝ))^(r*r) *
        Real.exp (((r*r:ℕ):ℝ)/2)) := h
    _ ≤ (ENNReal.ofReal ((Real.sqrt (r:ℝ))^(r*r)) *
        ENNReal.ofReal ((2*Real.exp 1)^((r:ℝ)*((r:ℝ)/2)))) *
      ENNReal.ofReal ((t*Real.sqrt (r:ℝ)/Real.sqrt ((r*r:ℕ):ℝ))^(r*r) *
        Real.exp (((r*r:ℕ):ℝ)/2)) :=
      mul_le_mul_left (mul_le_mul_right hMoment _) _
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (reconstructed_all_rows_probability_constant r hr ht)
end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_frobenius_smallball_all_rows
