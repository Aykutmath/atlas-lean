import AHHGaussianIntrinsicLogSobolev
import AHHSphereAmbientGaussianLaw

/-! Log-Sobolev with the exact variance of the actual normalized complex
Gaussian ensemble. The coefficient is 1/(4h) in Fisher-information form. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory
open AHHGaussianIntrinsicLogSobolev

namespace AHHRadial

theorem sphereAmbientGaussian_logSobolev (n h : ℕ) (hh : 0 < h)
    (f : SphereAmbient n h → ℝ) (hf : ContDiff ℝ 1 f)
    {c B D : ℝ} (hc : 0 < c) (hlo : ∀ x, c ≤ f x)
    (hB : ∀ x, ‖f x‖ ≤ B) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, f x * Real.log (f x) ∂sphereAmbientGaussianLaw n h) -
      (∫ x, f x ∂sphereAmbientGaussianLaw n h) *
        Real.log (∫ x, f x ∂sphereAmbientGaussianLaw n h) ≤
      (1 / (4 * (h : ℝ))) *
        ∫ x, ‖fderiv ℝ f x‖^2 / f x ∂sphereAmbientGaussianLaw n h := by
  rw [sphereAmbientGaussianLaw_eq_scaled_stdGaussian n h hh]
  have hs : (Real.sqrt (2 * (h : ℝ)))⁻¹ ^ 2 / 2 = 1 / (4 * (h : ℝ)) := by
    have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  simpa only [hs] using scaled_stdGaussian_logSobolev
    ((Real.sqrt (2 * (h : ℝ)))⁻¹) f hf hc hlo hB hD

/-- The quadratic form convenient for smooth angular powers and radial cutoffs. -/
theorem sphereAmbientGaussian_logSobolev_sq (n h : ℕ) (hh : 0 < h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ 1 g)
    {c B D : ℝ} (hc : 0 < c) (hlo : ∀ x, c ≤ g x)
    (hB : ∀ x, ‖g x‖ ≤ B) (hD : ∀ x, ‖fderiv ℝ g x‖ ≤ D) :
    (∫ x, (g x)^2 * Real.log ((g x)^2) ∂sphereAmbientGaussianLaw n h) -
      (∫ x, (g x)^2 ∂sphereAmbientGaussianLaw n h) *
        Real.log (∫ x, (g x)^2 ∂sphereAmbientGaussianLaw n h) ≤
      (1 / (h : ℝ)) * ∫ x, ‖fderiv ℝ g x‖^2 ∂sphereAmbientGaussianLaw n h := by
  have hder (x : SphereAmbient n h) : fderiv ℝ (fun y => (g y)^2) x =
      (2 * g x) • fderiv ℝ g x := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, nsmul_eq_mul] using!
      (((hg.differentiable (by norm_num)) x).hasFDerivAt.pow 2).fderiv
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ g 0)).trans (hD 0)
  have hD' (x : SphereAmbient n h) : ‖fderiv ℝ (fun y => (g y)^2) x‖ ≤ 2 * B * D := by
    rw [hder, norm_smul, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hB x) (by norm_num)) (hD x)
      (norm_nonneg _) (by positivity)
  have hB' (x : SphereAmbient n h) : ‖(g x)^2‖ ≤ B^2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hlo' (x : SphereAmbient n h) : c^2 ≤ (g x)^2 :=
    (sq_le_sq₀ hc.le (hc.trans_le (hlo x)).le).2 (hlo x)
  have hbnd := sphereAmbientGaussian_logSobolev n h hh (fun x => (g x)^2) (hg.pow 2)
    (sq_pos_of_pos hc) hlo' hB' hD'
  have he (x : SphereAmbient n h) : ‖fderiv ℝ (fun y => (g y)^2) x‖^2 / (g x)^2 =
      4 * ‖fderiv ℝ g x‖^2 := by
    rw [hder, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have hx := (hc.trans_le (hlo x)).ne'
    field_simp
    ring
  simp_rw [he] at hbnd
  rw [integral_const_mul] at hbnd
  have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh
  convert hbnd using 1
  field_simp
  <;> ring

#print axioms sphereAmbientGaussian_logSobolev_sq
#print axioms sphereAmbientGaussian_logSobolev
end AHHRadial
