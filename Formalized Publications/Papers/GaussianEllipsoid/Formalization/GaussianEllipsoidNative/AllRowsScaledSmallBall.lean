import AllRowsNuclearSmallBall
import DisjointBilinearSmallBall

/-! Reconstructed from preserved scaled consumers and the recovered scalar
linearity proof. New source; all-row prerequisite verification pending. -/
noncomputable section
open MeasureTheory Finset GaussianMixedNormHelpers
namespace GaussianEllipsoid.SmallBall

theorem gaussian_bilinear_scaled_frobenius_smallball_all_rows (r n : ℕ)
    (hr : 0 < r) (u : Fin n → ℝ) {σ d t : ℝ}
    (hσ : 0 < σ) (hd : 0 < d) (ht : 0 < t)
    (husum : ∑ i, (u i)^2 = σ^2)
    (hucap : ∀ i, (u i)^2 ≤ σ^2 * (2*(r:ℝ))⁻¹)
    (C : FrobeniusMatrix r r) :
    (bilinearGaussianSampleLaw r n).real
      {p | ‖bilinearScaled d r n u p-C‖ ≤ t*σ*(r:ℝ)/Real.sqrt d} ≤
        (4*t)^(r*r) := by
  let z : Fin n → ℝ := σ⁻¹ • u
  let b : ℝ := σ*Real.sqrt (r:ℝ)/Real.sqrt d
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hb : 0 < b := by dsimp [b]; positivity
  have hzsum : ∑ i, (z i)^2 = 1 := by
    simp only [z, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, husum]
    field_simp
  have hzcap : ∀ i, (z i)^2 ≤ (2*(r:ℝ))⁻¹ := by
    intro i
    calc
      (z i)^2 = (σ⁻¹)^2 * (u i)^2 := by
        simp only [z, Pi.smul_apply, smul_eq_mul, mul_pow]
      _ ≤ (σ⁻¹)^2 * (σ^2 * (2*(r:ℝ))⁻¹) :=
        mul_le_mul_of_nonneg_left (hucap i) (sq_nonneg _)
      _ = _ := by field_simp
  have hobs (p : BilinearSample r n) : bilinearScaled d r n u p =
      b • bilinearFrobenius r n z p := by
    rw [bilinearScaled, show z = σ⁻¹ • u from rfl, bilinearFrobenius_smul, smul_smul]
    congr 1
    dsimp [b]
    field_simp
  have hradius : t*σ*(r:ℝ)/Real.sqrt d = b*(t*Real.sqrt (r:ℝ)) := by
    dsimp [b]
    rw [show σ * Real.sqrt (r:ℝ) / Real.sqrt d * (t * Real.sqrt (r:ℝ)) =
      t * σ * (Real.sqrt (r:ℝ))^2 / Real.sqrt d by ring, Real.sq_sqrt hrR.le]
  have heq : {p | ‖bilinearScaled d r n u p-C‖ ≤ t*σ*(r:ℝ)/Real.sqrt d} =
      {p | ‖bilinearFrobenius r n z p-b⁻¹ • C‖ ≤ t*Real.sqrt (r:ℝ)} := by
    ext p
    have hdiff : bilinearScaled d r n u p-C =
        b • (bilinearFrobenius r n z p-b⁻¹ • C) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hb.ne', one_smul, hobs]
    simp only [Set.mem_setOf_eq, hdiff, norm_smul, Real.norm_eq_abs,
      abs_of_pos hb, hradius, mul_le_mul_iff_right₀ hb]
  rw [heq]
  exact gaussian_bilinear_frobenius_smallball_real_all_rows r n hr z hzsum hzcap
    (b⁻¹ • C) ht

end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.gaussian_bilinear_scaled_frobenius_smallball_all_rows
