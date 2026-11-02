import PaperScaledSmallBall
import PaperNuclearSmallBall

noncomputable section
open MeasureTheory Finset GaussianMixedNormHelpers
namespace GaussianEllipsoid.SmallBall

/-- Literal scaled-coordinate-block corollary with nu=1/1024,c=1, including
the paper's r^(3/2) radius and exact d^(-1/2) observation normalization. -/
theorem paper_scaled_nuclear_small_ball (r n : ℕ) (hr : 0 < r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (u : Fin n → ℝ) {σ d : ℝ} (hσ : 0 < σ) (hd : 0 < d)
    (husum : ∑ i, (u i)^2 = σ^2) (hu : Real.sqrt (r:ℝ)*‖u‖/σ ≤ θ)
    (C : FrobeniusMatrix r r) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearScaled d r n u p-C) ≤
        (1/1024:ℝ)*σ*(r:ℝ)^(3/2:ℝ)/Real.sqrt d} ≤ Real.exp (-(r*r:ℕ)) := by
  let z : Fin n → ℝ := σ⁻¹ • u
  let b : ℝ := σ*Real.sqrt (r:ℝ)/Real.sqrt d
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  have hb : 0 < b := by dsimp [b]; positivity
  have hzsum : ∑ i, (z i)^2 = 1 := by
    simp only [z,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum,husum]
    field_simp
  have hz : Real.sqrt (r:ℝ)*‖z‖ ≤ θ := by
    simpa only [z,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hσ),
      div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hu
  have hobs (p : BilinearSample r n) : bilinearScaled d r n u p =
      b • bilinearFrobenius r n z p := by
    rw [bilinearScaled,show z = σ⁻¹ • u from rfl,bilinearFrobenius_smul,smul_smul]
    congr 1
    dsimp [b]
    field_simp
  have hthree : (r:ℝ)^(3/2:ℝ) = (r:ℝ)*Real.sqrt (r:ℝ) := by
    rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add hrR,Real.rpow_one,← Real.sqrt_eq_rpow]
  have hradius : (1/1024:ℝ)*σ*(r:ℝ)^(3/2:ℝ)/Real.sqrt d = b*((r:ℝ)/1024) := by
    rw [hthree]
    dsimp [b]
    ring
  have heq : {p | spectralNuclearNorm (bilinearScaled d r n u p-C) ≤
        (1/1024:ℝ)*σ*(r:ℝ)^(3/2:ℝ)/Real.sqrt d} =
      {p | spectralNuclearNorm (bilinearFrobenius r n z p-b⁻¹ • C) ≤ (r:ℝ)/1024} := by
    ext p
    have hdiff : bilinearScaled d r n u p-C =
        b • (bilinearFrobenius r n z p-b⁻¹ • C) := by
      rw [smul_sub,smul_smul,mul_inv_cancel₀ hb.ne',one_smul,hobs]
    simp only [Set.mem_setOf_eq,hdiff,spectralNuclear_smul,abs_of_pos hb,
      hradius,mul_le_mul_iff_right₀ hb]
  rw [heq]
  exact paper_arbitrary_center_nuclear_small_ball r n hr hθ z hzsum hz (b⁻¹ • C)
end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.paper_scaled_nuclear_small_ball
