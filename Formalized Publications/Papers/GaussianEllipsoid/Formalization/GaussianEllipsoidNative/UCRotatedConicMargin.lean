import UCMatrixRotation
import UCFixedRankGeometry
import UCPeelingSmallTail

/-! Exact conic-loss perturbation and positive constants for the final
Grassmann/frame reduction. -/
noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid.UCRotatedConicMargin
open UCMatrixRotation UCFixedRankGeometry UCContinuityGeometry UCUniformContinuity UCPeelingSmallTail

/-- Rotation changes the actual centered conic margin by at most 4C||O-I||
for a Frobenius-unit PSD matrix on the actual continuity event. -/
theorem conicMargin_rotation_abs {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (A : Square d) (hA : A.PosSemidef) (hF : frobeniusNorm A = 1)
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (C : ℝ) (hC : ‖empiricalOperator x‖ ≤ C) :
    |conicMargin x (conjugate O A)-conicMargin x A| ≤
      4*C*‖(O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))-1‖ := by
  have hCn : 0 ≤ C := (norm_nonneg (empiricalOperator x)).trans hC
  have hlip := conicMargin_abs_sub_le hn x (conjugate O A) A
    (psd_transpose _ (conjugate_posSemidef O hA)) (psd_transpose _ hA) C hC
  have hrot := conjugate_sub_frobenius_le O A
  rw [hF,mul_one] at hrot
  exact hlip.trans ((mul_le_mul_of_nonneg_left hrot (by positivity)).trans_eq (by ring))

 def finalMargin (a c : ℝ) : ℝ := min peeledMargin (tailCutoff a*c/4)
 def rotationTolerance (a c : ℝ) : ℝ := tailCutoff a*c/(16*(continuityConstant a+1))

 theorem finalMargin_pos {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : 0 < finalMargin a c := by
  unfold finalMargin
  exact lt_min peeledMargin_pos (by positivity [tailCutoff_pos ha])

 theorem rotationTolerance_pos {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : 0 < rotationTolerance a c := by
  unfold rotationTolerance
  positivity [tailCutoff_pos ha,continuityConstant_pos ha]

 theorem finalMargin_le_peeledMargin (a c : ℝ) : finalMargin a c ≤ peeledMargin := min_le_left _ _

/-- The final constants force every aligned non-small-tail witness into the
fixed-frame diffuse bad event, with room to spare in its strict inequality. -/
theorem rotated_conic_lt_scaled {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {d n : ℕ} (hn : 0 < n) (x : Sample d n)
    (A : Square d) (hA : A.PosSemidef) (hF : frobeniusNorm A = 1)
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (hO : ‖(O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))-1‖ < rotationTolerance a c)
    (hC : ‖empiricalOperator x‖ ≤ continuityConstant a)
    (ρ : ℝ) (hρ : tailCutoff a < ρ) (hbad : conicMargin x A < finalMargin a c) :
    conicMargin x (conjugate O A) < ρ*c := by
  have hCn := (continuityConstant_pos ha).le
  have ht := (abs_le.mp (conicMargin_rotation_abs hn x A hA hF O (continuityConstant a) hC)).2
  have he : 4*continuityConstant a*rotationTolerance a c ≤ tailCutoff a*c/4 := by
    have htpos := rotationTolerance_pos ha hc
    have hmul := mul_le_mul_of_nonneg_right (show continuityConstant a ≤ continuityConstant a+1 by linarith) htpos.le
    have hh : (continuityConstant a+1)*rotationTolerance a c = tailCutoff a*c/16 := by
      unfold rotationTolerance
      have hden : continuityConstant a+1 ≠ 0 := by positivity
      field_simp
    rw [hh] at hmul
    linarith
  have hnear := mul_le_mul_of_nonneg_left hO.le (show 0 ≤ 4*continuityConstant a by positivity)
  have hmain := min_le_right peeledMargin (tailCutoff a*c/4)
  have hscale := mul_lt_mul_of_pos_right hρ hc
  change finalMargin a c ≤ tailCutoff a*c/4 at hmain
  have hδ : 0 < tailCutoff a := tailCutoff_pos ha
  nlinarith

#print axioms conicMargin_rotation_abs
#print axioms rotated_conic_lt_scaled
end GaussianEllipsoid.UCRotatedConicMargin
