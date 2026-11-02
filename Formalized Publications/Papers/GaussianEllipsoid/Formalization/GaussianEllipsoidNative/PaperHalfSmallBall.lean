import GaussianEllipsoid.NormBridges
import AllRowsScaledSmallBall
import PaperThetaCap
import PaperBilinearOriginalBlocks
import GaussianBlockAmplification

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianTensorMoments GaussianBilinearTransport
open GaussianPairedBlocks
open scoped BigOperators
namespace GaussianEllipsoid.SmallBall

/-- Paper Lemma main-lemma-4-1, literal floor(d/2) dimension, all d including
the zero-dimensional block cases. The constant12 is universal for all θ. -/
theorem paper_half_determinant_small_ball (d n : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (z : Fin n → ℝ) (hz2 : euclidNorm z = 1)
    (hz : ‖z‖ ≤ θ/Real.sqrt (d:ℝ))
    (M : FrobeniusMatrix (d/2) (d/2)) (t : ℝ) (ht : 0 < t) :
    (bilinearGaussianSampleLaw (d/2) n).real
      {p | ‖bilinearScaled (d:ℝ) (d/2) n z p-M‖ ≤ t*Real.sqrt (d:ℝ)} ≤
      (12*t)^((d/2)*(d/2)) := by
  by_cases hh0 : d/2=0
  · rw [show (12*t)^((d/2)*(d/2)) = 1 by simp [hh0]]
    exact measureReal_le_one
  have hh : 0 < d/2 := Nat.pos_of_ne_zero hh0
  have hd : 0 < d := by omega
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hhR : (0:ℝ) < (d/2:ℕ) := Nat.cast_pos.mpr hh
  have hsum : ∑ i, (z i)^2 = 1 := by
    rw [← euclidNorm_sq, hz2]
    norm_num
  have hcapd : Real.sqrt (d:ℝ)*‖z‖ ≤ θ := by
    have h := (le_div_iff₀ (Real.sqrt_pos.mpr hdR)).mp hz
    simpa only [mul_comm] using h
  have hcaph : Real.sqrt ((d/2:ℕ):ℝ)*‖z‖ ≤ θ :=
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by exact_mod_cast Nat.div_le_self d 2)) (norm_nonneg z)).trans hcapd
  have hcap := squared_coordinate_cap_of_paper_theta hh hθ0 hθ z hcaph
  let u : ℝ := t*(d:ℝ)/((d/2:ℕ):ℝ)
  have hu : 0 < u := by dsimp [u]; positivity
  have hb := gaussian_bilinear_scaled_frobenius_smallball_all_rows (d/2) n hh z
    (σ := 1) (d := (d:ℝ)) (t := u) (by norm_num) hdR hu
    (by simpa using hsum) (by simpa using hcap) M
  have hrad : u*1*((d/2:ℕ):ℝ)/Real.sqrt (d:ℝ) = t*Real.sqrt (d:ℝ) := by
    dsimp [u]
    have hs := Real.sq_sqrt hdR.le
    field_simp
    nlinarith only [hs]
  rw [hrad] at hb
  have hdh : (d:ℝ) ≤ 3*((d/2:ℕ):ℝ) := by exact_mod_cast (show d ≤ 3*(d/2) by omega)
  have hule : u ≤ 3*t := by
    apply (div_le_iff₀ hhR).mpr
    have hm := mul_le_mul_of_nonneg_left hdh ht.le
    nlinarith only [hm]
  exact hb.trans (pow_le_pow_left₀ (by positivity) (by linarith only [hule]) _)

end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.paper_half_determinant_small_ball
