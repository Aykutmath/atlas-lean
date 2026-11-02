import AllRowsNuclearSmallBall
import PaperThetaCap

noncomputable section
open MeasureTheory Finset GaussianMixedNormHelpers
namespace GaussianEllipsoid.SmallBall

/-- Paper Theorem5.7 / Section7 arbitrary-center block lemma with explicit
universal constants ν_sb=1/1024 and c_sb=1, all positive row dimensions. -/
theorem paper_arbitrary_center_nuclear_small_ball (r n : ℕ) (hr : 0 < r)
    {θ : ℝ} (hθ : θ < 1/Real.sqrt 2)
    (z : Fin n → ℝ) (hzsum : ∑ i, (z i)^2 = 1)
    (hz : Real.sqrt (r:ℝ)*‖z‖ ≤ θ) (M : FrobeniusMatrix r r) :
    (bilinearGaussianSampleLaw r n).real
      {p | spectralNuclearNorm (bilinearFrobenius r n z p-M) ≤ (r:ℝ)/1024} ≤
        Real.exp (-(r*r:ℕ)) := by
  have hzn : z ≠ 0 := by
    intro heq
    simp [heq] at hzsum
  have hθ0 : 0 < θ := (mul_pos
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hr)) (norm_pos_iff.mpr hzn)).trans_le hz
  exact gaussian_bilinear_nuclear_smallball_unit_all_rows r n hr z hzsum
    (squared_coordinate_cap_of_paper_theta hr hθ0 hθ z hz) M
end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.paper_arbitrary_center_nuclear_small_ball
