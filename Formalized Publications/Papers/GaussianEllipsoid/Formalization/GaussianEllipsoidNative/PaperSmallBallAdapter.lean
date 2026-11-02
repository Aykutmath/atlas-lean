import AllRowsBilinearSmallBall
import PaperThetaCap

noncomputable section
open Finset MeasureTheory
namespace GaussianEllipsoid.SmallBall

/-- Paper Proposition 5.4, all positive row dimensions, arbitrary centers,
and its full theta range. The proof gives the stronger uniform constant4. -/
theorem paper_determinant_frobenius_small_ball (r n : ℕ) (hr : 0 < r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (z : Fin n → ℝ) (hzsum : ∑ i, (z i)^2 = 1)
    (hz : Real.sqrt (r:ℝ)*‖z‖ ≤ θ)
    (M : EuclideanSpace ℝ (Fin r × Fin r)) {t : ℝ} (ht : 0 < t) :
    bilinearGaussianSampleLaw r n {p | ‖bilinearFlat r n z p-M‖ ≤ t*Real.sqrt (r:ℝ)} ≤
      ENNReal.ofReal ((4*t)^(r*r)) :=
  gaussian_bilinear_frobenius_smallball_all_rows r n hr z hzsum
    (squared_coordinate_cap_of_paper_theta hr hθ0 hθ z hz) M ht
end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.paper_determinant_frobenius_small_ball
