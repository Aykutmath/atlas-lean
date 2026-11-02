import GaussianBilinearContinuity
import Mathlib.Tactic

/-! Borel measurability of the actual bilinear continuity events, proved from
continuity of the explicit finite-coordinate polynomial covariance. -/

noncomputable section
open MeasureTheory GaussianTensorTrace GaussianEllipsoid
open scoped BigOperators Topology Matrix

namespace GaussianTensorMoments

theorem tensorGaussianCovariance_continuous (n h : ℕ) :
    Continuous (tensorGaussianCovariance n h) := by
  apply continuous_pi
  intro r
  apply continuous_pi
  intro s
  simp only [tensorGaussianCovariance, Matrix.sum_apply, Matrix.vecMulVec, Matrix.of_apply]
  fun_prop

theorem tensorGaussianCovariance_norm_continuous (n h : ℕ) :
    Continuous (fun z => ‖matrixCLM (tensorGaussianCovariance n h z)‖) := by
  have hc : Continuous (matrixCLM (α := Fin h × Fin h) (β := Fin h × Fin h)) :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) (m := Fin h × Fin h) (n := Fin h × Fin h)).trans
      LinearMap.toContinuousLinearMap).toLinearMap.continuous_of_finiteDimensional
  exact (hc.comp (tensorGaussianCovariance_continuous n h)).norm

/-- The operator norm itself is continuous, including the normalization at d=0. -/
theorem gaussianBilinearOperator_norm_continuous (n h d : ℕ) :
    Continuous (fun z => ‖gaussianBilinearOperator n h d z‖) := by
  have heq : (fun z => ‖gaussianBilinearOperator n h d z‖) =
      fun z => Real.sqrt (‖matrixCLM (tensorGaussianCovariance n h z)‖ / d) := by
    funext z
    rw [← gaussianBilinearOperator_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [heq]
  exact ((tensorGaussianCovariance_norm_continuous n h).div_const (d:ℝ)).sqrt

/-- Every fixed operator-norm good event is closed and hence Borel. -/
theorem gaussianBilinearOperator_good_isClosed (n h d : ℕ) (L : ℝ) :
    IsClosed {z | ‖gaussianBilinearOperator n h d z‖ ≤ L*Real.sqrt d} :=
  isClosed_le (gaussianBilinearOperator_norm_continuous n h d) continuous_const

theorem gaussianBilinearOperator_bad_measurableSet (n h d : ℕ) (L : ℝ) :
    MeasurableSet {z | L*Real.sqrt d < ‖gaussianBilinearOperator n h d z‖} :=
  (isOpen_lt continuous_const (gaussianBilinearOperator_norm_continuous n h d)).measurableSet

#print axioms gaussianBilinearOperator_norm_continuous
#print axioms gaussianBilinearOperator_bad_measurableSet

end GaussianTensorMoments
