import GaussianCovarianceMoments
import GaussianMomentTailArithmetic
import CovarianceSpectralBounds
import Mathlib.Tactic

/-! Unconditional explicit spectral-norm tail for two-factor iid real Gaussian
covariance. This is the elementary replacement for the product-state theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorTrace
open scoped BigOperators Matrix

namespace GaussianTensorMoments

theorem gaussianCovariance_posSemidef (n h : ℕ) (x : GaussianEntries n h) :
    (gaussianCovariance n h x).PosSemidef := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  simpa only [gaussianCovariance, covariance_eq_mul_transpose,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self (Matrix.of (fun i r => x (i,r)))

theorem tensorGaussianCovariance_posSemidef (n h : ℕ)
    (z : GaussianEntries n h × GaussianEntries n h) :
    (tensorGaussianCovariance n h z).PosSemidef := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  have heq : tensorGaussianCovariance n h z =
      covariance (fun i (r : Fin h × Fin h) => z.1 (i,r.1)*z.2 (i,r.2)) := by
    rw [covariance_eq_sum_outer]
    rfl
  rw [heq, covariance_eq_mul_transpose]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self
      (Matrix.of (fun i (r : Fin h × Fin h) => z.1 (i,r.1)*z.2 (i,r.2)))

/-- The one-factor comparison covariance moment, at moment index h. -/
theorem gaussianCovariance_dimension_trace_moment_le (q h : ℕ)
    (hq : 1 ≤ q) (hh : 0 < h) :
    (∫ x, Matrix.trace ((gaussianCovariance q h x)^h)
      ∂gaussianProductLaw (Fin q × Fin h)) ≤
      (h:ℝ)*(32*(q+h : ℕ))^h := by
  have hp (x : GaussianEntries q h) :
      Matrix.trace ((gaussianCovariance q h x)^h) ≤
        (h:ℝ)*‖gaussianMatrixCLM q h x‖^(2*h) := by
    have heq : matrixCLM (Matrix.of (fun i r => x (i,r))) = gaussianMatrixCLM q h x := rfl
    simpa only [gaussianCovariance, covariance_eq_mul_transpose, Fintype.card_fin, heq]
      using gram_trace_pow_le (Matrix.of (fun i r => x (i,r))) h
  calc
    _ ≤ ∫ x, (h:ℝ)*‖gaussianMatrixCLM q h x‖^(2*h)
        ∂gaussianProductLaw (Fin q × Fin h) :=
      integral_mono (gaussianCovariance_integrable_trace_power q h h hh)
        ((gaussianMatrixCLM_integrable_even_moment q h h).const_mul _) hp
    _ = (h:ℝ)*(∫ x, ‖gaussianMatrixCLM q h x‖^(2*h)
        ∂gaussianProductLaw (Fin q × Fin h)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (gaussianMatrixCLM_dimension_moment_le q h hq)
      (Nat.cast_nonneg h)

/-- Quantitative actual tensor covariance trace-moment estimate. -/
theorem tensorGaussianCovariance_dimension_trace_moment_le (n q h : ℕ)
    (hq : 1 ≤ q) (hh : 0 < h) (hn : n ≤ q^2) :
    (∫ z, Matrix.trace ((tensorGaussianCovariance n h z)^h) ∂tensorGaussianLaw n h) ≤
      (h:ℝ)^2 * (1024*(h+q : ℕ)^2)^h := by
  haveI : Nonempty (Fin h) := Fin.pos_iff_nonempty.mp hh
  have hntrace (x : GaussianEntries q h) : 0 ≤ Matrix.trace ((gaussianCovariance q h x)^h) :=
    (pow_nonneg (norm_nonneg _) _).trans
      (posSemidef_norm_pow_le_trace _ (gaussianCovariance_posSemidef q h x) h)
  have hnonneg : 0 ≤ ∫ x, Matrix.trace ((gaussianCovariance q h x)^h)
      ∂gaussianProductLaw (Fin q × Fin h) := integral_nonneg hntrace
  have hupper := gaussianCovariance_dimension_trace_moment_le q h hq hh
  have hsquare := (sq_le_sq₀ hnonneg (by positivity)).mpr hupper
  calc
    _ ≤ (∫ x, Matrix.trace ((gaussianCovariance q h x)^h)
        ∂gaussianProductLaw (Fin q × Fin h))^2 :=
      tensorGaussianCovariance_trace_moment_le_square n q h h hh hq hn
    _ ≤ ((h:ℝ)*(32*(q+h : ℕ))^h)^2 := hsquare
    _ = _ := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul, Nat.mul_comm h 2, pow_mul]
      congr 1
      push_cast
      ring

/-- The complete explicit two-factor covariance tail, with no external
product-state, Wick, moment, net, or concentration premise. -/
theorem tensorGaussianCovariance_norm_tail (n q h : ℕ)
    (hq : 1 ≤ q) (hh : 0 < h) (hn : n ≤ q^2) :
    (tensorGaussianLaw n h).real
      {z | 2048*(h+q : ℕ)^2 < ‖matrixCLM (tensorGaussianCovariance n h z)‖} ≤
      (h:ℝ)^2/(2:ℝ)^h := by
  haveI : Nonempty (Fin h) := Fin.pos_iff_nonempty.mp hh
  have hdom (z : GaussianEntries n h × GaussianEntries n h) :
      ‖matrixCLM (tensorGaussianCovariance n h z)‖^h ≤
        Matrix.trace ((tensorGaussianCovariance n h z)^h) :=
    posSemidef_norm_pow_le_trace _ (tensorGaussianCovariance_posSemidef n h z) h
  have hnonneg : 0 ≤ᵐ[tensorGaussianLaw n h]
      fun z => Matrix.trace ((tensorGaussianCovariance n h z)^h) :=
    ae_of_all _ (fun z => (pow_nonneg (norm_nonneg _) _).trans (hdom z))
  have hB : (0:ℝ) < 1024*(h+q : ℕ)^2 := by
    have hsum : 0 < h+q := by omega
    positivity
  have hb := measureReal_lt_of_dominated_moment hB h hnonneg
    (tensorGaussianCovariance_integrable_trace_power n h h hh) hdom
    (tensorGaussianCovariance_dimension_trace_moment_le n q h hq hh hn)
  convert hb using 1 <;> norm_num [← mul_assoc]

#print axioms gaussianCovariance_posSemidef
#print axioms tensorGaussianCovariance_posSemidef
#print axioms tensorGaussianCovariance_dimension_trace_moment_le
#print axioms tensorGaussianCovariance_norm_tail

end GaussianTensorMoments
