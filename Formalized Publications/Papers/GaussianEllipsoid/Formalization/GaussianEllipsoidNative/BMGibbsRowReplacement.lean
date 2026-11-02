import BMSmoothRowReplacement
import BMHessianPriorNorms

/-! State-count-free, actual-law one-row replacement for bounded-potential
finite-prior Gibbs log-partitions. This is the specialized universality input
for the Bandeira–Maillard approximate-fitting route. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMSmoothRowReplacement
open BMFiniteGibbsTest BMFiniteGibbsHessian Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMGibbsRowReplacement
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {d m : ℕ}

/-- Error scale independent of the number of states and of the finite prior. -/
def replacementError (D : Data2 κ) (K : ℝ) (d : ℕ) : ℝ :=
  (Real.pi/2) * (Real.sqrt (8/(d:ℝ))*K^2) *
    (diagonalPriorConstant D + pairPriorConstant D)

theorem replacementError_nonneg (D : Data2 κ) (K : ℝ) (d : ℕ) :
    0 ≤ replacementError D K d := by
  have h1 := diagonalPriorConstant_nonneg D
  have h2 := pairPriorConstant_nonneg D
  unfold replacementError
  positivity

/-- Fully proved one-row Gibbs expectation replacement. The prior is arbitrary
and may encode every other row, provided it is held fixed when this row is
replaced. There is no state-count or entropy factor in the bound.

The comparison row is a literal linear form in independent standard Gaussian
coordinates; its covariance equality is a deterministic coefficient identity. -/
theorem one_row_gibbs_replacement
    (D : Data2 κ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hAsym : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2 / (d : ℝ) * Matrix.trace (A a*A b))
    (hd : 0 < d) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K) :
    |(∫ x, logPartition D.toData
        (polynomialFamily (fun a => normalizedQuadratic d (A a)) x)
          ∂gaussianProductLaw (Fin d)) -
      ∫ z, logPartition D.toData
        (polynomialFamily (fun a => linearPolynomial (B a)) z)
          ∂gaussianProductLaw (Fin m)| ≤ replacementError D K d := by
  have h := one_row_smooth_replacement (smoothTest D.toData) (gradientSmoothTest D)
    (fun _ => rfl) A hAsym B hCov hd hK hA
  change |(∫ x, logPartition D.toData
        (polynomialFamily (fun a => normalizedQuadratic d (A a)) x)
          ∂gaussianProductLaw (Fin d)) -
      ∫ z, logPartition D.toData
        (polynomialFamily (fun a => linearPolynomial (B a)) z)
          ∂gaussianProductLaw (Fin m)| ≤
      (Real.pi/2) * (Real.sqrt (8/(d:ℝ))*K^2) *
        ∑ a, ∑ b, ‖boundedHessian D a b‖ at h
  exact h.trans (mul_le_mul_of_nonneg_left (sum_boundedHessian_norm_le D) (by positivity))

/-- The actual one-row replacement error tends to zero, with inverse-square-root
dimension rate and all potential/spectral constants fixed. -/
theorem replacementError_tendsto_zero (D : Data2 κ) (K : ℝ) :
    Tendsto (fun d : ℕ => replacementError D K d) atTop (nhds 0) := by
  have hi : Tendsto (fun d : ℕ => (d : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h8 : Tendsto (fun d : ℕ => 8/(d : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hi
  have hs : Tendsto (fun d : ℕ => Real.sqrt (8/(d : ℝ))) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using! Real.continuous_sqrt.continuousAt.tendsto.comp h8
  have hp : Tendsto (fun _ : ℕ => Real.pi/2) atTop (nhds (Real.pi/2)) := tendsto_const_nhds
  have h := ((hp.mul (hs.mul_const (K^2))).mul_const
    (diagonalPriorConstant D + pairPriorConstant D))
  simpa only [replacementError, zero_mul, mul_zero] using h

#print axioms one_row_gibbs_replacement
#print axioms replacementError_tendsto_zero
end BMGibbsRowReplacement
