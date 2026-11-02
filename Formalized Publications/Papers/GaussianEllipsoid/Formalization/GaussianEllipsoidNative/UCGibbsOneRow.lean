import UCFrobeniusReplacement
import BMHessianPriorNorms

/-! An actual-law, state-count-free UC one-row Gibbs replacement. The only
matrix inputs are deterministic symmetry, covariance, and product energy.
Arbitrary deterministic state-dependent shifts are allowed. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open GaussianEllipsoid.UCFrobeniusReplacement
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCGibbsOneRow
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d m : ℕ}

/-- A shift in the current row preserves the bounded Hessian estimates. -/
theorem shifted_gibbs_replacement
    (D : Data2 κ) (v : κ → ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hAsym : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2/(d:ℝ)*Matrix.trace (A a*A b))
    (R : ℝ) (hR : 0 ≤ R)
    (hAB : ∀ a b, 8/(d:ℝ)^2 * frobeniusSq (A a*A b) ≤ R^2) :
    |(∫ x, logPartition D.toData
        (polynomialFamily (fun a => normalizedQuadratic d (A a)) x + v)
          ∂gaussianProductLaw (Fin d)) -
      ∫ z, logPartition D.toData
        (polynomialFamily (fun a => linearPolynomial (B a)) z + v)
          ∂gaussianProductLaw (Fin m)| ≤
      (Real.pi/2)*R*(diagonalPriorConstant D + pairPriorConstant D) := by
  let F := affineTest (smoothTest D.toData) 1 v
  let H := fun a => affineTest (gradientSmoothTest D a) 1 v
  have hH : ∀ a, (H a).value = F.gradient a := by
    intro a
    simp only [H, F, affineTest, one_smul]
    rfl
  have h := one_row_smooth_replacement F H hH A hAsym B hCov R hR hAB
  have hsum : (∑ a, ∑ b, ‖(H a).gradient b‖) ≤
      diagonalPriorConstant D + pairPriorConstant D := by
    apply le_trans _ (sum_boundedHessian_norm_le D)
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    simp only [H, affineTest, one_smul]
    exact BoundedContinuousFunction.norm_compContinuous_le _ _
  have h' := h.trans (mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by positivity) hR))
  simpa only [F, affineTest, smoothTest, BoundedContinuousFunction.compContinuous_apply,
    boundedLogPartition, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    affineMap, ContinuousMap.coe_mk, one_smul] using h'

/-- For the exact UC d/2 scale the replacement error is O(τ), uniformly in
sample dimension, state count, prior, and state-dependent current-row shifts. -/
theorem diffuse_shifted_gibbs_replacement
    (D : Data2 κ) (v : κ → ℝ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (hAsym : ∀ a, (A a).transpose = A a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2/(d:ℝ)*Matrix.trace (A a*A b))
    (hd : 0 < d) (τ : ℝ) (hτ : 0 ≤ τ)
    (hA : ∀ a, spectralNorm (A a)^2 ≤ (d:ℝ)/2*τ^2)
    (hF : ∀ a, frobeniusSq (A a) ≤ (d:ℝ)/2) :
    |(∫ x, logPartition D.toData
        (polynomialFamily (fun a => normalizedQuadratic d (A a)) x + v)
          ∂gaussianProductLaw (Fin d)) -
      ∫ z, logPartition D.toData
        (polynomialFamily (fun a => linearPolynomial (B a)) z + v)
          ∂gaussianProductLaw (Fin m)| ≤
      ((Real.pi/2)*Real.sqrt 2*(diagonalPriorConstant D + pairPriorConstant D))*τ := by
  have h := shifted_gibbs_replacement D v A hAsym B hCov (Real.sqrt 2*τ)
    (by positivity) (fun a b => UCFrobeniusStein.diffuse_product_energy d hd
      (A a) (A b) τ (hA a) (hF b))
  exact h.trans_eq (by ring)

#print axioms shifted_gibbs_replacement
#print axioms diffuse_shifted_gibbs_replacement
end GaussianEllipsoid.UCGibbsOneRow
