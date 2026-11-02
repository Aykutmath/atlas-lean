import BMGibbsRowReplacement
import Mathlib.LinearAlgebra.Matrix.Trace

open BMQuadraticStein BMGibbsRowReplacement BMFiniteGibbsHessian
open BMFiniteGibbsTest BMAffineSmooth BMSmoothQuadraticComposition
open MeasureTheory GaussianTensorMoments
open scoped BigOperators BoundedContinuousFunction
namespace BMGaussianEquivalent

/-- Full-entry realization of the Gaussian-equivalent linear measurements. -/
noncomputable def gaussianCoefficients {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (k : Fin (d*d)) : ℝ :=
  Real.sqrt (2/(d:ℝ)) * A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The covariance equality is proved from the literal coefficients, rather
than remaining as a premise of the Gibbs comparison. -/
theorem gaussianCoefficients_covariance {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℝ)
    (hB : B.transpose = B) :
    (∑ k, gaussianCoefficients A k * gaussianCoefficients B k) =
      2/(d:ℝ)*Matrix.trace (A*B) := by
  have hBij (i j : Fin d) : B j i = B i j := by
    exact congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hB
  rw [← (finProdFinEquiv : Fin d × Fin d ≃ Fin (d*d)).sum_comp
    (fun k => gaussianCoefficients A k * gaussianCoefficients B k)]
  simp only [gaussianCoefficients, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  have hs : (Real.sqrt (2/(d:ℝ)))^2 = 2/(d:ℝ) := Real.sq_sqrt (by positivity)
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hBij]
  calc
    _ = (Real.sqrt (2/(d:ℝ)))^2 * (A i j * B j i) := by ring
    _ = _ := by rw [hs]

/-- Actual GOE row built from d² independent real standard Gaussian entries.
This has diagonal variance2/d and off-diagonal variance1/d. -/
noncomputable def symmetrizedGaussianMatrix (d : ℕ) (z : Fin (d*d) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
      Real.sqrt (2/(d:ℝ)) * (z (finProdFinEquiv (i,j)) + z (finProdFinEquiv (j,i))) / 2

theorem symmetrizedGaussianMatrix_transpose (d : ℕ) (z : Fin (d*d) → ℝ) :
    (symmetrizedGaussianMatrix d z).transpose = symmetrizedGaussianMatrix d z := by
  ext i j
  simp [symmetrizedGaussianMatrix, add_comm]

theorem eval_gaussianCoefficients {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (z : Fin (d*d) → ℝ) :
    MvPolynomial.eval z (linearPolynomial (gaussianCoefficients A)) =
      Real.sqrt (2/(d:ℝ)) * ∑ i, ∑ j, A i j * z (finProdFinEquiv (i,j)) := by
  simp only [linearPolynomial, map_sum, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [← (finProdFinEquiv : Fin d × Fin d ≃ Fin (d*d)).sum_comp
    (fun k => gaussianCoefficients A k * z k)]
  simp only [gaussianCoefficients, Equiv.symm_apply_apply, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

/-- Exact trace observable of the constructed Gaussian-equivalent matrix. -/
theorem trace_symmetrizedGaussianMatrix_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.transpose = A) (z : Fin (d*d) → ℝ) :
    Matrix.trace (symmetrizedGaussianMatrix d z * A) =
      MvPolynomial.eval z (linearPolynomial (gaussianCoefficients A)) := by
  have hAij (i j : Fin d) : A j i = A i j :=
    congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hA
  rw [eval_gaussianCoefficients]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, symmetrizedGaussianMatrix]
  have hh : (∑ i, ∑ j, z (finProdFinEquiv (j,i)) * A i j) =
      ∑ i, ∑ j, z (finProdFinEquiv (i,j)) * A i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hAij]
  simp_rw [hAij]
  simp only [mul_add, add_div, add_mul, Finset.sum_add_distrib]
  have hterm (i j : Fin d) (a : ℝ) :
      (Real.sqrt (2/(d:ℝ))*a/2)*A i j =
        (Real.sqrt (2/(d:ℝ))/2)*(a*A i j) := by ring
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  rw [hh]
  have he : (∑ i, ∑ j, A i j * z (finProdFinEquiv (i,j))) =
      ∑ i, ∑ j, z (finProdFinEquiv (i,j))*A i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

/-- The actual full-entry Gaussian row replacement, with no covariance-match
hypothesis left to the caller. -/
theorem one_row_gibbs_replacement_actual {κ : Type*} [Fintype κ] [DecidableEq κ]
    {d : ℕ} (D : Data2 κ) (A : κ → Matrix (Fin d) (Fin d) ℝ)
    (hAsym : ∀ a, (A a).transpose = A a) (hd : 0 < d)
    {K : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K) :
    |(∫ x, logPartition D.toData
        (polynomialFamily (fun a => normalizedQuadratic d (A a)) x)
          ∂gaussianProductLaw (Fin d)) -
      ∫ z, logPartition D.toData (fun a => Matrix.trace (symmetrizedGaussianMatrix d z*A a))
          ∂gaussianProductLaw (Fin (d*d))| ≤ replacementError D K d := by
  have h := one_row_gibbs_replacement D A hAsym (fun a => gaussianCoefficients (A a))
    (fun a b => gaussianCoefficients_covariance (A a) (A b) (hAsym b)) hd hK hA
  simpa only [polynomialFamily, ContinuousMap.coe_mk,
    trace_symmetrizedGaussianMatrix_mul _ (hAsym _)] using h

#print axioms gaussianCoefficients_covariance
#print axioms symmetrizedGaussianMatrix_transpose
#print axioms eval_gaussianCoefficients
#print axioms trace_symmetrizedGaussianMatrix_mul
#print axioms one_row_gibbs_replacement_actual
end BMGaussianEquivalent
