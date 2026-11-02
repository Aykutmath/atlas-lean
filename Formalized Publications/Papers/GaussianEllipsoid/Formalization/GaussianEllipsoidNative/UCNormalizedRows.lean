import UCGibbsOneRow
import BMGaussianEquivalent
import GaussianEllipsoid.Coordinates
import GaussianEllipsoid.NormBridges
import GaussianEllipsoid.GaussianProbability

set_option autoImplicit false

/-! Exact normalizations linking the actual project measurementQ to the
state-count-free diffuse Gibbs replacement theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMGaussianEquivalent
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCNormalizedRows
variable {d : ℕ}

def scale (d : ℕ) : ℝ := Real.sqrt d / Real.sqrt 2

theorem scale_nonneg (d : ℕ) : 0 ≤ scale d := by unfold scale; positivity

theorem scale_sq (d : ℕ) : scale d^2 = (d:ℝ)/2 := by
  rw [scale, div_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

def scaled (A : Square d) : Square d := scale d • A

theorem spectralNorm_eq_matrixOpNorm (A : Square d) :
    spectralNorm A = matrixOpNorm A := by
  rw [matrixOpNorm, Matrix.l2_opNorm_def]
  rfl

theorem scaled_spectral_sq (A : Square d) :
    spectralNorm (scaled A)^2 = (d:ℝ)/2 * matrixOpNorm A^2 := by
  rw [spectralNorm_eq_matrixOpNorm, scaled, matrixOpNorm_smul,
    Real.norm_eq_abs, abs_of_nonneg (scale_nonneg d), mul_pow, scale_sq]

theorem scaled_frobeniusSq (A : Square d) :
    frobeniusSq (scaled A) = (d:ℝ)/2 * frobeniusNorm A^2 := by
  rw [show frobeniusSq (scaled A) = frobeniusNorm (scaled A)^2 from
    (frobeniusNorm_sq (scaled A)).symm, scaled, frobeniusNorm_smul,
    Real.norm_eq_abs, abs_of_nonneg (scale_nonneg d), mul_pow, scale_sq]

theorem scaled_transpose (A : Square d) (hA : A.transpose = A) :
    (scaled A).transpose = scaled A := by simp [scaled, hA]

/-- The normalized quadratic endpoint is exactly the paper's centered row. -/
theorem eval_scaled (hd : 0 < d) (A : Square d) (x : Vector d) :
    MvPolynomial.eval x (normalizedQuadratic d (scaled A)) =
      (quadratic A x - Matrix.trace A)/Real.sqrt 2 := by
  have hd0 : Real.sqrt (d:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  rw [normalizedQuadratic, scaled, centeredQuadratic_smul, smul_smul]
  simp only [MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_centeredQuadratic]
  have he : (∑ i, ∑ j, A i j * (x i*x j)) = quadratic A x := by
    rw [quadratic_eq_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  unfold scale
  field_simp

/-- The full-entry Gaussian coefficients simplify to the matrix entries. -/
theorem coefficient_scaled (hd : 0 < d) (A : Square d) (k : Fin (d*d)) :
    gaussianCoefficients (scaled A) k =
      A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  have hd0 : Real.sqrt (d:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hd)
  have h20 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  simp only [gaussianCoefficients, scaled, Matrix.smul_apply, smul_eq_mul, scale]
  rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

/-- Literal full-entry isonormal Gaussian row for symmetric test matrices. -/
def gaussianRow (A : Square d) (z : Fin (d*d) → ℝ) : ℝ :=
  ∑ k, A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2*z k

theorem eval_gaussian_scaled (hd : 0 < d) (A : Square d) (z : Fin (d*d) → ℝ) :
    MvPolynomial.eval z (linearPolynomial (gaussianCoefficients (scaled A))) =
      gaussianRow A z := by
  simp only [linearPolynomial, map_sum, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, coefficient_scaled hd,
    gaussianRow]

/-- Actual UC row comparison with no Gaussianity, covariance, or Stein
assumptions remaining. Matrices use the project's norms and quadratic form. -/
theorem actual_diffuse_row_replacement {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : Data2 κ) (v : κ → ℝ) (A : κ → Square d)
    (hAsym : ∀ a, (A a).transpose = A a) (hd : 0 < d)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hOp : ∀ a, matrixOpNorm (A a) ≤ τ)
    (hF : ∀ a, frobeniusNorm (A a) ≤ 1) :
    |(∫ x, logPartition D.toData
        (fun a => (quadratic (A a) x-Matrix.trace (A a))/Real.sqrt 2 + v a)
          ∂gaussianVectorLaw d) -
      ∫ z, logPartition D.toData (fun a => gaussianRow (A a) z + v a)
          ∂gaussianProductLaw (Fin (d*d))| ≤
      ((Real.pi/2)*Real.sqrt 2*(diagonalPriorConstant D + pairPriorConstant D))*τ := by
  have hAn a : spectralNorm (scaled (A a))^2 ≤ (d:ℝ)/2*τ^2 := by
    rw [scaled_spectral_sq]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (matrixOpNorm_nonneg _) (hOp a) 2) (by positivity)
  have hFn a : frobeniusSq (scaled (A a)) ≤ (d:ℝ)/2 := by
    rw [scaled_frobeniusSq]
    have h := pow_le_pow_left₀ (frobeniusNorm_nonneg _) (hF a) 2
    simpa only [one_pow, mul_one] using mul_le_mul_of_nonneg_left h
      (by positivity : 0 ≤ (d:ℝ)/2)
  have h := UCGibbsOneRow.diffuse_shifted_gibbs_replacement D v
    (fun a => scaled (A a)) (fun a => scaled_transpose _ (hAsym a))
    (fun a => gaussianCoefficients (scaled (A a)))
    (fun a b => gaussianCoefficients_covariance _ _ (scaled_transpose _ (hAsym b)))
    hd τ hτ hAn hFn
  simpa only [polynomialFamily, ContinuousMap.coe_mk, Pi.add_def,
    eval_scaled hd, eval_gaussian_scaled hd, gaussianVectorLaw, gaussianProductLaw] using h

#print axioms actual_diffuse_row_replacement
end GaussianEllipsoid.UCNormalizedRows
