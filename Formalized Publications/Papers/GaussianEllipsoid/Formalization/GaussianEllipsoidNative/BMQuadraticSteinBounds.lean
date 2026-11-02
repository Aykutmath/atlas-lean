import BMQuadraticComposition
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments MvPolynomial
open scoped BigOperators

namespace BMQuadraticStein
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual Euclidean operator norm is used throughout, rather than the
supremum norm on the function-valued matrix type. -/
def spectralNorm (A : Matrix ι ι ℝ) : ℝ := ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A‖

/-- The squared Frobenius norm in entries. -/
def frobeniusSq (A : Matrix ι ι ℝ) : ℝ := ∑ i, ∑ j, (A i j)^2

theorem frobeniusSq_nonneg (A : Matrix ι ι ℝ) : 0 ≤ frobeniusSq A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Exact Euclidean operator norm controls the entrywise square energy. -/
theorem frobeniusSq_le_card_spectralNorm_sq (A : Matrix ι ι ℝ) :
    frobeniusSq A ≤ (Fintype.card ι : ℝ) * spectralNorm A ^ 2 := by
  have hcol (j : ι) : (∑ i, (A i j)^2) ≤ spectralNorm A ^ 2 := by
    let e : EuclideanSpace ℝ ι := (EuclideanSpace.basisFun ι ℝ) j
    have h := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A).le_opNorm e
    have hn : ‖e‖ = 1 := (EuclideanSpace.basisFun ι ℝ).norm_eq_one j
    have he : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A e =
        (WithLp.equiv 2 (ι → ℝ)).symm (fun i => A i j) := by
      change (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) e) = _
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toLpLin_apply]
      ext i
      simp [e, EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct]
    rw [hn, mul_one, he] at h
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa [spectralNorm, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hsq
  unfold frobeniusSq
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : ι, spectralNorm A ^ 2 := Finset.sum_le_sum fun j _ => hcol j
    _ = _ := by simp

/-- The genuine spectral norm is submultiplicative. -/
theorem spectralNorm_mul_le (A B : Matrix ι ι ℝ) :
    spectralNorm (A*B) ≤ spectralNorm A * spectralNorm B := by
  unfold spectralNorm
  rw [map_mul]
  exact norm_mul_le _ _

/-- Bounded spectral norm controls the product's Frobenius energy with one
dimension factor, which is the small factor in the normalized Stein kernel. -/
theorem frobeniusSq_mul_le (A B : Matrix ι ι ℝ) :
    frobeniusSq (A*B) ≤ (Fintype.card ι : ℝ) *
      (spectralNorm A)^2 * (spectralNorm B)^2 := by
  calc
    _ ≤ (Fintype.card ι : ℝ) * spectralNorm (A*B)^2 :=
      frobeniusSq_le_card_spectralNorm_sq _
    _ ≤ (Fintype.card ι : ℝ) * (spectralNorm A * spectralNorm B)^2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (show 0 ≤ spectralNorm (A*B) from norm_nonneg _)
          (spectralNorm_mul_le A B) 2) (by positivity)
    _ = _ := by ring

theorem expectation_smul_sq (c : ℝ) (P : MvPolynomial ι ℝ) :
    expectation ((c • P)^2) = c^2 * expectation (P^2) := by
  have he : (c • P)^2 = c^2 • (P^2) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_pow]
    ring
  rw [he, map_smul, smul_eq_mul]

/-- Centered fluctuation of the normalized quadratic Stein kernel. -/
def normalizedKernelFluctuation (d : ℕ) (A B : Matrix ι ι ℝ) : MvPolynomial ι ℝ :=
  (2 / (d : ℝ)) • centeredQuadratic (A*B)

/-- Exact finite-dimensional L² fluctuation bound, requiring no probabilistic
premise and no positive definiteness. -/
theorem normalizedKernelFluctuation_second_moment_le_frobenius
    (d : ℕ) (A B : Matrix ι ι ℝ) :
    expectation (normalizedKernelFluctuation d A B ^ 2) ≤
      8 / (d : ℝ)^2 * frobeniusSq (A*B) := by
  rw [normalizedKernelFluctuation, expectation_smul_sq]
  calc
    _ ≤ (2 / (d : ℝ))^2 * (2 * frobeniusSq (A*B)) :=
      mul_le_mul_of_nonneg_left (expectation_centeredQuadratic_sq_le _) (sq_nonneg _)
    _ = _ := by ring

/-- For d-dimensional matrices, the normalized Stein kernel fluctuation has
second moment ≤ 8‖A‖op²‖B‖op²/d. -/
theorem normalizedKernelFluctuation_second_moment_le_spectral
    (d : ℕ) (hd : 0 < d) (A B : Matrix (Fin d) (Fin d) ℝ) :
    expectation (normalizedKernelFluctuation d A B ^ 2) ≤
      8 / (d : ℝ) * spectralNorm A ^ 2 * spectralNorm B ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  calc
    _ ≤ 8 / (d : ℝ)^2 * frobeniusSq (A*B) :=
      normalizedKernelFluctuation_second_moment_le_frobenius d A B
    _ ≤ 8 / (d : ℝ)^2 * ((d : ℝ) * spectralNorm A ^ 2 * spectralNorm B ^ 2) := by
      exact mul_le_mul_of_nonneg_left (by simpa using frobeniusSq_mul_le A B) (by positivity)
    _ = _ := by field_simp

/-- A polynomial test factor is controlled by its actual Gaussian L² moment.
This is the quantitative remainder bound needed after the vector Stein identity. -/
theorem normalizedKernelFluctuation_test_sq_le
    (d : ℕ) (hd : 0 < d) (A B : Matrix (Fin d) (Fin d) ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    (expectation (normalizedKernelFluctuation d A B * P))^2 ≤
      (8 / (d : ℝ) * spectralNorm A ^ 2 * spectralNorm B ^ 2) * expectation (P^2) := by
  exact (expectation_mul_sq_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (normalizedKernelFluctuation_second_moment_le_spectral d hd A B)
      (expectation_sq_nonneg P))

#print axioms normalizedKernelFluctuation_second_moment_le_spectral
#print axioms normalizedKernelFluctuation_test_sq_le
end BMQuadraticStein
