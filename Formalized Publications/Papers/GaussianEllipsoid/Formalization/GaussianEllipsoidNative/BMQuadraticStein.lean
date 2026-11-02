import GaussianMultivariateStein
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Centered Gaussian quadratic-form identities, using the actual product
standard Gaussian measure. No abstract integration-by-parts hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments MvPolynomial
open scoped BigOperators

namespace BMQuadraticStein
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Gaussian expectation as a linear functional on polynomials. -/
def expectation : MvPolynomial ι ℝ →ₗ[ℝ] ℝ where
  toFun P := ∫ x, MvPolynomial.eval x P ∂gaussianProductLaw ι
  map_add' P Q := by
    simp only [eval_add]
    exact integral_add (gaussianProductLaw_integrable_polynomial P)
      (gaussianProductLaw_integrable_polynomial Q)
  map_smul' c P := by
    simp only [MvPolynomial.smul_eq_C_mul, eval_mul, eval_C, smul_eq_mul]
    exact integral_const_mul c _

@[simp] theorem expectation_one : expectation (1 : MvPolynomial ι ℝ) = 1 := by
  simp [expectation]

@[simp] theorem expectation_C (c : ℝ) : expectation (C c : MvPolynomial ι ℝ) = c := by
  simp [expectation]

theorem expectation_coordinate_mul (i : ι) (P : MvPolynomial ι ℝ) :
    expectation (X i * P) = expectation (pderiv i P) := by
  simpa only [expectation, LinearMap.coe_mk, AddHom.coe_mk, eval_mul, eval_X]
    using gaussianProductLaw_polynomial_stein P i

/-- A centered coordinate pair admits an exact first-order Stein identity. -/
theorem expectation_centered_pair_mul (i j : ι) (P : MvPolynomial ι ℝ) :
    expectation ((X i * X j - if i = j then 1 else 0) * P) =
      expectation (X j * pderiv i P) := by
  have h := expectation_coordinate_mul i (X j * P)
  rw [pderiv_mul] at h
  by_cases hij : i = j
  · subst j
    simp only [pderiv_X_self, one_mul, map_add, ← mul_assoc] at h
    simp only [if_true, sub_mul, one_mul, map_sub]
    linarith
  · simp only [pderiv_X_of_ne (Ne.symm hij), zero_mul, zero_add] at h
    simpa only [if_neg hij, sub_zero, mul_assoc] using h

/-- The corresponding second-order Stein identity. -/
theorem expectation_centered_pair_mul_second (i j : ι) (P : MvPolynomial ι ℝ) :
    expectation ((X i * X j - if i = j then 1 else 0) * P) =
      expectation (pderiv j (pderiv i P)) := by
  rw [expectation_centered_pair_mul, expectation_coordinate_mul]

/-- Polynomial representation of xᵀAx − tr A, without symmetry assumptions. -/
def centeredQuadratic (A : Matrix ι ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i, ∑ j, A i j • (X i * X j - if i = j then 1 else 0)

/-- Exact evaluated coordinates, including the diagonal centering. -/
theorem eval_centeredQuadratic (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    eval x (centeredQuadratic A) =
      (∑ i, ∑ j, A i j * (x i * x j)) - Matrix.trace A := by
  simp only [centeredQuadratic, map_sum, MvPolynomial.smul_eq_C_mul, eval_sub,
    eval_mul, eval_X, eval_C]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  simp [Matrix.trace, apply_ite (eval x), mul_ite]

/-- Full centered quadratic-form Stein identity, first-order form. -/
theorem expectation_centeredQuadratic_mul (A : Matrix ι ι ℝ)
    (P : MvPolynomial ι ℝ) :
    expectation (centeredQuadratic A * P) =
      ∑ i, ∑ j, A i j * expectation (X j * pderiv i P) := by
  simp only [centeredQuadratic, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    smul_eq_mul, expectation_centered_pair_mul]

/-- Full centered quadratic-form Stein identity, Hessian form. -/
theorem expectation_centeredQuadratic_mul_second (A : Matrix ι ι ℝ)
    (P : MvPolynomial ι ℝ) :
    expectation (centeredQuadratic A * P) =
      ∑ i, ∑ j, A i j * expectation (pderiv j (pderiv i P)) := by
  rw [expectation_centeredQuadratic_mul]
  simp_rw [expectation_coordinate_mul]

@[simp] theorem expectation_centeredQuadratic (A : Matrix ι ι ℝ) :
    expectation (centeredQuadratic A) = 0 := by
  simpa using expectation_centeredQuadratic_mul_second A 1

/-- Gradient of a general (possibly nonsymmetric) centered quadratic form. -/
theorem pderiv_centeredQuadratic (A : Matrix ι ι ℝ) (k : ι) :
    pderiv k (centeredQuadratic A) = ∑ j, (A k j + A j k) • X j := by
  simp only [centeredQuadratic, map_sum, Derivation.map_smul, map_sub,
    pderiv_mul, pderiv_X]
  simp only [Pi.single_apply]
  simp only [apply_ite (pderiv k), pderiv_one, map_zero, ite_self, sub_zero]
  simp_rw [add_smul, smul_add, Finset.sum_add_distrib]
  congr 1
  · simp [ite_mul, smul_ite, Finset.sum_ite_irrel]
  · simp [mul_ite, smul_ite]

/-- Exact covariance matching for Gaussian quadratic forms. -/
theorem expectation_centeredQuadratic_mul_centeredQuadratic
    (A B : Matrix ι ι ℝ) :
    expectation (centeredQuadratic A * centeredQuadratic B) =
      ∑ i, ∑ j, A i j * (B i j + B j i) := by
  rw [expectation_centeredQuadratic_mul_second]
  simp_rw [pderiv_centeredQuadratic]
  simp only [map_sum, Derivation.map_smul, pderiv_X, Pi.single_apply]
  simp [smul_ite, apply_ite expectation]

/-- For symmetric matrices this is exactly twice the Frobenius pairing. -/
theorem expectation_centeredQuadratic_covariance_symmetric
    (A B : Matrix ι ι ℝ) (hB : B.transpose = B) :
    expectation (centeredQuadratic A * centeredQuadratic B) =
      2 * ∑ i, ∑ j, A i j * B i j := by
  rw [expectation_centeredQuadratic_mul_centeredQuadratic]
  have hsym (i j : ι) : B j i = B i j := congrFun (congrFun hB i) j
  simp_rw [hsym]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

/-- Variance is bounded by twice the entrywise Frobenius square, even for
nonsymmetric coefficient matrices. -/
theorem expectation_centeredQuadratic_sq_le (A : Matrix ι ι ℝ) :
    expectation (centeredQuadratic A ^ 2) ≤ 2 * ∑ i, ∑ j, (A i j)^2 := by
  rw [pow_two, expectation_centeredQuadratic_mul_centeredQuadratic]
  have h (i j : ι) : A i j * (A i j + A j i) ≤
      (3 * (A i j)^2 + (A j i)^2) / 2 := by
    nlinarith [sq_nonneg (A i j - A j i)]
  calc
    _ ≤ ∑ i, ∑ j, (3 * (A i j)^2 + (A j i)^2) / 2 := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = _ := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm (f := fun i j => (A j i)^2)]
      ring

/-- Positivity of the genuine Gaussian polynomial square integral. -/
theorem expectation_sq_nonneg (P : MvPolynomial ι ℝ) : 0 ≤ expectation (P ^ 2) := by
  apply integral_nonneg
  intro x
  simp only [eval_pow]
  exact sq_nonneg _

/-- Cauchy–Schwarz for the actual Gaussian polynomial expectation. -/
theorem expectation_mul_sq_le (P Q : MvPolynomial ι ℝ) :
    (expectation (P*Q))^2 ≤ expectation (P^2) * expectation (Q^2) := by
  have h (t : ℝ) : 0 ≤ expectation (P^2) - 2*t*expectation (P*Q) +
      t^2*expectation (Q^2) := by
    have hh := expectation_sq_nonneg (P - t • Q)
    have he : (P-t • Q)^2 = P^2 - (2*t) • (P*Q) + t^2 • (Q^2) := by
      simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_pow, map_ofNat]
      ring
    rw [he, map_add, map_sub, map_smul, map_smul] at hh
    exact hh
  by_cases hq : expectation (Q^2) = 0
  · have hh := h ((expectation (P^2)+1)/(2*expectation (P*Q)))
    by_cases hpq : expectation (P*Q) = 0
    · simp [hpq, hq]
    · have he : expectation (P^2) - 2 * ((expectation (P^2)+1) /
          (2*expectation (P*Q))) * expectation (P*Q) +
          ((expectation (P^2)+1)/(2*expectation (P*Q)))^2 * expectation (Q^2) = -1 := by
        rw [hq]
        field_simp [hpq]
        <;> ring
      rw [he] at hh
      norm_num at hh
  · have hh := h (expectation (P*Q) / expectation (Q^2))
    have hqpos : 0 < expectation (Q^2) := lt_of_le_of_ne (expectation_sq_nonneg Q) (Ne.symm hq)
    have hmul := mul_nonneg hh (le_of_lt hqpos)
    have he : (expectation (P^2) - 2 * (expectation (P*Q) / expectation (Q^2)) *
          expectation (P*Q) + (expectation (P*Q) / expectation (Q^2))^2 *
          expectation (Q^2)) * expectation (Q^2) =
          expectation (P^2)*expectation (Q^2) - (expectation (P*Q))^2 := by
      field_simp [hq]
      <;> ring
    rw [he] at hmul
    linarith

#print axioms expectation_centeredQuadratic_mul
#print axioms expectation_centeredQuadratic_mul_second
end BMQuadraticStein
