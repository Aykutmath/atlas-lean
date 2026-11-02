import BMQuadraticStein

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments MvPolynomial
open scoped BigOperators

namespace BMQuadraticStein
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A finite-dimensional algebraic chain rule for polynomial substitution. -/
theorem pderiv_aeval (q : κ → MvPolynomial ι ℝ) (P : MvPolynomial κ ℝ) (i : ι) :
    pderiv i (aeval q P) =
      ∑ a, aeval q (pderiv a P) * pderiv i (q a) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P a hP =>
    simp only [map_mul, aeval_X, pderiv_mul, hP, map_add]
    simp only [pderiv_X, Pi.single_apply, apply_ite (aeval q), map_one, map_zero]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    ring

/-- Substitution of a finite family of centered quadratic forms. -/
def quadraticSubstitution (A : κ → Matrix ι ι ℝ) :
    MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  aeval (fun a => centeredQuadratic (A a))

/-- Exact finite-dimensional Stein identity before collecting matrix products.
All coordinates may be strongly dependent; their common Gaussian input is
retained throughout. -/
theorem expectation_quadraticSubstitution_stein
    (A : κ → Matrix ι ι ℝ) (P : MvPolynomial κ ℝ) (a : κ) :
    expectation (centeredQuadratic (A a) * quadraticSubstitution A P) =
      ∑ i, ∑ j, A a i j * expectation
        (X j * ∑ b, quadraticSubstitution A (pderiv b P) *
          (∑ k, (A b i k + A b k i) • X k)) := by
  rw [expectation_centeredQuadratic_mul]
  unfold quadraticSubstitution
  simp_rw [pderiv_aeval, pderiv_centeredQuadratic]

/-- Move the last index of a finite triple sum to the front. -/
theorem sum_three_rotate {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid M] (f : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The uncentered second-chaos polynomial. -/
def rawQuadratic (A : Matrix ι ι ℝ) : MvPolynomial ι ℝ :=
  ∑ i, ∑ j, A i j • (X i * X j)

/-- Removing the trace produces exactly the centered quadratic form. -/
theorem rawQuadratic_eq_centered_add_trace (A : Matrix ι ι ℝ) :
    rawQuadratic A = centeredQuadratic A + C (Matrix.trace A) := by
  simp only [rawQuadratic, centeredQuadratic, smul_sub, Finset.sum_sub_distrib]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [MvPolynomial.smul_eq_C_mul, mul_one, Matrix.trace, Matrix.diag, map_sum]
  ring

/-- Matrix of the Gaussian quadratic Stein kernel. -/
def kernelMatrix (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A.transpose * (B+B.transpose)

/-- Algebraic gradient contraction is the exact quadratic Stein kernel. -/
theorem rawQuadratic_kernelMatrix (A B : Matrix ι ι ℝ) :
    rawQuadratic (kernelMatrix A B) =
      ∑ i, ∑ j, A i j • (X j * pderiv i (centeredQuadratic B)) := by
  simp only [rawQuadratic, kernelMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.add_apply, pderiv_centeredQuadratic, Finset.mul_sum, Finset.smul_sum,
    Finset.sum_smul, mul_smul_comm, smul_smul]
  exact sum_three_rotate (fun j k i =>
    (A i j * (B i k + B k i)) • (X j * X k))

/-- The exact vector Stein identity in covariance-plus-centered-remainder form. -/
theorem expectation_quadraticSubstitution_covariance_remainder
    (A : κ → Matrix ι ι ℝ) (P : MvPolynomial κ ℝ) (a : κ) :
    expectation (centeredQuadratic (A a) * quadraticSubstitution A P) =
      ∑ b, (Matrix.trace (kernelMatrix (A a) (A b)) *
          expectation (quadraticSubstitution A (pderiv b P)) +
        expectation (centeredQuadratic (kernelMatrix (A a) (A b)) *
          quadraticSubstitution A (pderiv b P))) := by
  have hraw : expectation (centeredQuadratic (A a) * quadraticSubstitution A P) =
      ∑ b, expectation (rawQuadratic (kernelMatrix (A a) (A b)) *
        quadraticSubstitution A (pderiv b P)) := by
    rw [expectation_centeredQuadratic_mul]
    unfold quadraticSubstitution
    simp_rw [pderiv_aeval, Finset.mul_sum, map_sum, Finset.mul_sum,
      rawQuadratic_kernelMatrix, Finset.sum_mul, smul_mul_assoc, map_sum,
      map_smul, smul_eq_mul]
    rw [sum_three_rotate]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    congr 1
    ring
  rw [hraw]
  apply Finset.sum_congr rfl
  intro b hb
  rw [rawQuadratic_eq_centered_add_trace, add_mul, map_add, C_mul', map_smul]
  simp only [smul_eq_mul]
  ring

#print axioms expectation_quadraticSubstitution_covariance_remainder
end BMQuadraticStein
