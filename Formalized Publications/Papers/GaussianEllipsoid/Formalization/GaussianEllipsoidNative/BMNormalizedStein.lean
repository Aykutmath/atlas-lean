import BMQuadraticSteinBounds

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments MvPolynomial
open scoped BigOperators

namespace BMQuadraticStein
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem centeredQuadratic_smul (c : ℝ) (A : Matrix ι ι ℝ) :
    centeredQuadratic (c • A) = c • centeredQuadratic A := by
  simp only [centeredQuadratic, Matrix.smul_apply, smul_eq_mul, mul_smul,
    Finset.smul_sum]

/-- For symmetric input matrices the Stein-kernel coefficient is twice AB. -/
theorem kernelMatrix_symmetric_smul (c : ℝ) (A B : Matrix ι ι ℝ)
    (hA : A.transpose = A) (hB : B.transpose = B) :
    kernelMatrix (c • A) (c • B) = (2*c^2) • (A*B) := by
  have hA' (i j : ι) : A j i = A i j := congrFun (congrFun hA i) j
  have hB' (i j : ι) : B j i = B i j := congrFun (congrFun hB i) j
  ext i j
  simp only [kernelMatrix, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hA', hB']
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Q_A=(xᵀAx−tr A)/√d, the centered rank-one measurement of BM. -/
def normalizedQuadratic (d : ℕ) (A : Matrix ι ι ℝ) : MvPolynomial ι ℝ :=
  (Real.sqrt (d : ℝ))⁻¹ • centeredQuadratic A

/-- Substitute a finite family of the actual normalized quadratic measurements. -/
def normalizedSubstitution (d : ℕ) (A : κ → Matrix ι ι ℝ) :
    MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  aeval (fun a => normalizedQuadratic d (A a))

theorem normalizedSubstitution_eq_quadraticSubstitution
    (d : ℕ) (A : κ → Matrix ι ι ℝ) :
    normalizedSubstitution d A =
      quadraticSubstitution (fun a => (Real.sqrt (d : ℝ))⁻¹ • A a) := by
  simp only [normalizedSubstitution, quadraticSubstitution,
    centeredQuadratic_smul, normalizedQuadratic]

/-- Normalized vector Stein identity: the covariance is exactly 2 tr(AB)/d,
and the entire non-Gaussian error is an explicitly centered quadratic form. -/
theorem normalized_vector_stein
    (d : ℕ) (A : κ → Matrix ι ι ℝ) (hA : ∀ a, (A a).transpose = A a)
    (P : MvPolynomial κ ℝ) (a : κ) :
    expectation (normalizedQuadratic d (A a) * normalizedSubstitution d A P) =
      ∑ b, ((2 / (d : ℝ) * Matrix.trace (A a * A b)) *
          expectation (normalizedSubstitution d A (pderiv b P)) +
        expectation (normalizedKernelFluctuation d (A a) (A b) *
          normalizedSubstitution d A (pderiv b P))) := by
  have hs : 2 * ((Real.sqrt (d : ℝ))⁻¹)^2 = 2 / (d : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    rfl
  have h := expectation_quadraticSubstitution_covariance_remainder
    (fun a => (Real.sqrt (d : ℝ))⁻¹ • A a) P a
  simp only [kernelMatrix_symmetric_smul _ _ _ (hA _) (hA _), hs,
    Matrix.trace_smul, centeredQuadratic_smul, smul_eq_mul] at h
  simpa only [← normalizedSubstitution_eq_quadraticSubstitution,
    normalizedQuadratic, normalizedKernelFluctuation] using h

/-- The vector Stein discrepancy is bounded using only actual polynomial
L² derivative moments and genuine spectral norms. -/
theorem normalized_vector_stein_discrepancy_sq_le
    (d : ℕ) (hd : 0 < d) (A : κ → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a, (A a).transpose = A a) (P : MvPolynomial κ ℝ) (a : κ) :
    (expectation (normalizedQuadratic d (A a) * normalizedSubstitution d A P) -
      ∑ b, (2 / (d : ℝ) * Matrix.trace (A a * A b)) *
        expectation (normalizedSubstitution d A (pderiv b P)))^2 ≤
      (Fintype.card κ : ℝ) * ∑ b,
        (8 / (d : ℝ) * spectralNorm (A a)^2 * spectralNorm (A b)^2) *
          expectation ((normalizedSubstitution d A (pderiv b P))^2) := by
  rw [normalized_vector_stein d A hA P a, Finset.sum_add_distrib, add_sub_cancel_left]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ
    (fun _ : κ => (1 : ℝ))
    (fun b => expectation (normalizedKernelFluctuation d (A a) (A b) *
      normalizedSubstitution d A (pderiv b P)))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun b _ => normalizedKernelFluctuation_test_sq_le d hd
      (A a) (A b) (normalizedSubstitution d A (pderiv b P))) (by positivity))

/-- In particular, normalized quadratic measurements have exactly the Gaussian
covariance, not merely an asymptotically matching covariance. -/
theorem normalized_vector_covariance
    (d : ℕ) (A : κ → Matrix ι ι ℝ) (hA : ∀ a, (A a).transpose = A a)
    (a b : κ) :
    expectation (normalizedQuadratic d (A a) * normalizedQuadratic d (A b)) =
      2 / (d : ℝ) * Matrix.trace (A a * A b) := by
  have h := normalized_vector_stein d A hA (X b) a
  simpa [normalizedSubstitution, normalizedKernelFluctuation, Pi.single_apply,
    apply_ite (aeval (fun a => normalizedQuadratic d (A a))),
    apply_ite expectation, mul_ite, ite_mul] using h

/-- Uniform bounded-spectral-norm form of the finite-dimensional discrepancy.
L is a bound on the sum of the actual Gaussian L² derivative moments. -/
theorem normalized_vector_stein_discrepancy_sq_le_uniform
    (d : ℕ) (hd : 0 < d) (A : κ → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a, (A a).transpose = A a) (P : MvPolynomial κ ℝ) (a : κ)
    (K L : ℝ) (hK : 0 ≤ K) (hAnorm : ∀ b, spectralNorm (A b) ≤ K)
    (hP : (∑ b, expectation ((normalizedSubstitution d A (pderiv b P))^2)) ≤ L) :
    (expectation (normalizedQuadratic d (A a) * normalizedSubstitution d A P) -
      ∑ b, (2 / (d : ℝ) * Matrix.trace (A a * A b)) *
        expectation (normalizedSubstitution d A (pderiv b P)))^2 ≤
      8 * (Fintype.card κ : ℝ) * K^4 * L / d := by
  have hnorm (b : κ) : spectralNorm (A b)^2 ≤ K^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hAnorm b) 2
  calc
    _ ≤ (Fintype.card κ : ℝ) * ∑ b,
        (8 / (d : ℝ) * spectralNorm (A a)^2 * spectralNorm (A b)^2) *
          expectation ((normalizedSubstitution d A (pderiv b P))^2) :=
      normalized_vector_stein_discrepancy_sq_le d hd A hA P a
    _ ≤ (Fintype.card κ : ℝ) * ∑ b,
        (8 / (d : ℝ) * K^4) *
          expectation ((normalizedSubstitution d A (pderiv b P))^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro b hb
      apply mul_le_mul_of_nonneg_right _ (expectation_sq_nonneg _)
      calc
        _ ≤ 8 / (d : ℝ) * K^2 * K^2 := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hnorm a) (by positivity))
            (hnorm b) (sq_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (Fintype.card κ : ℝ) * (8 / (d : ℝ) * K^4) *
        ∑ b, expectation ((normalizedSubstitution d A (pderiv b P))^2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card κ : ℝ) * (8 / (d : ℝ) * K^4) * L :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    _ = _ := by ring

#print axioms normalized_vector_stein
#print axioms normalized_vector_stein_discrepancy_sq_le
end BMQuadraticStein
