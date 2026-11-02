import UCFrobeniusStein

/-! New reconstruction: dimension-free ordered-triple quadratic bounds.
No matrix in the triple is assumed symmetric. -/
noncomputable section
open BMQuadraticStein BMSmoothQuadraticComposition BMSmoothSteinBounds MvPolynomial
open GaussianEllipsoid.UCFrobeniusStein
open scoped BigOperators BoundedContinuousFunction
namespace PaperThirdQuadraticBound
variable {d : ℕ}

abbrev quadratic (A : Matrix (Fin d) (Fin d) ℝ) := rawQuadratic A

theorem eval_quadratic (A : Matrix (Fin d) (Fin d) ℝ) (w : Fin d → ℝ) :
    eval w (quadratic A) = ∑ i, ∑ j, A i j * (w i * w j) := by
  simp [quadratic, rawQuadratic, MvPolynomial.smul_eq_C_mul]

theorem quadratic_second_moment (A : Matrix (Fin d) (Fin d) ℝ) :
    expectation ((quadratic A)^2) =
      expectation ((centeredQuadratic A)^2) + (Matrix.trace A)^2 := by
  change expectation ((rawQuadratic A)^2) = _
  rw [rawQuadratic_eq_centered_add_trace]
  have he : (centeredQuadratic A + C (Matrix.trace A))^2 =
      (centeredQuadratic A)^2 + (2*Matrix.trace A) • centeredQuadratic A +
      C ((Matrix.trace A)^2) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, map_ofNat, map_pow]
    ring
  rw [he, map_add, map_add, map_smul, expectation_centeredQuadratic,
    expectation_C, smul_zero, add_zero]

theorem trace_mul_sq_le (A B : Matrix (Fin d) (Fin d) ℝ) :
    (Matrix.trace (A*B))^2 ≤ frobeniusSq A * frobeniusSq B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
    (fun p => A p.1 p.2) (fun p => B p.2 p.1)
  simp only [Fintype.sum_prod_type] at h
  rw [Finset.sum_comm (f := fun i j => (B j i)^2)] at h
  simpa only [Matrix.trace, Matrix.diag, Matrix.mul_apply, frobeniusSq] using h

theorem triple_bounds (A B C : Matrix (Fin d) (Fin d) ℝ)
    {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA : spectralNorm A ≤ τ) (hB : spectralNorm B ≤ τ)
    (hFA : frobeniusSq A ≤ 1) (hFC : frobeniusSq C ≤ 1) :
    (Matrix.trace (A*B*C))^2 ≤ τ^2 ∧ frobeniusSq (A*B*C) ≤ τ^2 := by
  have ha := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hb := pow_le_pow_left₀ (norm_nonneg _) hB 2
  have hBC : frobeniusSq (B*C) ≤ τ^2 := calc
    _ ≤ spectralNorm B^2 * frobeniusSq C := frobeniusSq_mul_le_spectral_frobenius B C
    _ ≤ τ^2 * 1 := mul_le_mul hb hFC (frobeniusSq_nonneg _) (sq_nonneg _)
    _ = _ := mul_one _
  rw [Matrix.mul_assoc]
  constructor
  · exact (trace_mul_sq_le A (B*C)).trans (by
      have h := mul_le_mul hFA hBC (frobeniusSq_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      simpa using h)
  · calc
      _ ≤ spectralNorm A^2 * frobeniusSq (B*C) := frobeniusSq_mul_le_spectral_frobenius A (B*C)
      _ ≤ τ^2 * τ^2 := mul_le_mul ha hBC (frobeniusSq_nonneg _) (sq_nonneg _)
      _ ≤ τ^2 := by nlinarith [sq_nonneg τ, mul_nonneg hτ (sub_nonneg.mpr hτ1)]

theorem bounded_triple_test_le (A B C : Matrix (Fin d) (Fin d) ℝ)
    (f : (Fin d → ℝ) →ᵇ ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA : spectralNorm A ≤ τ) (hB : spectralNorm B ≤ τ)
    (hFA : frobeniusSq A ≤ 1) (hFC : frobeniusSq C ≤ 1) :
    |boundedExpectation f (quadratic (A*B*C))| ≤ Real.sqrt 3 * τ * ‖f‖ := by
  have ht := triple_bounds A B C hτ hτ1 hA hB hFA hFC
  have hv := expectation_centeredQuadratic_sq_le (A*B*C)
  change expectation ((centeredQuadratic (A*B*C))^2) ≤ 2*frobeniusSq (A*B*C) at hv
  have hm : expectation ((quadratic (A*B*C))^2) ≤ 3*τ^2 := by
    rw [quadratic_second_moment]
    linarith [ht.1, ht.2]
  have hh := (boundedExpectation_sq_le (quadratic (A*B*C)) f).trans
    (mul_le_mul_of_nonneg_right hm (sq_nonneg _))
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), mul_assoc] using hh

#print axioms triple_bounds
#print axioms bounded_triple_test_le
end PaperThirdQuadraticBound
