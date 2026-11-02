import BMSmoothSteinBounds

/-! Dimension-free Stein discrepancy for diffuse matrix families. Retaining
Frobenius energy instead of replacing it by dimension times spectral norm is
crucial for the conic comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMSmoothSteinBounds MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCFrobeniusStein
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Multiplication by an operator controls each Euclidean column separately. -/
theorem frobeniusSq_mul_le_spectral_frobenius (A B : Matrix ι ι ℝ) :
    frobeniusSq (A*B) ≤ spectralNorm A^2 * frobeniusSq B := by
  have hcol (j : ι) : (∑ i, ((A*B) i j)^2) ≤
      spectralNorm A^2 * ∑ i, (B i j)^2 := by
    let v : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => B i j)
    have h := ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A).le_opNorm v
    have he : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A v =
        WithLp.toLp 2 (fun i => (A*B) i j) := by
      change (((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A :
        EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι) v) = _
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toLpLin_apply]
      ext i
      rfl
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [he, mul_pow] at hsq
    simpa [spectralNorm, v, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hsq
  unfold frobeniusSq
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : ι, spectralNorm A^2 * ∑ i, (B i j)^2 :=
      Finset.sum_le_sum fun j _ => hcol j
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

/-- The native quadratic Stein remainder with its sharp Frobenius energy. -/
theorem kernel_bounded_test_sq_le_frobenius
    (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℝ)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    (boundedExpectation f (normalizedKernelFluctuation d A B))^2 ≤
      (8 / (d : ℝ)^2 * frobeniusSq (A*B)) * ‖f‖^2 :=
  (boundedExpectation_sq_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (normalizedKernelFluctuation_second_moment_le_frobenius d A B) (sq_nonneg _))

/-- Any deterministic product-energy bound gives an absolute, actual-law
Stein error without a dimension or state-count loss. -/
theorem kernel_bounded_test_abs_le
    (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℝ)
    {R : ℝ} (hR : 0 ≤ R)
    (hAB : 8 / (d : ℝ)^2 * frobeniusSq (A*B) ≤ R^2)
    (f : (Fin d → ℝ) →ᵇ ℝ) :
    |boundedExpectation f (normalizedKernelFluctuation d A B)| ≤ R*‖f‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hR (norm_nonneg _))).mp
  rw [sq_abs, mul_pow]
  exact (kernel_bounded_test_sq_le_frobenius d A B f).trans
    (mul_le_mul_of_nonneg_right hAB (sq_nonneg _))

/-- UC normalization: when ‖A‖op²≤dτ²/2 and ‖B‖F²≤d/2, the
quadratic Stein discrepancy is at most √2 τ, uniformly in dimension. -/
theorem diffuse_product_energy (d : ℕ) (hd : 0 < d)
    (A B : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ)
    (hA : spectralNorm A^2 ≤ (d:ℝ)/2*τ^2)
    (hB : frobeniusSq B ≤ (d:ℝ)/2) :
    8/(d:ℝ)^2 * frobeniusSq (A*B) ≤ (Real.sqrt 2*τ)^2 := by
  have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  calc
    _ ≤ 8/(d:ℝ)^2 * (spectralNorm A^2 * frobeniusSq B) :=
      mul_le_mul_of_nonneg_left (frobeniusSq_mul_le_spectral_frobenius A B) (by positivity)
    _ ≤ 8/(d:ℝ)^2 * (((d:ℝ)/2*τ^2) * ((d:ℝ)/2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hA hB (frobeniusSq_nonneg B) (by positivity)) (by positivity)
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; field_simp; ring

#print axioms frobeniusSq_mul_le_spectral_frobenius
#print axioms kernel_bounded_test_abs_le
#print axioms diffuse_product_energy
end GaussianEllipsoid.UCFrobeniusStein
