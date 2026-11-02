import AHHComplexCovarianceBounds
import FrobeniusCovarianceSynthesis

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open GaussianTensorTrace GaussianEllipsoid
namespace AHHAlgebraBridges

/-- The newly stated real covariance is literally the previously checked
row-vectorized tensor covariance; both use the Euclidean operator norm. -/
theorem realCov_norm_eq_matrixCLM (n h : ℕ) (a b : Fin n → Fin h → ℝ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a b)‖ =
      ‖matrixCLM (realCov n h a b)‖ := rfl

/-- Row-vectorization is exactly the Frobenius linear isometry in the actual
bilinear synthesis, with the literal d⁻¹/² scale. -/
theorem bilinear_frobenius_covariance_identity (n h : ℕ)
    (a b : Fin n → Fin h → ℝ) (d : ℝ) (hd : 0 ≤ d) :
    ‖tensorFrobeniusSynthesis a b d‖ ^ 2 =
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a b)‖ / d := by
  exact tensorFrobeniusSynthesis_norm_sq a b d hd

/-- Manuscript display 2759, first inequality, for the literal real
Euclidean-to-Frobenius operator and four complex Euclidean covariance norms. -/
theorem pathwise_real_bilinear_to_complex (n h : ℕ) (hh : 0 < h)
    (d : ℝ) (hd : 0 < d) (a a' b b' : Fin n → Fin h → ℝ) :
    ‖tensorFrobeniusSynthesis a b d‖ ^ 2 ≤
      (h : ℝ) ^ 2 / d * ∑ s : Bool, ∑ t : Bool,
        ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ := by
  rw [bilinear_frobenius_covariance_identity n h a b d (le_of_lt hd)]
  have hb := div_le_div_of_nonneg_right
    (realCov_norm_le_four_complexCov_norm n h hh a a' b b') (le_of_lt hd)
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb

/-- The four-event common bound has exact constant 4C₀; no sign-ensemble
independence is assumed in this pathwise statement. -/
theorem pathwise_four_sign_bound (n h : ℕ) (hh : 0 < h)
    (d : ℝ) (hd : 0 < d) (a a' b b' : Fin n → Fin h → ℝ)
    (C₀ : ℝ) (hC : ∀ s t : Bool, ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ ≤ C₀) :
    ‖tensorFrobeniusSynthesis a b d‖ ^ 2 ≤ (4 * C₀) * (h : ℝ) ^ 2 / d := by
  have hs : (∑ s : Bool, ∑ t : Bool,
      ‖cMatrixCLM (complexCov n h a a' b b' s t)‖) ≤ 4 * C₀ := by
    calc
      _ ≤ ∑ _s : Bool, ∑ _t : Bool, C₀ :=
        Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => hC s t))
      _ = _ := by simp; ring
  have hb := (pathwise_real_bilinear_to_complex n h hh d hd a a' b b').trans
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (h : ℝ) ^ 2 / d))
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hb

/-- Explicit bridge for the paper's renaming of constants: C = 4C₀. -/
theorem pathwise_four_sign_renamed_constant (n h : ℕ) (hh : 0 < h)
    (d : ℝ) (hd : 0 < d) (a a' b b' : Fin n → Fin h → ℝ)
    (C₀ C : ℝ) (hrename : C = 4 * C₀)
    (hC : ∀ s t : Bool, ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ ≤ C₀) :
    ‖tensorFrobeniusSynthesis a b d‖ ^ 2 ≤ C * (h : ℝ) ^ 2 / d := by
  subst C
  exact pathwise_four_sign_bound n h hh d hd a a' b b' C₀ hC

/-- If h≤d, the literal four-sign bound is at most (4C₀)d. -/
theorem pathwise_dimension_bound (n h d : ℕ) (hh : 0 < h) (hd : 0 < d) (hhd : h ≤ d)
    (a a' b b' : Fin n → Fin h → ℝ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hC : ∀ s t : Bool, ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ ≤ C₀) :
    ‖tensorFrobeniusSynthesis a b (d : ℝ)‖ ^ 2 ≤ (4 * C₀) * d := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hhdR : (h : ℝ) ≤ d := Nat.cast_le.mpr hhd
  have hs : (h : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg h) hhdR 2
  calc
    _ ≤ (4 * C₀) * (h : ℝ) ^ 2 / d :=
      pathwise_four_sign_bound n h hh (d : ℝ) hdR a a' b b' C₀ hC
    _ ≤ (4 * C₀) * (d : ℝ) ^ 2 / d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by positivity)) (le_of_lt hdR)
    _ = _ := by field_simp

/-- The square-root constant is explicit as 2√C₀. -/
theorem pathwise_sqrt_dimension_bound (n h d : ℕ) (hh : 0 < h) (hd : 0 < d) (hhd : h ≤ d)
    (a a' b b' : Fin n → Fin h → ℝ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hC : ∀ s t : Bool, ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ ≤ C₀) :
    ‖tensorFrobeniusSynthesis a b (d : ℝ)‖ ≤ 2 * Real.sqrt C₀ * Real.sqrt d := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have heq : (2 * Real.sqrt C₀ * Real.sqrt (d : ℝ)) ^ 2 = (4 * C₀) * d := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC₀, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  rw [heq]
  exact pathwise_dimension_bound n h d hh hd hhd a a' b b' C₀ hC₀ hC

/-- At h=0 the codomain is the zero Frobenius space, so the operator is zero. -/
theorem bilinear_zero_local_dimension (n : ℕ) (d : ℝ)
    (a b : Fin n → Fin 0 → ℝ) : tensorFrobeniusSynthesis a b d = 0 := by
  ext y i j
  exact Fin.elim0 i

/-- At d=0 Lean's exact sqrt normalization is zero, explicitly separated from
all positive-dimension division arguments. -/
theorem bilinear_zero_scale (n h : ℕ) (a b : Fin n → Fin h → ℝ) :
    tensorFrobeniusSynthesis a b 0 = 0 := by
  ext y i j
  simp [tensorFrobeniusSynthesis, scaledSynthesisCLM]

/-- The floor(d/2) endpoints d=0,1 have zero local dimension. -/
theorem paper_small_dimension_operator_zero (n d : ℕ) (hd : d < 2)
    (a b : Fin n → Fin (d / 2) → ℝ) : tensorFrobeniusSynthesis a b (d : ℝ) = 0 := by
  have hz : d / 2 = 0 := Nat.div_eq_of_lt hd
  ext y i j
  have hi := i.isLt
  omega

/-- The paper's h=floor(d/2) convention, with d=0 and d=1 explicitly handled. -/
theorem paper_half_dimension_bound_all_d (n d : ℕ)
    (a a' b b' : Fin n → Fin (d / 2) → ℝ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hC : ∀ s t : Bool, ‖cMatrixCLM (complexCov n (d / 2) a a' b b' s t)‖ ≤ C₀) :
    ‖tensorFrobeniusSynthesis a b (d : ℝ)‖ ≤ 2 * Real.sqrt C₀ * Real.sqrt d := by
  by_cases hd : 2 ≤ d
  · exact pathwise_sqrt_dimension_bound n (d / 2) d (by omega) (by omega)
      (Nat.div_le_self d 2) a a' b b' C₀ hC₀ hC
  · rw [paper_small_dimension_operator_zero n d (by omega) a b, norm_zero]
    positivity

/-- Precisely the eventual hypotheses used when h=floor(d/2). -/
theorem paper_half_dimension_eventually_positive :
    ∀ᶠ d : ℕ in Filter.atTop, 0 < d ∧ 0 < d / 2 ∧ d / 2 ≤ d := by
  filter_upwards [Filter.eventually_ge_atTop 2] with d hd
  exact ⟨by omega, by omega, Nat.div_le_self d 2⟩

end AHHAlgebraBridges
