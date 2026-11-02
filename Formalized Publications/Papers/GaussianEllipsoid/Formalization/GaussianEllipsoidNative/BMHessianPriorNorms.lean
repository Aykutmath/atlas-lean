import BMBoundedHessian

open BMFiniteGibbsTest
open scoped BoundedContinuousFunction
namespace BMFiniteGibbsHessian
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def diagonalPriorConstant (D : Data2 κ) : ℝ :=
  Real.exp (2*D.beta*‖D.potential‖)*(D.beta^2*‖D.potentialDeriv‖^2+D.beta*‖D.potentialSecond‖)
noncomputable def pairPriorConstant (D : Data2 κ) : ℝ :=
  D.beta^2*Real.exp (4*D.beta*‖D.potential‖)*‖D.potentialDeriv‖^2

theorem diagonalPriorConstant_nonneg (D : Data2 κ) : 0 ≤ diagonalPriorConstant D := by
  have hb := D.beta_nonneg
  unfold diagonalPriorConstant
  positivity

theorem pairPriorConstant_nonneg (D : Data2 κ) : 0 ≤ pairPriorConstant D := by
  unfold pairPriorConstant
  positivity

theorem boundedDiagonal_norm_le_prior (D : Data2 κ) (a : κ) :
    ‖boundedDiagonal D a‖ ≤ diagonalPriorConstant D * D.weight a := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (diagonalPriorConstant_nonneg D) (D.weight_nonneg a))).2
  intro y
  have hb := D.beta_nonneg
  have hw := D.weight_nonneg a
  have hq := probability_nonneg D.toData y a
  have hqbound := probability_le_prior D.toData y a
  have h1 := D.potentialDeriv.norm_coe_le_norm (y a)
  have h2 := D.potentialSecond.norm_coe_le_norm (y a)
  have hinside : ‖D.beta^2*(D.potentialDeriv (y a))^2-D.beta*D.potentialSecond (y a)‖ ≤
      D.beta^2*‖D.potentialDeriv‖^2+D.beta*‖D.potentialSecond‖ := by
    calc
      _ ≤ ‖D.beta^2*(D.potentialDeriv (y a))^2‖ + ‖D.beta*D.potentialSecond (y a)‖ := norm_sub_le _ _
      _ = D.beta^2*‖D.potentialDeriv (y a)‖^2 + D.beta*‖D.potentialSecond (y a)‖ := by
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hb, sq_abs]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h1 2) (sq_nonneg _))
        (mul_le_mul_of_nonneg_left h2 hb)
  rw [boundedDiagonal_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg hq]
  have hp := mul_le_mul hqbound hinside (norm_nonneg _)
    (mul_nonneg (Real.exp_nonneg _) hw)
  convert! hp using 1 <;> simp only [diagonalPriorConstant, Data2.toData] <;> ring

theorem boundedPair_norm_le_prior (D : Data2 κ) (a b : κ) :
    ‖boundedPair D a b‖ ≤ pairPriorConstant D * (D.weight a*D.weight b) := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (pairPriorConstant_nonneg D) (mul_nonneg (D.weight_nonneg a) (D.weight_nonneg b)))).2
  intro y
  have hp := probability_pair_le_prior D.toData y a b
  have hqa := probability_nonneg D.toData y a
  have hqb := probability_nonneg D.toData y b
  have h1 := D.potentialDeriv.norm_coe_le_norm (y a)
  have h2 := D.potentialDeriv.norm_coe_le_norm (y b)
  have hprod := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  have hh := mul_le_mul hp hprod
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (D.weight_nonneg a) (D.weight_nonneg b)))
  have h := mul_le_mul_of_nonneg_left hh (sq_nonneg D.beta)
  rw [boundedPair_apply]
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs,
    abs_of_nonneg hqa, abs_of_nonneg hqb]
  convert! h using 1 <;> simp only [pairPriorConstant, pow_two, Real.norm_eq_abs] <;> ring

theorem boundedHessian_norm_le_prior (D : Data2 κ) (a b : κ) :
    ‖boundedHessian D a b‖ ≤
      (if a=b then diagonalPriorConstant D*D.weight a else 0) +
        pairPriorConstant D*(D.weight a*D.weight b) := by
  unfold boundedHessian
  apply (norm_sub_le _ _).trans
  by_cases hab : a=b
  · simp only [if_pos hab]
    exact add_le_add (boundedDiagonal_norm_le_prior D a) (boundedPair_norm_le_prior D a b)
  · simp only [if_neg hab, norm_zero, zero_add]
    exact boundedPair_norm_le_prior D a b

/-- The Hessian's total coordinate norm is independent of the number of
states. This is the exact dimension-free interpolation input. -/
theorem sum_boundedHessian_norm_le (D : Data2 κ) :
    (∑ a, ∑ b, ‖boundedHessian D a b‖) ≤ diagonalPriorConstant D + pairPriorConstant D := by
  calc
    _ ≤ ∑ a, ∑ b, ((if a=b then diagonalPriorConstant D*D.weight a else 0) +
        pairPriorConstant D*(D.weight a*D.weight b)) :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => boundedHessian_norm_le_prior D a b))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, D.weight_sum, mul_one]

#print axioms boundedDiagonal_norm_le_prior
#print axioms boundedPair_norm_le_prior
#print axioms boundedHessian_norm_le_prior
#print axioms sum_boundedHessian_norm_le
end BMFiniteGibbsHessian
