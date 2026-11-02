import BMGordonSoftMinMaxDeriv

noncomputable section
open scoped BigOperators

namespace BMGordonSoftMinMax
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

/-- Entries of the genuine Hessian of the nested soft minmax. -/
def hessian (β : ℝ) (x : I × J → ℝ) (a b : I × J) : ℝ :=
  β * gradient β x a *
    ((if a = b then 1 else 0) -
      2 * (if a.1 = b.1 then innerWeight β x b else 0) + gradient β x b)

lemma rowLinear_eq_sum (β : ℝ) (x : I × J → ℝ) (i : I) :
    rowLinear β x i = ∑ b : I × J,
      (if i = b.1 then innerWeight β x b else 0) • ContinuousLinearMap.proj b := by
  simp only [Fintype.sum_prod_type, ite_smul, zero_smul, rowLinear]
  rw [Finset.sum_comm]
  simp

lemma hessianLinear_eq (β : ℝ) (x : I × J → ℝ) (a : I × J) :
    (∑ b, hessian β x a b • ContinuousLinearMap.proj b) =
      (β * gradient β x a) •
        (ContinuousLinearMap.proj a - (2 : ℝ) • rowLinear β x a.1 + gradientLinear β x) := by
  rw [rowLinear_eq_sum]
  simp only [hessian, mul_smul, sub_smul, add_smul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.smul_sum, gradientLinear, ite_smul, zero_smul,
    one_smul]
  simp

/-- The actual gradient has the explicit bounded Hessian as its derivative. -/
theorem hasFDerivAt_gradient_hessian (β : ℝ) (x : I × J → ℝ) (a : I × J) :
    HasFDerivAt (fun y => gradient β y a)
      (∑ b, hessian β x a b • (ContinuousLinearMap.proj b : (I × J → ℝ) →L[ℝ] ℝ)) x := by
  rw [hessianLinear_eq]
  exact hasFDerivAt_gradient β x a

/-- Different rows have a nonnegative Hessian interaction. -/
theorem hessian_of_row_ne (β : ℝ) (x : I × J → ℝ) (a b : I × J)
    (hab : a.1 ≠ b.1) :
    hessian β x a b = β * gradient β x a * gradient β x b := by
  have hne : a ≠ b := fun h => hab (congrArg Prod.fst h)
  simp [hessian, hne, hab]

theorem hessian_nonneg_of_row_ne (β : ℝ) (hβ : 0 ≤ β) (x : I × J → ℝ)
    (a b : I × J) (hab : a.1 ≠ b.1) : 0 ≤ hessian β x a b := by
  rw [hessian_of_row_ne β x a b hab]
  exact mul_nonneg (mul_nonneg hβ (gradient_pos β x a).le) (gradient_pos β x b).le

/-- Distinct coordinates within a row have the negative soft-maximum interaction. -/
theorem hessian_of_same_row_ne (β : ℝ) (x : I × J → ℝ) (a b : I × J)
    (hrow : a.1 = b.1) (hab : a ≠ b) :
    hessian β x a b = β * outerWeight β x a.1 * innerWeight β x a *
      innerWeight β x b * (outerWeight β x a.1 - 2) := by
  simp only [hessian, if_neg hab, if_pos hrow, gradient]
  rw [← hrow]
  ring

theorem hessian_nonpos_of_same_row_ne (β : ℝ) (hβ : 0 ≤ β) (x : I × J → ℝ)
    (a b : I × J) (hrow : a.1 = b.1) (hab : a ≠ b) : hessian β x a b ≤ 0 := by
  rw [hessian_of_same_row_ne β x a b hrow hab]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg (mul_nonneg (mul_nonneg hβ (outerWeight_pos β x a.1).le)
      (innerWeight_pos β x a).le) (innerWeight_pos β x b).le
  · linarith [outerWeight_le_one β x a.1]

/-- A dimension-free global Hessian bound, sufficient for Gaussian integration. -/
theorem abs_hessian_le (β : ℝ) (x : I × J → ℝ) (a b : I × J) :
    |hessian β x a b| ≤ 4 * |β| := by
  have hg : |gradient β x a| ≤ 1 := by
    rw [abs_of_pos (gradient_pos β x a)]
    exact gradient_le_one β x a
  have hg' : |gradient β x b| ≤ 1 := by
    rw [abs_of_pos (gradient_pos β x b)]
    exact gradient_le_one β x b
  have hq : |(if a.1 = b.1 then innerWeight β x b else 0)| ≤ 1 := by
    split_ifs
    · rw [abs_of_pos (innerWeight_pos β x b)]
      exact innerWeight_le_one β x b
    · norm_num
  have hd : |(if a = b then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  have hc : |(if a = b then (1 : ℝ) else 0) -
      2 * (if a.1 = b.1 then innerWeight β x b else 0) + gradient β x b| ≤ 4 := by
    calc
      _ ≤ |(if a = b then (1 : ℝ) else 0) -
        2 * (if a.1 = b.1 then innerWeight β x b else 0)| + |gradient β x b| :=
          abs_add_le _ _
      _ ≤ (|(if a = b then (1 : ℝ) else 0)| +
        |2 * (if a.1 = b.1 then innerWeight β x b else 0)|) + |gradient β x b| :=
          add_le_add_left (abs_sub _ _) _
      _ ≤ 4 := by rw [abs_mul]; norm_num; linarith
  simp only [hessian, abs_mul]
  calc
    _ ≤ (|β| * 1) * 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg (abs_nonneg β)) hc (abs_nonneg _)
        (mul_nonneg (abs_nonneg β) zero_le_one)
    _ = _ := by ring

end BMGordonSoftMinMax
