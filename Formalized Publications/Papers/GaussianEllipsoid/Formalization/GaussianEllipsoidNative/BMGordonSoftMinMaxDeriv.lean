import BMGordonSoftMinMax

noncomputable section
open scoped BigOperators

namespace BMGordonSoftMinMax
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- Conditional mean of coordinate increments in a Gibbs row. -/
def rowLinear (β : ℝ) (x : I × J → ℝ) (i : I) : (I × J → ℝ) →L[ℝ] ℝ :=
  ∑ j, innerWeight β x (i,j) • ContinuousLinearMap.proj (i,j)

/-- The gradient as a continuous linear form. -/
def gradientLinear (β : ℝ) (x : I × J → ℝ) : (I × J → ℝ) →L[ℝ] ℝ :=
  ∑ a, gradient β x a • ContinuousLinearMap.proj a

lemma gradientLinear_eq (β : ℝ) (x : I × J → ℝ) :
    gradientLinear β x = ∑ i, outerWeight β x i • rowLinear β x i := by
  simp only [gradientLinear, Fintype.sum_prod_type, rowLinear, Finset.smul_sum,
    smul_smul, gradient]

lemma hasFDerivAt_rowSum (β : ℝ) (x : I × J → ℝ) (i : I) :
    HasFDerivAt (fun y => rowSum β y i)
      ((β * rowSum β x i) • rowLinear β x i) x := by
  have hd := HasFDerivAt.sum (u := (Finset.univ : Finset J))
    (fun j _ => (((ContinuousLinearMap.proj (i,j) :
      (I × J → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul β).exp)
  convert! hd using 1
  · ext y
    simp [rowSum]
  ext h
  simp only [rowLinear, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.mul_sum, innerWeight]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [ne_of_gt (rowSum_pos β x i)] <;> ring

lemma hasFDerivAt_inv_rowSum (β : ℝ) (x : I × J → ℝ) (i : I) :
    HasFDerivAt (fun y => (rowSum β y i)⁻¹)
      ((-β * (rowSum β x i)⁻¹) • rowLinear β x i) x := by
  have hd := (hasDerivAt_inv (ne_of_gt (rowSum_pos β x i))).comp_hasFDerivAt x
    (hasFDerivAt_rowSum β x i)
  convert! hd using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt (rowSum_pos β x i)] <;> ring

lemma hasFDerivAt_outerSum (β : ℝ) (x : I × J → ℝ) :
    HasFDerivAt (outerSum β)
      ((-β * outerSum β x) • gradientLinear β x) x := by
  have hd := HasFDerivAt.sum (u := (Finset.univ : Finset I))
    (fun i _ => hasFDerivAt_inv_rowSum β x i)
  convert! hd using 1
  · ext y
    simp [outerSum]
  ext h
  rw [gradientLinear_eq]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum, outerWeight]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (outerSum_pos β x), ne_of_gt (rowSum_pos β x i)] <;> ring

/-- The actual nested soft minmax has the Gibbs-product gradient. -/
theorem hasFDerivAt_softMinMax (β : ℝ) (hβ : β ≠ 0) (x : I × J → ℝ) :
    HasFDerivAt (softMinMax β) (gradientLinear β x) x := by
  have hd := (((hasFDerivAt_outerSum β x).log
    (ne_of_gt (outerSum_pos β x))).neg).mul_const β⁻¹
  convert! hd using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  field_simp [hβ, ne_of_gt (outerSum_pos β x)] <;> ring

lemma hasFDerivAt_innerWeight (β : ℝ) (x : I × J → ℝ) (a : I × J) :
    HasFDerivAt (fun y => innerWeight β y a)
      ((β * innerWeight β x a) • (ContinuousLinearMap.proj a - rowLinear β x a.1)) x := by
  have he := (((ContinuousLinearMap.proj a :
    (I × J → ℝ) →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul β).exp
  have hd := he.mul (hasFDerivAt_inv_rowSum β x a.1)
  convert! hd using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    innerWeight, div_eq_mul_inv]
  ring

lemma hasFDerivAt_inv_outerSum (β : ℝ) (x : I × J → ℝ) :
    HasFDerivAt (fun y => (outerSum β y)⁻¹)
      ((β * (outerSum β x)⁻¹) • gradientLinear β x) x := by
  have hd := (hasDerivAt_inv (ne_of_gt (outerSum_pos β x))).comp_hasFDerivAt x
    (hasFDerivAt_outerSum β x)
  convert! hd using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt (outerSum_pos β x)] <;> ring

lemma hasFDerivAt_outerWeight (β : ℝ) (x : I × J → ℝ) (i : I) :
    HasFDerivAt (fun y => outerWeight β y i)
      ((β * outerWeight β x i) • (gradientLinear β x - rowLinear β x i)) x := by
  have hd := (hasFDerivAt_inv_rowSum β x i).mul (hasFDerivAt_inv_outerSum β x)
  convert! hd using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul, outerWeight, div_eq_mul_inv]
  ring

/-- Exact second derivative of the nested soft minmax, in linear-form form. -/
theorem hasFDerivAt_gradient (β : ℝ) (x : I × J → ℝ) (a : I × J) :
    HasFDerivAt (fun y => gradient β y a)
      ((β * gradient β x a) •
        (ContinuousLinearMap.proj a - (2 : ℝ) • rowLinear β x a.1 + gradientLinear β x)) x := by
  have hd := (hasFDerivAt_outerWeight β x a.1).mul (hasFDerivAt_innerWeight β x a)
  convert! hd using 1
  ext h
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, gradient]
  ring

end BMGordonSoftMinMax
