import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BMGordonSoftMinMax
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]

/-- Inner positive exponential partition function. -/
def rowSum (β : ℝ) (x : I × J → ℝ) (i : I) : ℝ :=
  ∑ j, Real.exp (β * x (i,j))

/-- Partition function for the outer soft minimum. -/
def outerSum (β : ℝ) (x : I × J → ℝ) : ℝ :=
  ∑ i, (rowSum β x i)⁻¹

/-- The actual nested soft maximum/minimum, with a common inverse temperature. -/
def softMinMax (β : ℝ) (x : I × J → ℝ) : ℝ :=
  -Real.log (outerSum β x) / β

/-- Conditional Gibbs probabilities within each row. -/
def innerWeight (β : ℝ) (x : I × J → ℝ) (a : I × J) : ℝ :=
  Real.exp (β * x a) / rowSum β x a.1

/-- Gibbs probabilities of the outer soft minimum. -/
def outerWeight (β : ℝ) (x : I × J → ℝ) (i : I) : ℝ :=
  (rowSum β x i)⁻¹ / outerSum β x

/-- Entries of the gradient of the actual nested soft minmax. -/
def gradient (β : ℝ) (x : I × J → ℝ) (a : I × J) : ℝ :=
  outerWeight β x a.1 * innerWeight β x a

variable (β : ℝ) (x : I × J → ℝ)

theorem rowSum_pos (i : I) : 0 < rowSum β x i :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem outerSum_pos : 0 < outerSum β x :=
  Finset.sum_pos (fun i _ => inv_pos.mpr (rowSum_pos β x i)) Finset.univ_nonempty

theorem innerWeight_pos (a : I × J) : 0 < innerWeight β x a :=
  div_pos (Real.exp_pos _) (rowSum_pos β x a.1)

theorem outerWeight_pos (i : I) : 0 < outerWeight β x i :=
  div_pos (inv_pos.mpr (rowSum_pos β x i)) (outerSum_pos β x)

theorem innerWeight_sum (i : I) : ∑ j, innerWeight β x (i,j) = 1 := by
  simp only [innerWeight, ← Finset.sum_div, rowSum]
  exact div_self (ne_of_gt (rowSum_pos β x i))

theorem outerWeight_sum : ∑ i, outerWeight β x i = 1 := by
  simp only [outerWeight, ← Finset.sum_div, outerSum]
  exact div_self (ne_of_gt (outerSum_pos β x))

theorem innerWeight_le_one (a : I × J) : innerWeight β x a ≤ 1 := by
  have h := Finset.single_le_sum (fun j _ => (innerWeight_pos β x (a.1,j)).le)
    (Finset.mem_univ a.2)
  simpa only [innerWeight_sum, Prod.mk.eta] using h

theorem outerWeight_le_one (i : I) : outerWeight β x i ≤ 1 := by
  have h := Finset.single_le_sum (fun k _ => (outerWeight_pos β x k).le)
    (Finset.mem_univ i)
  simpa only [outerWeight_sum] using h

theorem gradient_pos (a : I × J) : 0 < gradient β x a :=
  mul_pos (outerWeight_pos β x a.1) (innerWeight_pos β x a)

theorem gradient_le_one (a : I × J) : gradient β x a ≤ 1 := by
  exact (mul_le_mul (outerWeight_le_one β x a.1) (innerWeight_le_one β x a)
    (innerWeight_pos β x a).le zero_le_one).trans_eq (one_mul 1)

theorem gradient_sum : ∑ a, gradient β x a = 1 := by
  simp only [Fintype.sum_prod_type, gradient, ← Finset.mul_sum, innerWeight_sum, mul_one,
    outerWeight_sum]

end BMGordonSoftMinMax
