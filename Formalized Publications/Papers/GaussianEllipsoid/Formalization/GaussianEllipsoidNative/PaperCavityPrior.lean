import BMBoundedHessian

/-! New reconstruction: fixed-prior domination and its sum of sup norms. -/
noncomputable section
open BMFiniteGibbsTest BMFiniteGibbsHessian
open scoped BigOperators BoundedContinuousFunction
namespace PaperCavityPrior
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Sum is taken after each individual norm, preserving the prior mass. -/
def priorMass {E : Type*} [NormedAddCommGroup E] (p : κ → E) : ℝ :=
  ∑ a, ‖p a‖

theorem priorMass_nonneg {E : Type*} [NormedAddCommGroup E] (p : κ → E) :
    0 ≤ priorMass p := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem probability_le_exp_prior (D : Data κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (y : κ → ℝ) (a : κ) :
    probability D y a ≤ Real.exp D.beta * D.weight a := by
  have hlo : Real.exp (-D.beta) ≤ partition D y := by
    calc
      _ = ∑ b, D.weight b * Real.exp (-D.beta) := by
        rw [← Finset.sum_mul, D.weight_sum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun b _ =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          have hb := D.beta_nonneg
          have hu := (hunit (y b)).2
          nlinarith)) (D.weight_nonneg b)
  have hnum : D.weight a * Real.exp (-D.beta * D.potential (y a)) ≤ D.weight a := by
    calc
      _ ≤ D.weight a * Real.exp 0 := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by
          have hb := D.beta_nonneg
          have hu := (hunit (y a)).1
          nlinarith)) (D.weight_nonneg a)
      _ = _ := by rw [Real.exp_zero, mul_one]
  apply (div_le_iff₀ (partition_pos D y)).mpr
  calc
    _ ≤ D.weight a := hnum
    _ = (Real.exp D.beta * D.weight a) * Real.exp (-D.beta) := by
      rw [mul_right_comm, ← Real.exp_add]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo
      (mul_nonneg (Real.exp_nonneg _) (D.weight_nonneg a))

#print axioms probability_le_exp_prior
end PaperCavityPrior
