import FourThirdScalarMoments

noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace BMFourThirdMoment

/-- Coarse but uniform fractional-moment control after shifting by one. -/
lemma abs_sub_one_four_thirds_le (a : ℝ) :
    |a - 1| ^ (4 / 3 : ℝ) ≤ 4 * (|a| ^ (4 / 3 : ℝ) + 1) := by
  have htri : |a - 1| ≤ |a| + 1 := by simpa using abs_sub_le a 0 1
  have htwo : (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ^ (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hnonneg : 0 ≤ |a| ^ (4 / 3 : ℝ) := Real.rpow_nonneg (abs_nonneg a) _
  by_cases ha : |a| ≤ 1
  · have hb : |a - 1| ≤ 2 := by linarith
    have hp := Real.rpow_le_rpow (abs_nonneg (a - 1)) hb (show (0 : ℝ) ≤ 4 / 3 by norm_num)
    nlinarith
  · have hb : |a - 1| ≤ 2 * |a| := by linarith
    calc
      |a - 1| ^ (4 / 3 : ℝ) ≤ (2 * |a|) ^ (4 / 3 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg (a - 1)) hb (by norm_num)
      _ = (2 : ℝ) ^ (4 / 3 : ℝ) * |a| ^ (4 / 3 : ℝ) :=
        Real.mul_rpow (by norm_num) (abs_nonneg a)
      _ ≤ 4 * |a| ^ (4 / 3 : ℝ) := mul_le_mul_of_nonneg_right htwo hnonneg
      _ ≤ 4 * (|a| ^ (4 / 3 : ℝ) + 1) := by linarith

/-- Finite-sum version of the shift bound; the moment constant becomes 4(K+1). -/
theorem sum_abs_sub_one_four_thirds_le {n : ℕ} (a : Fin n → ℝ) {K : ℝ}
    (hmoment : (∑ i, |a i| ^ (4 / 3 : ℝ)) ≤ K * n) :
    (∑ i, |a i - 1| ^ (4 / 3 : ℝ)) ≤ (4 * (K + 1)) * n := by
  calc
    (∑ i, |a i - 1| ^ (4 / 3 : ℝ)) ≤ ∑ i, 4 * (|a i| ^ (4 / 3 : ℝ) + 1) :=
      Finset.sum_le_sum fun i _ => abs_sub_one_four_thirds_le (a i)
    _ = 4 * ((∑ i, |a i| ^ (4 / 3 : ℝ)) + n) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ 4 * (K * n + n) := by linarith
    _ = (4 * (K + 1)) * n := by ring


#print axioms abs_sub_one_four_thirds_le
#print axioms sum_abs_sub_one_four_thirds_le
end BMFourThirdMoment
