import ActualFixedVectorTail

noncomputable section
namespace GaussianEllipsoidCandidate

/-- The polynomial fixed-vector prefactor can be replaced by the paper's
logarithmic prefactor with an explicit eventual threshold and halved rate. -/
theorem paper_logarithmic_prefactor {A C x n : ℝ} (hA : 0 ≤ A) (hC : 0 < C)
    (hx : 1 ≤ x) (hlog : 1 ≤ Real.log x) (hn : n ≤ A*x^2)
    (hlarge : 48*C^3*(A+1) ≤ x) :
    (n+1)*Real.exp (-x^2/(C*Real.log x)) ≤
      Real.log x*Real.exp (-x^2/(2*C*Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hpoly : n+1 ≤ (x/(2*C))^3/6 := by
    calc n+1 ≤ (A+1)*x^2 := by nlinarith
      _ ≤ x^3/(48*C^3) := by
        apply (le_div_iff₀ (by positivity : 0 < 48*C^3)).mpr
        have h := mul_le_mul_of_nonneg_right hlarge (sq_nonneg x)
        nlinarith only [h]
      _ = _ := by field_simp; ring
  have hpow := Real.pow_div_factorial_le_exp (x/(2*C)) (by positivity : 0 ≤ x/(2*C)) 3
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, mul_one] at hpow
  have hlogle : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have harg : x/(2*C) ≤ x^2/(2*C*Real.log x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_left hlogle (by positivity : 0 ≤ 2*C*x)
    nlinarith only [h]
  have hexp : n+1 ≤ Real.exp (x^2/(2*C*Real.log x)) :=
    (hpoly.trans hpow).trans (Real.exp_le_exp.mpr harg)
  calc
    _ ≤ Real.exp (x^2/(2*C*Real.log x))*Real.exp (-x^2/(C*Real.log x)) :=
      mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg _)
    _ = Real.exp (-x^2/(2*C*Real.log x)) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ _ := by nlinarith [Real.exp_nonneg (-x^2/(2*C*Real.log x))]
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_logarithmic_prefactor
