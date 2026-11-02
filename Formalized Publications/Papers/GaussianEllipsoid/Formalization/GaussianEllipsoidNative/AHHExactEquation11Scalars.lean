import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Scalar estimates for the independent joint-moment proof of AHH (11), k=2.
These results do not assert the sphere LSI or the ensemble moment hypotheses. -/
noncomputable section
namespace AHHExactEquation11

private theorem zero_le_of_deriv_nonneg (f d : ℝ → ℝ)
    (h0 : f 0 = 0)
    (hd : ∀ x, 0 ≤ x → HasDerivAt f (d x) x)
    (hd0 : ∀ x, 0 ≤ x → 0 ≤ d x) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      exact (hd y (Set.mem_Ici.mp (interior_subset hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hd y (Set.mem_Ici.mp (interior_subset hy))).deriv]
      exact hd0 y (Set.mem_Ici.mp (interior_subset hy))
  simpa only [h0] using hm (by simp) hx hx

private def lowerResidual (x : ℝ) : ℝ :=
  Real.log (1+x) - 2*x/(x+2) - 2*x^3/(3*(x+2)^3)

private theorem lowerResidual_deriv (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt lowerResidual (x^4 / ((x+1)*(x+2)^4)) x := by
  have h1 : 1+x ≠ 0 := by positivity
  have h2 : x+2 ≠ 0 := by positivity
  have h3 : 3*(x+2)^3 ≠ 0 := by positivity
  have hh :=
    ((((hasDerivAt_id x).const_add 1).log h1).sub
      (((hasDerivAt_id x).const_mul 2).div ((hasDerivAt_id x).add_const 2) h2)).sub
      ((((hasDerivAt_id x).pow 3).const_mul 2).div
        ((((hasDerivAt_id x).add_const 2).pow 3).const_mul 3) h3)
  convert hh using 1 <;> try rfl
  dsimp only [id_eq, Pi.pow_apply]
  norm_num
  field_simp
  <;> ring

theorem log_lower_cubic (x : ℝ) (hx : 0 ≤ x) :
    2*x/(x+2) + 2*x^3/(3*(x+2)^3) ≤ Real.log (1+x) := by
  have hr := zero_le_of_deriv_nonneg lowerResidual
    (fun y => y^4 / ((y+1)*(y+2)^4)) (by norm_num [lowerResidual])
    lowerResidual_deriv (by intro y hy; positivity) x hx
  dsimp [lowerResidual] at hr
  linarith

private def upperResidual (x : ℝ) : ℝ :=
  x/5 - x^2/50 + x^3/375 - Real.log (1+x/5)

private theorem upperResidual_deriv (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt upperResidual (x^3 / (125*(x+5))) x := by
  have h1 : 1+x/5 ≠ 0 := by positivity
  have hh :=
    ((((hasDerivAt_id x).div_const 5).sub
      (((hasDerivAt_id x).pow 2).div_const 50)).add
      (((hasDerivAt_id x).pow 3).div_const 375)).sub
      ((((hasDerivAt_id x).div_const 5).const_add 1).log h1)
  convert hh using 1 <;> try rfl
  dsimp only [id_eq, Pi.pow_apply]
  norm_num
  field_simp
  <;> ring

theorem log_upper_cubic (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1+x/5) ≤ x/5 - x^2/50 + x^3/375 := by
  have hr := zero_le_of_deriv_nonneg upperResidual
    (fun y => y^3 / (125*(y+5))) (by norm_num [upperResidual])
    upperResidual_deriv (by intro y hy; positivity) x hx
  dsimp [upperResidual] at hr
  linarith

def upperRate (x : ℝ) : ℝ :=
  x/5*Real.log (1+x) - (2+3*x/5)*Real.log (1+x/5) + 2*x/5

theorem upper_rate_ge (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x^2/16 ≤ upperRate x := by
  have hl := mul_le_mul_of_nonneg_left (log_lower_cubic x hx)
    (show 0 ≤ x/5 by positivity)
  have hu := mul_le_mul_of_nonneg_left (log_upper_cubic x hx)
    (show 0 ≤ 2+3*x/5 by positivity)
  have hx2 : x^2 ≤ 1 := by nlinarith
  have hx3 : x^3 ≤ 1 := by nlinarith [sq_nonneg x]
  have hx4 : x^4 ≤ 1 := by nlinarith [sq_nonneg (x^2), sq_nonneg (x^2-1)]
  have hx5 : x^5 ≤ 1 := by
    calc
      x^5 = x^4*x := by ring
      _ ≤ 1*x := mul_le_mul_of_nonneg_right hx4 hx
      _ ≤ 1 := by simpa using hx1
  have hpoly : 0 ≤ 13800-1700*x-7634*x^2-3651*x^3-88*x^4-48*x^5 := by
    linarith
  have hrat : 0 ≤ x^2*(13800-1700*x-7634*x^2-3651*x^3-88*x^4-48*x^5) /
      (30000*(x+2)^3) := by positivity
  have heq :
      x/5*(2*x/(x+2)+2*x^3/(3*(x+2)^3)) -
        (2+3*x/5)*(x/5-x^2/50+x^3/375)+2*x/5-x^2/16 =
      x^2*(13800-1700*x-7634*x^2-3651*x^3-88*x^4-48*x^5) /
        (30000*(x+2)^3) := by
    field_simp
    <;> ring
  rw [← heq] at hrat
  dsimp [upperRate]
  linarith

theorem lower_rate_le (h x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hlarge : 20 < h*x^2) :
    -(41/448)*(h-1)*x^2+(23/56)*x ≤ -h*x^2/16 := by
  have hx2 : x^2 ≤ 1 := by nlinarith
  nlinarith

#print axioms log_lower_cubic
#print axioms log_upper_cubic
#print axioms upper_rate_ge
#print axioms lower_rate_le

end AHHExactEquation11
