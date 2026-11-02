import AHHRadialGammaMoments
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine independent pairs of Gamma radii. The product probability measure
is explicit. These exponential moments use the sum of the two logarithms,
which is the logarithm of their product almost everywhere. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace AHHRadial

/-- Integrability of the joint logarithmic moment of two independent radii. -/
theorem gamma_pair_integrable_exp_log {h q : ℝ} (hh : 0 < h) (hhq : 0 < h+q) :
    Integrable (fun p : ℝ × ℝ => Real.exp (q*(Real.log p.1+Real.log p.2)))
      ((gammaMeasure h h).prod (gammaMeasure h h)) := by
  have := isProbabilityMeasure_gammaMeasure hh hh
  have hi := gamma_integrable_exp_log hh hh hhq
  simpa only [mul_add, Real.exp_add] using hi.mul_prod hi

/-- Exact joint moment under the explicit product Gamma measure. -/
theorem gamma_pair_integral_exp_log {h q : ℝ} (hh : 0 < h) (hhq : 0 < h+q) :
    (∫ p : ℝ × ℝ, Real.exp (q*(Real.log p.1+Real.log p.2))
      ∂((gammaMeasure h h).prod (gammaMeasure h h))) =
      (Real.Gamma (h+q)/(Real.Gamma h*h^q))^2 := by
  have := isProbabilityMeasure_gammaMeasure hh hh
  simp_rw [mul_add, Real.exp_add]
  rw [integral_prod_mul (fun r : ℝ => Real.exp (q*Real.log r))
    (fun r : ℝ => Real.exp (q*Real.log r)), gamma_integral_exp_log hh hh hhq, pow_two]

/-- Two independent radii contribute twice the upper log-moment bound. -/
theorem gamma_pair_exp_moment_upper {h q : ℝ} (hh : 0 < h) (hq : 0 ≤ q) :
    (∫ p : ℝ × ℝ, Real.exp (q*(Real.log p.1+Real.log p.2))
      ∂((gammaMeasure h h).prod (gammaMeasure h h))) ≤
      Real.exp (2*h*((1+q/h)*Real.log (1+q/h)-q/h)) := by
  have := isProbabilityMeasure_gammaMeasure hh hh
  simp_rw [mul_add, Real.exp_add]
  rw [integral_prod_mul (fun r : ℝ => Real.exp (q*Real.log r))
    (fun r : ℝ => Real.exp (q*Real.log r))]
  have hm := gamma_exp_moment_upper hh hq
  have hn : 0 ≤ ∫ r : ℝ, Real.exp (q*Real.log r) ∂gammaMeasure h h :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp (h*((1+q/h)*Real.log (1+q/h)-q/h)) *
        Real.exp (h*((1+q/h)*Real.log (1+q/h)-q/h)) :=
      mul_le_mul hm hm hn (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Two independent radii contribute twice the inverse log-moment bound. -/
theorem gamma_pair_exp_moment_lower {h t : ℝ} (hh : 1 < h) (ht0 : 0 ≤ t)
    (ht : t < h-1) :
    (∫ p : ℝ × ℝ, Real.exp (-t*(Real.log p.1+Real.log p.2))
      ∂((gammaMeasure h h).prod (gammaMeasure h h))) ≤
      Real.exp ((2*t+t^2)/(h-1-t)) := by
  have := isProbabilityMeasure_gammaMeasure (show 0 < h by linarith) (show 0 < h by linarith)
  simp_rw [mul_add, Real.exp_add]
  rw [integral_prod_mul (fun r : ℝ => Real.exp (-t*Real.log r))
    (fun r : ℝ => Real.exp (-t*Real.log r))]
  have hm := gamma_exp_moment_lower hh ht0 ht
  have hn : 0 ≤ ∫ r : ℝ, Real.exp (-t*Real.log r) ∂gammaMeasure h h :=
    integral_nonneg (fun _ => (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp ((t+t^2/2)/(h-1-t))*Real.exp ((t+t^2/2)/(h-1-t)) :=
      mul_le_mul hm hm hn (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms gamma_pair_integrable_exp_log
#print axioms gamma_pair_integral_exp_log
#print axioms gamma_pair_exp_moment_upper
#print axioms gamma_pair_exp_moment_lower
end AHHRadial
