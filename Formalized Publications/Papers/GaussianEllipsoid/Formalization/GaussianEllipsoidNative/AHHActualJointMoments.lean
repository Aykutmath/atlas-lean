import AHHActualLogSelection
import AHHRadialWeightMoments
import AHHSphereExponentialMoments

/-! Joint radial/angular exponential moments for the concrete polar law.
The only analytic premise is the named concrete sphere entropy inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers
namespace AHHRadial

theorem polarLog_exp_integrable (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (i : Fin n) (q : ℝ) (hq : 0 < (h : ℝ)+q) :
    Integrable (fun w => Real.exp (q*polarLog n h i w)) (polarLaw n h) := by
  have hi := (radialWeight_exp_integrable n h hh i q hq).mul_prod
    (sphere_normalized_exp_integrable n h hn hh q)
  simpa only [polarLaw, polarLog, mul_add, Real.exp_add] using hi

theorem polarLog_exp_integral (n h : ℕ) (hh : 0 < h) (i : Fin n) (q : ℝ) :
    (∫ w, Real.exp (q*polarLog n h i w) ∂polarLaw n h) =
      (∫ r, Real.exp (q*Real.log (radialWeight r i)) ∂radiiLaw n h) *
      (∫ d, Real.exp (q*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
        ∂directionsLaw n h) := by
  letI := radiiLaw_probability n h hh
  letI := directionsLaw_probability n h hh
  simp only [polarLaw, polarLog, mul_add, Real.exp_add]
  exact integral_prod_mul
    (fun r : Fin n → Radius × Radius => Real.exp (q*Real.log (radialWeight r i)))
    (fun d : Directions n h => Real.exp (q*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h)))

theorem polarLog_upper_exp_le (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) (i : Fin n) (q : ℝ)
    (hq : 1 ≤ q) (hqh : q ≤ h) :
    (∫ w, Real.exp (q*polarLog n h i w) ∂polarLaw n h) ≤
      Real.exp (2*(h : ℝ)*((1+q/h)*Real.log (1+q/h)-q/h) + q*Real.log (1+q/h)) := by
  rw [polarLog_exp_integral n h (by omega)]
  have hr := radialWeight_upper_exp_le n h (by omega) i q (by linarith)
  have hs := sphere_normalized_upper_exp_le n h hn hh hEntropy q hq hqh
  calc
    _ ≤ Real.exp (2*(h : ℝ)*((1+q/h)*Real.log (1+q/h)-q/h)) *
        Real.exp (q*Real.log (1+q/h)) := mul_le_mul hr hs
          (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem polarLog_lower_exp_le (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) (i : Fin n) (t : ℝ)
    (ht : 0 ≤ t) (hth : t < (h : ℝ)-1) :
    (∫ w, Real.exp (-t*polarLog n h i w) ∂polarLaw n h) ≤
      Real.exp ((2*t+t^2)/((h : ℝ)-1-t) + t*(t+1)/((h : ℝ)-1)) := by
  rw [polarLog_exp_integral n h (by omega)]
  have hr := radialWeight_lower_exp_le n h hh i t ht hth
  have hs := sphere_normalized_negative_exp_le n h hn hh hEntropy t ht
  calc
    _ ≤ Real.exp ((2*t+t^2)/((h : ℝ)-1-t)) *
        Real.exp (t*(t+1)/((h : ℝ)-1)) := mul_le_mul hr hs
          (integral_nonneg (fun _ => (Real.exp_pos _).le)) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

/-- Numerical parameters for the nontrivial regime. -/
theorem large_regime_parameters (h : ℕ) (e : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hlarge : 20 < (h : ℝ)*e^2) :
    2 ≤ h ∧ 1 ≤ (h : ℝ)*e/5 ∧ (h : ℝ)*e/5 ≤ h := by
  have he2 : e^2 ≤ 1 := by nlinarith
  have he2e : e^2 ≤ e := by nlinarith
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hh20 : (20 : ℝ) < h := by nlinarith
  have hh2 : 2 ≤ h := by exact_mod_cast (show (2 : ℝ) ≤ h by linarith)
  exact ⟨hh2, by nlinarith, by nlinarith⟩

theorem polarLog_upper_epsilon_moment (n h : ℕ) (hn : 0 < n)
    (hEntropy : SpherePowerEntropyBound n h) (e : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hlarge : 20 < (h : ℝ)*e^2) (i : Fin n) :
    (∫ w, Real.exp (((h : ℝ)*e/5)*polarLog n h i w) ∂polarLaw n h) ≤
      Real.exp ((h : ℝ)*((2+3*e/5)*Real.log (1+e/5)-2*e/5)) := by
  obtain ⟨hh, hq, hqh⟩ := large_regime_parameters h e he he1 hlarge
  have hm := polarLog_upper_exp_le n h hn hh hEntropy i ((h : ℝ)*e/5) hq hqh
  have hh0 : (h : ℝ) ≠ 0 := by positivity
  have heq : (h : ℝ)*e/5/(h : ℝ) = e/5 := by field_simp
  simp only [heq] at hm
  convert hm using 1 <;> congr 1 <;> ring

theorem polarLog_lower_epsilon_moment (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) (e : ℝ) (he : 0 ≤ e) (he1 : e ≤ 1)
    (i : Fin n) :
    (∫ w, Real.exp (-(((h : ℝ)-1)*e/8)*polarLog n h i w) ∂polarLaw n h) ≤
      Real.exp (((15/7)*(((h : ℝ)-1)*e/8)^2+(23/7)*(((h : ℝ)-1)*e/8))/((h : ℝ)-1)) := by
  let a : ℝ := (h : ℝ)-1
  let t : ℝ := a*e/8
  have ha : 0 < a := by
    have hhR : (1 : ℝ) < h := by exact_mod_cast hh
    dsimp [a]
    linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht8 : 8*t ≤ a := by dsimp [t]; nlinarith
  have hth : t < a := by linarith
  have hm := polarLog_lower_exp_le n h hn hh hEntropy i t ht hth
  have hnum : 0 ≤ 2*t+t^2 := by positivity
  have hd : (2*t+t^2)/(a-t) ≤ (8/7)*(2*t+t^2)/a := by
    apply (div_le_div_iff₀ (by linarith : 0 < a-t) ha).mpr
    have hp := mul_le_mul_of_nonneg_right ht8 hnum
    nlinarith
  have hb : (2*t+t^2)/(a-t)+t*(t+1)/a ≤ ((15/7)*t^2+(23/7)*t)/a := by
    calc
      _ ≤ (8/7)*(2*t+t^2)/a+t*(t+1)/a := add_le_add hd le_rfl
      _ = _ := by ring
  exact hm.trans (Real.exp_le_exp.mpr hb)

#print axioms polarLog_exp_integrable
#print axioms polarLog_upper_epsilon_moment
#print axioms polarLog_lower_epsilon_moment
end AHHRadial
