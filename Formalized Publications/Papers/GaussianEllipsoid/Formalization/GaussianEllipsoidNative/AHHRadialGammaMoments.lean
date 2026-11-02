import AHHRadialMean
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! Real-power moments and logarithmic moment bounds for the actual Gamma measure.
The measure is Mathlib's `ProbabilityTheory.gammaMeasure`, with shape and rate
both equal to h. No assumed moment law, concentration axiom, or surrogate measure
appears in the statements. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set GaussianMixedNormHelpers
namespace AHHRadial

/-- The full real-power moment identity, valid whenever the moment exists. -/
theorem gamma_integral_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) :
    (∫ r : ℝ, r ^ q ∂gammaMeasure a b) =
      Real.Gamma (a + q) / (Real.Gamma a * b ^ q) := by
  rw [integral_gammaMeasure_eq_kernel ha hb]
  have hi : (∫ r : ℝ in Ioi 0, r ^ (a - 1) * (Real.exp (-b * r) * r ^ q)) =
      (∫ r : ℝ in Ioi 0, r ^ ((a + q) - 1) * Real.exp (-(b*r))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [show -b * r = -(b*r) by ring]
    calc
      _ = (r ^ (a-1) * r ^ q) * Real.exp (-(b*r)) := by ring
      _ = _ := by rw [← Real.rpow_add hr]; congr 2; ring
  rw [hi, Real.integral_rpow_mul_exp_neg_mul_Ioi haq hb,
    one_div, Real.inv_rpow hb.le, Real.rpow_add hb]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hb a),
    ne_of_gt (Real.rpow_pos_of_pos hb q), ne_of_gt (Real.Gamma_pos_of_pos ha)]

/-- Integrability follows from the positive, explicitly evaluated actual integral. -/
theorem gamma_integrable_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) :
    Integrable (fun r : ℝ => r ^ q) (gammaMeasure a b) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_integral_rpow ha hb haq]
  exact ne_of_gt (div_pos (Real.Gamma_pos_of_pos haq)
    (mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos hb q)))

theorem gamma_integral_rpow_pos {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) :
    0 < ∫ r : ℝ, r ^ q ∂gammaMeasure a b := by
  rw [gamma_integral_rpow ha hb haq]
  exact div_pos (Real.Gamma_pos_of_pos haq)
    (mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos hb q))

theorem gamma_log_integral_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a + q) :
    Real.log (∫ r : ℝ, r ^ q ∂gammaMeasure a b) =
      Real.log (Real.Gamma (a+q)) - Real.log (Real.Gamma a) - q*Real.log b := by
  rw [gamma_integral_rpow ha hb haq,
    Real.log_div (Real.Gamma_pos_of_pos haq).ne'
      (mul_pos (Real.Gamma_pos_of_pos ha) (Real.rpow_pos_of_pos hb q)).ne',
    Real.log_mul (Real.Gamma_pos_of_pos ha).ne' (Real.rpow_pos_of_pos hb q).ne',
    Real.log_rpow hb]
  ring

private theorem differentiableAt_logGamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (Real.log ∘ Real.Gamma) x := by
  apply DifferentiableAt.log
  · exact Real.differentiableAt_Gamma (by intro m; have := Nat.cast_nonneg (α := ℝ) m; linarith)
  · exact (Real.Gamma_pos_of_pos hx).ne'

/-- The logarithmic Gamma derivative is bounded by its forward unit secant. -/
theorem deriv_logGamma_le {x : ℝ} (hx : 0 < x) :
    deriv (Real.log ∘ Real.Gamma) x ≤ Real.log x := by
  have h := Real.convexOn_log_Gamma.deriv_le_slope hx
    (show x+1 ∈ Ioi (0:ℝ) by change (0:ℝ) < _; linarith) (by linarith)
    (differentiableAt_logGamma hx)
  simpa [slope_def_field, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne'] using h

/-- The backward unit secant gives the matching lower bound past one. -/
theorem log_sub_one_le_deriv_logGamma {x : ℝ} (hx : 1 < x) :
    Real.log (x-1) ≤ deriv (Real.log ∘ Real.Gamma) x := by
  have hxm : 0 < x-1 := by linarith
  have h := Real.convexOn_log_Gamma.slope_le_deriv hxm
    (show x ∈ Ioi (0:ℝ) by change (0:ℝ) < _; linarith) (by linarith : x-1 < x)
    (differentiableAt_logGamma (by linarith))
  have hg : Real.Gamma x = (x-1)*Real.Gamma (x-1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one hxm.ne'
  simpa [slope_def_field, hg,
    Real.log_mul hxm.ne' (Real.Gamma_pos_of_pos hxm).ne'] using h


private theorem hasDerivAt_upperGammaResidual {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y*Real.log y - y - Real.log (Real.Gamma y))
      (Real.log x - deriv (Real.log ∘ Real.Gamma) x) x := by
  have hd := (((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).sub
    (hasDerivAt_id x)).sub (differentiableAt_logGamma hx).hasDerivAt
  convert hd using 1 <;> try rfl
  dsimp only [id_eq]
  rw [one_mul, mul_inv_cancel₀ hx.ne']
  ring

private theorem upperGammaResidual_monotone :
    MonotoneOn (fun y : ℝ => y*Real.log y - y - Real.log (Real.Gamma y)) (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · intro x hx
    exact (hasDerivAt_upperGammaResidual hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_upperGammaResidual (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [(hasDerivAt_upperGammaResidual (interior_subset hx)).deriv]
    exact sub_nonneg.mpr (deriv_logGamma_le (interior_subset hx))

/-- The positive-power log moment bound used in the joint upper tail. -/
theorem gamma_log_moment_upper {h q : ℝ} (hh : 0 < h) (hq : 0 ≤ q) :
    Real.log (∫ r : ℝ, r ^ q ∂gammaMeasure h h) ≤
      h*((1+q/h)*Real.log (1+q/h)-q/h) := by
  have hhq : 0 < h+q := by linarith
  have hm := upperGammaResidual_monotone hh hhq (show h ≤ h+q by linarith)
  have hc : 0 < 1+q/h := by positivity
  have he : h+q = h*(1+q/h) := by field_simp
  have hl : Real.log (h+q) = Real.log h + Real.log (1+q/h) := by
    rw [he, Real.log_mul hh.ne' hc.ne']
  rw [gamma_log_integral_rpow hh hh hhq]
  dsimp only at hm
  rw [hl] at hm
  have heq : h*((1+q/h)*Real.log (1+q/h)-q/h) =
      (h+q)*Real.log (1+q/h)-q := by field_simp
  rw [heq]
  nlinarith

/-- A denominator-uniform bound on the logarithmic Gamma derivative along
    the negative-moment interval. -/
private theorem negative_moment_deriv_le {h t s : ℝ} (hh : 1 < h)
    (ht : t < h-1) (hs0 : 0 ≤ s) (hst : s ≤ t) :
    Real.log h - deriv (Real.log ∘ Real.Gamma) (h-s) ≤
      (1+s)/(h-1-t) := by
  have hd : 0 < h-1-t := by linarith
  have hs : 0 < h-1-s := by linarith
  have hh0 : 0 < h := by linarith
  have hpsi := log_sub_one_le_deriv_logGamma (show 1 < h-s by linarith)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hh0 hs)
  rw [Real.log_div hh0.ne' hs.ne'] at hlog
  have heq : h/(h-1-s)-1 = (1+s)/(h-1-s) := by field_simp; ring
  rw [heq] at hlog
  have hfrac : (1+s)/(h-1-s) ≤ (1+s)/(h-1-t) := by
    exact div_le_div_of_nonneg_left (by linarith) hd (by linarith)
  have harg : h-s-1 = h-1-s := by ring
  rw [harg] at hpsi
  linarith

private theorem hasDerivAt_lowerGammaResidual {h t s : ℝ}
    (hhs : 0 < h-s) :
    HasDerivAt (fun x : ℝ => (x+x^2/2)/(h-1-t) -
      (Real.log (Real.Gamma (h-x))-Real.log (Real.Gamma h)+x*Real.log h))
      ((1+s)/(h-1-t) + deriv (Real.log ∘ Real.Gamma) (h-s) - Real.log h) s := by
  have hd := (((hasDerivAt_id s).add (((hasDerivAt_id s).pow 2).div_const 2)).div_const
    (h-1-t)).sub
      ((((differentiableAt_logGamma hhs).hasDerivAt.comp s
        ((hasDerivAt_id s).const_sub h)).sub_const (Real.log (Real.Gamma h))).add
          ((hasDerivAt_id s).mul_const (Real.log h)))
  convert hd using 1 <;> try rfl
  dsimp only [id_eq]
  norm_num
  ring

/-- The negative-power log moment bound used in the joint lower tail. -/
theorem gamma_log_moment_lower {h t : ℝ} (hh : 1 < h) (ht0 : 0 ≤ t)
    (ht : t < h-1) :
    Real.log (∫ r : ℝ, r ^ (-t) ∂gammaMeasure h h) ≤
      (t+t^2/2)/(h-1-t) := by
  let f : ℝ → ℝ := fun x => (x+x^2/2)/(h-1-t) -
    (Real.log (Real.Gamma (h-x))-Real.log (Real.Gamma h)+x*Real.log h)
  have hd : ∀ s ∈ Icc 0 t, HasDerivAt f
      ((1+s)/(h-1-t) + deriv (Real.log ∘ Real.Gamma) (h-s) - Real.log h) s := by
    intro s hs
    exact hasDerivAt_lowerGammaResidual (by rcases hs with ⟨hs0,hst⟩; linarith)
  have hm : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) t)
    · intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      rw [(hd s hs').deriv]
      have hb := negative_moment_deriv_le hh ht hs'.1 hs'.2
      linarith
  have hf := hm (show 0 ∈ Icc 0 t by exact ⟨le_rfl,ht0⟩)
    (show t ∈ Icc 0 t by exact ⟨ht0,le_rfl⟩) ht0
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0] at hf
  rw [gamma_log_integral_rpow (by linarith) (by linarith) (by linarith)]
  dsimp only [f] at hf
  simp only [sub_eq_add_neg] at hf ⊢
  linarith


/-- Gamma measures are concentrated on strictly positive reals. -/
theorem gamma_ae_pos (a b : ℝ) : ∀ᵐ r ∂gammaMeasure a b, 0 < r := by
  rw [ae_iff]
  simp only [not_lt]
  change gammaMeasure a b (Iic 0) = 0
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic,
    lintegral_Iic_eq_lintegral_Iio_add_Icc _ (le_refl (0:ℝ)),
    lintegral_gammaPDF_of_nonpos (le_refl (0:ℝ))]
  simp

/-- Real powers and exponential logarithmic moments agree under the genuine law. -/
theorem gamma_rpow_ae_eq_exp_log (a b q : ℝ) :
    (fun r : ℝ => r^q) =ᵐ[gammaMeasure a b] (fun r => Real.exp (q*Real.log r)) := by
  filter_upwards [gamma_ae_pos a b] with r hr
  rw [Real.rpow_def_of_pos hr, mul_comm]

theorem gamma_integrable_exp_log {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a+q) :
    Integrable (fun r : ℝ => Real.exp (q*Real.log r)) (gammaMeasure a b) :=
  (gamma_integrable_rpow ha hb haq).congr (gamma_rpow_ae_eq_exp_log a b q)

theorem gamma_integral_exp_log {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (haq : 0 < a+q) :
    (∫ r : ℝ, Real.exp (q*Real.log r) ∂gammaMeasure a b) =
      Real.Gamma (a+q)/(Real.Gamma a*b^q) := by
  rw [← integral_congr_ae (gamma_rpow_ae_eq_exp_log a b q), gamma_integral_rpow ha hb haq]

/-- Direct exponential-form upper bound, ready for exponential Markov. -/
theorem gamma_exp_moment_upper {h q : ℝ} (hh : 0 < h) (hq : 0 ≤ q) :
    (∫ r : ℝ, Real.exp (q*Real.log r) ∂gammaMeasure h h) ≤
      Real.exp (h*((1+q/h)*Real.log (1+q/h)-q/h)) := by
  rw [← integral_congr_ae (gamma_rpow_ae_eq_exp_log h h q)]
  exact (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (gamma_log_moment_upper hh hq))

/-- Direct exponential-form inverse moment bound. -/
theorem gamma_exp_moment_lower {h t : ℝ} (hh : 1 < h) (ht0 : 0 ≤ t)
    (ht : t < h-1) :
    (∫ r : ℝ, Real.exp (-t*Real.log r) ∂gammaMeasure h h) ≤
      Real.exp ((t+t^2/2)/(h-1-t)) := by
  rw [← integral_congr_ae (gamma_rpow_ae_eq_exp_log h h (-t))]
  exact (Real.le_exp_log _).trans (Real.exp_le_exp.mpr (gamma_log_moment_lower hh ht0 ht))

#print axioms gamma_integral_rpow
#print axioms gamma_integrable_rpow
#print axioms gamma_integral_rpow_pos
#print axioms gamma_log_integral_rpow
#print axioms deriv_logGamma_le
#print axioms log_sub_one_le_deriv_logGamma
#print axioms gamma_log_moment_upper
#print axioms gamma_log_moment_lower
#print axioms gamma_ae_pos
#print axioms gamma_rpow_ae_eq_exp_log
#print axioms gamma_integrable_exp_log
#print axioms gamma_integral_exp_log
#print axioms gamma_exp_moment_upper
#print axioms gamma_exp_moment_lower
end AHHRadial
