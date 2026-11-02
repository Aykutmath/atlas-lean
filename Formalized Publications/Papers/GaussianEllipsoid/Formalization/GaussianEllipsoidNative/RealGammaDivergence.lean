import RealGammaMoment
import GammaExtendedMoment
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace GaussianMixedNormHelpers

/-- A nonintegrable power at zero stays nonintegrable after exponential damping. -/
theorem not_integrableOn_rpow_exp_near_zero (p b : ℝ) (hp : p ≤ -1) (hb : 0 ≤ b) :
    ¬ IntegrableOn (fun x : ℝ => x^p * Real.exp (-b*x)) (Ioi 0) := by
  intro h
  have hsmall : IntegrableOn (fun x : ℝ => x^p * Real.exp (-b*x)) (Ioo 0 1) :=
    h.mono_set (fun _ hx => hx.1)
  have hpow : IntegrableOn (fun x : ℝ => x^p) (Ioo 0 1) := by
    apply (hsmall.const_mul (Real.exp b)).mono'
      ((measurable_id.pow_const p).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simp only [id_eq]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le p)]
    have he : 1 ≤ Real.exp b * Real.exp (-b*x) := by
      rw [← Real.exp_add]
      have hz : 0 ≤ b + -b*x := by nlinarith [mul_nonneg hb (sub_nonneg.mpr hx.2.le)]
      simpa using Real.exp_le_exp.mpr hz
    have hm := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hx.1.le p)
    nlinarith
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ)<1)).mp hpow
  linarith

/-- The Gamma inverse moment diverges at and beyond its exact critical exponent. -/
theorem not_integrable_gammaMeasure_half_negative_real (a s : ℝ)
    (ha : 0 < a) (has : a ≤ s) :
    ¬ Integrable (fun x : ℝ => x^(-s)) (gammaMeasure a (1/2)) := by
  intro h
  have hg : Integrable (fun x : ℝ => gammaPDFReal a (1/2) x * x^(-s)) volume := by
    have h' := (integrable_withDensity_iff_integrable_smul'
      ((measurable_gammaPDFReal a (1/2)).ennreal_ofReal)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mp h
    have hr : (0:ℝ) < 1/2 := by norm_num
    simpa only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul] using h'
  have hpos : (2:ℝ)^(a) * Real.Gamma a ≠ 0 := by positivity
  have hscaled := (hg.const_mul ((2:ℝ)^a * Real.Gamma a)).integrableOn (s := Ioi 0)
  have heq : Set.EqOn
      (fun x : ℝ => (2^a * Real.Gamma a) * (gammaPDFReal a (1/2) x * x^(-s)))
      (fun x : ℝ => x^(a-s-1)*Real.exp (-(1/2)*x)) (Ioi 0) := by
    intro x hx
    dsimp only
    rw [gammaPDFReal_half_eq_chiSquareKernel hx]
    unfold chiSquareKernel
    have hp : x^(a-1)*x^(-s) = x^(a-s-1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    calc
      _ = (x^(a-1)*x^(-s))*Real.exp (-(1/2)*x) := by
        rw [show -(x/2) = -(1/2)*x by ring]
        field_simp
      _ = _ := by rw [hp]
  have hh := hscaled.congr_fun heq measurableSet_Ioi
  exact not_integrableOn_rpow_exp_near_zero (a-s-1) (1/2) (by linarith) (by norm_num) hh

#print axioms not_integrable_gammaMeasure_half_negative_real
end GaussianMixedNormHelpers
