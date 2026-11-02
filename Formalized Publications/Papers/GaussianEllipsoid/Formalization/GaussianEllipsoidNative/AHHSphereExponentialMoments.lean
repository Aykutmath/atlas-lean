import AHHSphereMomentReduction

/-! Normalized exponential-moment interfaces for the actual sphere law.
All estimates remain conditional on `SpherePowerEntropyBound`; integrability
and the real-power/exponential identifications are unconditional. -/
noncomputable section
open MeasureTheory ProbabilityTheory AHHBoundedPositiveMoments
namespace AHHRadial

theorem sphere_normalized_exp_eq_rpow (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (p : ℝ) (d : Directions n h) :
    Real.exp (p*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h)) =
      (unitCovarianceNorm n h d / unitCovarianceMean n h)^p := by
  rw [Real.rpow_def_of_pos (div_pos
    (by linarith [one_le_unitCovarianceNorm n h hn d])
    (by linarith [one_le_unitCovarianceMean n h hn hh]))]
  congr 1
  ring

theorem sphere_normalized_exp_integrable (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (p : ℝ) : Integrable (fun d =>
      Real.exp (p*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h)))
      (directionsLaw n h) := by
  simp_rw [sphere_normalized_exp_eq_rpow n h hn hh p]
  exact normalized_unitCovarianceNorm_rpow_integrable n h hn hh p

theorem sphere_normalized_exp_integral_pos (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (p : ℝ) : 0 < ∫ d,
      Real.exp (p*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h := by
  letI := directionsLaw_probability n h hh
  exact ProbabilityTheory.mgf_pos (sphere_normalized_exp_integrable n h hn hh p)

theorem sphere_normalized_negative_exp_le (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) (t : ℝ) (ht : 0 ≤ t) :
    (∫ d, Real.exp (-t*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h) ≤ Real.exp (t*(t+1)/((h : ℝ)-1)) := by
  have hlog := (sphere_moments_of_powerEntropy n h hn hh hEntropy).2 t ht
  have hpos := sphere_normalized_exp_integral_pos n h hn (by omega) (-t)
  have heq : (∫ d,
      Real.exp (-t*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h) =
      ∫ d, (unitCovarianceNorm n h d / unitCovarianceMean n h)^(-t)
        ∂directionsLaw n h := by
    simp_rw [sphere_normalized_exp_eq_rpow n h hn (by omega) (-t)]
  rw [← heq] at hlog
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog

/-- Positive normalized moments whenever the exponent lies between 1 and h. -/
theorem sphere_normalized_upper_exp_le (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) (q : ℝ) (hq : 1 ≤ q) (hqh : q ≤ h) :
    (∫ d, Real.exp (q*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h) ≤ Real.exp (q*Real.log (1+q/(h : ℝ))) := by
  have hh0 : 0 < h := by omega
  have hhr : 0 < (h : ℝ) := by exact_mod_cast hh0
  have hha : 0 < (h : ℝ)-1 := by exact_mod_cast (show 0 < (h : ℤ)-1 by omega)
  have hq0 : 0 < q := by linarith
  have hmu := one_le_unitCovarianceMean n h hn hh0
  have hmupos : 0 < unitCovarianceMean n h := by linarith
  have hdelta : (q-1)/((h : ℝ)-1) ≤ q/(h : ℝ) := by
    apply (div_le_div_iff₀ hha hhr).mpr
    nlinarith
  have hroot := (sphere_moments_of_powerEntropy n h hn hh hEntropy).1 q hq
  have hroot' : (∫ d, (unitCovarianceNorm n h d)^q ∂directionsLaw n h)^(1/q) ≤
      unitCovarianceMean n h * (1+q/(h : ℝ)) := by
    have hmul : q/(h : ℝ) ≤ unitCovarianceMean n h * (q/(h : ℝ)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmu) (div_nonneg hq0.le hhr.le)]
    nlinarith
  have hM := unitCovarianceNorm_rpow_integral_pos n h hn hh0 q
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hM.le _) hroot' hq0.le
  rw [one_div, Real.rpow_inv_rpow hM.le hq0.ne',
    Real.mul_rpow hmupos.le (by positivity)] at hp
  have heq : (∫ d,
      Real.exp (q*Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h) =
      (∫ d, (unitCovarianceNorm n h d)^q ∂directionsLaw n h) /
        (unitCovarianceMean n h)^q := by
    simp_rw [sphere_normalized_exp_eq_rpow n h hn hh0 q,
      Real.div_rpow (le_trans zero_le_one (one_le_unitCovarianceNorm n h hn _)) hmupos.le,
      integral_div]
  rw [heq]
  have hquot : (∫ d, (unitCovarianceNorm n h d)^q ∂directionsLaw n h) /
      (unitCovarianceMean n h)^q ≤ (1+q/(h : ℝ))^q :=
    (div_le_iff₀ (Real.rpow_pos_of_pos hmupos q)).mpr (by simpa only [mul_comm] using hp)
  have hb : 0 < 1+q/(h : ℝ) := by positivity
  simpa only [Real.rpow_def_of_pos hb, mul_comm] using hquot

/-- The actual upper exponent q=hε/5 in the nontrivial regime. -/
theorem sphere_normalized_upper_exp_epsilon (n h : ℕ) (hn : 0 < n)
    (hEntropy : SpherePowerEntropyBound n h) (e : ℝ)
    (he : 0 ≤ e) (he1 : e ≤ 1) (hlarge : 20 < (h : ℝ)*e^2) :
    (∫ d, Real.exp (((h : ℝ)*e/5)*
      Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h) ≤ Real.exp (((h : ℝ)*e/5)*Real.log (1+e/5)) := by
  have hh0 : 0 < (h : ℝ) := by
    nlinarith [sq_nonneg e, (show 0 ≤ (h : ℝ) from Nat.cast_nonneg h)]
  have hesq : e^2 ≤ e := by nlinarith
  have heprod := mul_le_mul_of_nonneg_left hesq hh0.le
  have hq : 1 ≤ (h : ℝ)*e/5 := by linarith
  have hqh : (h : ℝ)*e/5 ≤ h := by nlinarith [mul_le_mul_of_nonneg_left he1 hh0.le]
  have hh : 2 ≤ h := by
    have hs : e^2 ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs hh0.le
    have : (2 : ℝ) ≤ h := by nlinarith
    exact_mod_cast this
  have ht := sphere_normalized_upper_exp_le n h hn hh hEntropy ((h : ℝ)*e/5) hq hqh
  have hratio : ((h : ℝ)*e/5)/(h : ℝ) = e/5 := by field_simp [hh0.ne']
  simpa only [hratio] using ht

/-- The actual lower exponent t=(h−1)ε/8. -/
theorem sphere_normalized_negative_exp_epsilon (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) (e : ℝ) (he : 0 ≤ e) :
    (∫ d, Real.exp (-(((h : ℝ)-1)*e/8)*
      Real.log (unitCovarianceNorm n h d / unitCovarianceMean n h))
      ∂directionsLaw n h) ≤
        Real.exp (((((h : ℝ)-1)*e/8)*((((h : ℝ)-1)*e/8)+1))/((h : ℝ)-1)) := by
  apply sphere_normalized_negative_exp_le n h hn hh hEntropy
  have hha : 0 ≤ (h : ℝ)-1 := by exact_mod_cast (show 0 ≤ (h : ℤ)-1 by omega)
  positivity

#print axioms sphere_normalized_exp_integrable
#print axioms sphere_normalized_negative_exp_le
#print axioms sphere_normalized_upper_exp_le
#print axioms sphere_normalized_upper_exp_epsilon
#print axioms sphere_normalized_negative_exp_epsilon
end AHHRadial
