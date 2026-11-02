import AHHSphereObservableBounds
import AHHAEMomentCorollaries

/-! Exact remaining analytic obligation for the actual product-sphere law.

`SpherePowerEntropyBound` is a proposition, not a theorem or axiom. This file
proves the implication from that explicitly named analytic obligation to both
moment estimates. It also proves all observable/mean bounds unconditionally
and discharges the one-sample case. The general sphere entropy inequality,
including its locally Lipschitz/Sobolev justification, remains unproved.
-/
noncomputable section
open MeasureTheory ProbabilityTheory AHHBoundedPositiveMoments
namespace AHHRadial

def unitCovarianceMean (n h : ℕ) : ℝ :=
  ∫ d, unitCovarianceNorm n h d ∂directionsLaw n h

theorem one_le_unitCovarianceMean (n h : ℕ) (hn : 0 < n) (hh : 0 < h) :
    1 ≤ unitCovarianceMean n h := by
  letI := directionsLaw_probability n h hh
  have hm := integral_mono (integrable_const (1 : ℝ))
    (unitCovarianceNorm_integrable n h hh) (one_le_unitCovarianceNorm n h hn)
  simpa only [integral_const, probReal_univ, one_smul, unitCovarianceMean] using hm

theorem unitCovarianceMean_le (n h : ℕ) (hh : 0 < h) :
    unitCovarianceMean n h ≤ n := by
  letI := directionsLaw_probability n h hh
  have hm := integral_mono (unitCovarianceNorm_integrable n h hh)
    (integrable_const (n : ℝ)) (unitCovarianceNorm_le n h)
  simpa only [integral_const, probReal_univ, one_smul, unitCovarianceMean] using hm

/-- All real powers of the actual observable are integrable; no entropy input. -/
theorem unitCovarianceNorm_rpow_integrable (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (p : ℝ) : Integrable (fun d => (unitCovarianceNorm n h d)^p) (directionsLaw n h) := by
  letI := directionsLaw_probability n h hh
  have hlog := (continuous_unitCovarianceNorm n h).measurable.log
  have hb := log_bounded (unitCovarianceNorm n h)
    (one_le_unitCovarianceNorm n h hn) (unitCovarianceNorm_le n h)
  have hi := integrable_exp_of_bounded (directionsLaw n h)
    (fun d => Real.log (unitCovarianceNorm n h d)) hlog hb p
  apply hi.congr
  exact ae_of_all _ fun d => by
    dsimp only
    rw [Real.rpow_def_of_pos (by linarith [one_le_unitCovarianceNorm n h hn d])]
    congr 1
    ring

theorem unitCovarianceNorm_rpow_integral_pos (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (p : ℝ) : 0 < ∫ d, (unitCovarianceNorm n h d)^p ∂directionsLaw n h := by
  letI := directionsLaw_probability n h hh
  have hlog := (continuous_unitCovarianceNorm n h).measurable.log
  have hb := log_bounded (unitCovarianceNorm n h)
    (one_le_unitCovarianceNorm n h hn) (unitCovarianceNorm_le n h)
  rw [← mgf_log_eq_rpow_integral (directionsLaw n h) (unitCovarianceNorm n h)
    (fun d => by linarith [one_le_unitCovarianceNorm n h hn d])]
  exact mgf_pos _ _ hlog hb p

theorem normalized_unitCovarianceNorm_rpow_integrable (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (p : ℝ) :
    Integrable (fun d => (unitCovarianceNorm n h d / unitCovarianceMean n h)^p)
      (directionsLaw n h) := by
  have hmean : 0 ≤ unitCovarianceMean n h := le_trans zero_le_one
    (one_le_unitCovarianceMean n h hn hh)
  have heq (d : Directions n h) :
      (unitCovarianceNorm n h d / unitCovarianceMean n h)^p =
      (unitCovarianceNorm n h d)^p / (unitCovarianceMean n h)^p :=
    Real.div_rpow (le_trans zero_le_one (one_le_unitCovarianceNorm n h hn d)) hmean p
  simp_rw [heq]
  exact (unitCovarianceNorm_rpow_integrable n h hn hh p).div_const _

/-- The sole remaining analytic hypothesis in the sphere moment reduction.
Here the law, the operator norm, and all real exponents are concrete. -/
def SpherePowerEntropyBound (n h : ℕ) : Prop :=
  ∀ p : ℝ, powerEntropy (directionsLaw n h)
      (fun d => Real.log (unitCovarianceNorm n h d)) p ≤
    p^2 / ((h : ℝ)-1) *
      (∫ d, (unitCovarianceNorm n h d)^(p-1) ∂directionsLaw n h)

/-- Conditional reduction only; this is not an unconditional sphere theorem. -/
theorem sphere_moments_of_powerEntropy (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h)
    (hEntropy : SpherePowerEntropyBound n h) :
    (∀ q : ℝ, 1 ≤ q →
      (∫ d, (unitCovarianceNorm n h d)^q ∂directionsLaw n h)^(1/q) ≤
        unitCovarianceMean n h + (q-1)/((h : ℝ)-1)) ∧
    (∀ t : ℝ, 0 ≤ t →
      Real.log (∫ d, (unitCovarianceNorm n h d / unitCovarianceMean n h)^(-t)
        ∂directionsLaw n h) ≤ t*(t+1)/((h : ℝ)-1)) := by
  letI := directionsLaw_probability n h (by omega)
  have ha : 0 < (h : ℝ)-1 := by exact_mod_cast (show 0 < (h : ℤ)-1 by omega)
  constructor
  · intro q hq
    exact positive_moment_le (directionsLaw n h) (unitCovarianceNorm n h)
      (continuous_unitCovarianceNorm n h).measurable
      (one_le_unitCovarianceNorm n h hn) (unitCovarianceNorm_le n h) ha hEntropy hq
  · intro t ht
    exact negative_moment_le (directionsLaw n h) (unitCovarianceNorm n h)
      (continuous_unitCovarianceNorm n h).measurable
      (one_le_unitCovarianceNorm n h hn) (unitCovarianceNorm_le n h) ha hEntropy ht

@[simp] theorem unitCovarianceNorm_one_sample (h : ℕ) (d : Directions 1 h) :
    unitCovarianceNorm 1 h d = 1 :=
  le_antisymm (by simpa only [Nat.cast_one] using unitCovarianceNorm_le 1 h d)
    (one_le_unitCovarianceNorm 1 h (by decide) d)

/-- A genuinely unconditional analytic input for the one-sample subcase. -/
theorem spherePowerEntropyBound_one_sample (h : ℕ) (hh : 2 ≤ h) :
    SpherePowerEntropyBound 1 h := by
  letI := directionsLaw_probability 1 h (by omega)
  have ha : 0 ≤ (h : ℝ)-1 := by exact_mod_cast (show 0 ≤ (h : ℤ)-1 by omega)
  intro p
  simp only [unitCovarianceNorm_one_sample, Real.log_one, powerEntropy,
    mul_zero, zero_mul, integral_zero, mgf, Real.exp_zero, integral_const,
    probReal_univ, one_smul, Real.one_rpow, sub_zero, mul_one, one_mul, Real.log_one]
  positivity

#print axioms unitCovarianceNorm_rpow_integrable
#print axioms unitCovarianceNorm_rpow_integral_pos
#print axioms normalized_unitCovarianceNorm_rpow_integrable
#print axioms one_le_unitCovarianceMean
#print axioms unitCovarianceMean_le
#print axioms sphere_moments_of_powerEntropy
#print axioms spherePowerEntropyBound_one_sample
end AHHRadial
