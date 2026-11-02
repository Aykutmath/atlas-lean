import AHHActualJointMoments
import AHHExactEquation11Finish

/-! AHH equation (11), k=2, for the actual independent real Gaussian ensemble,
conditional only on the explicitly named concrete sphere power-entropy bound.

This file does NOT prove that analytic sphere inequality. In particular this
conditional endpoint is not an unconditional closure of the manuscript row. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges AHHGaussian
namespace AHHRadial

/-- Stronger relative-deviation estimate on the concrete polar product model.
The requirement n>0 is necessary for this relative-only statement. -/
theorem polar_relative_deviation_of_powerEntropy (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (hEntropy : SpherePowerEntropyBound n h)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (polarLaw n h).real {w | e*unitCovarianceMean n h ≤
      |polarCovarianceNorm n h w-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) := by
  letI := polarLaw_probability n h hh
  have hμ : 0 < unitCovarianceMean n h :=
    lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceMean n h hn hh)
  apply AHHExactEquation11.relative_deviation_from_tails (polarLaw n h) n hn
    (polarCovarianceNorm n h) (unitCovarianceMean n h) h e hμ he he1
    (polarCovarianceNorm_pos n h hn)
  · intro hlarge
    apply AHHExactEquation11.upper_tail_from_joint_moments (polarLaw n h) n
      (polarLog n h) (fun w => polarCovarianceNorm n h w / unitCovarianceMean n h)
      h e (Nat.cast_nonneg h) he.le he1
    · intro w hw
      exact polar_upper_log_select n h hn hh (1+e) (by linarith) w hw
    · intro i
      exact polarLog_exp_integrable n h hn hh i _ (by positivity)
    · exact polarLog_upper_epsilon_moment n h hn hEntropy e he.le he1 hlarge
  · intro hlarge he1'
    obtain ⟨hh2, hq, hqh⟩ := large_regime_parameters h e he.le he1 hlarge
    have hhR : (1 : ℝ) < h := by exact_mod_cast hh2
    apply AHHExactEquation11.lower_tail_from_joint_moments (polarLaw n h) n
      (polarLog n h) (fun w => polarCovarianceNorm n h w / unitCovarianceMean n h)
      h e hhR he.le he1' hlarge
    · intro w hw
      exact polar_lower_log_select n h hn hh (1-e) w hw
    · intro i
      apply polarLog_exp_integrable n h hn hh i
      have hm := mul_le_mul_of_nonneg_left he1 (show 0 ≤ (h : ℝ)-1 by linarith)
      nlinarith
    · exact polarLog_lower_epsilon_moment n h hn hh2 hEntropy e he.le he1

/-- Exact distributional receipt for inclusive deviations: both sides push
forward to the same actual normalized complex Gaussian sample law. -/
theorem actual_polar_deviation_probability_eq (n h : ℕ) (hh : 0 < h)
    (s t : Bool) (μ a : ℝ) :
    (fourGaussianLaw n h).real {x | a ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-μ|} =
    (polarLaw n h).real {w | a ≤ |polarCovarianceNorm n h w-μ|} := by
  let S : Set (Fin n → CE h × CE h) :=
    {z | a ≤ |‖gaussianCovariance n h z‖-μ|}
  have hS : MeasurableSet S := by
    apply measurableSet_le measurable_const
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (((continuous_gaussianCovariance n h).norm.sub continuous_const).norm.measurable)
  have hA := map_measureReal_apply (μ := fourGaussianLaw n h)
    (actualNormalizedPairs_preserving n h hh s t).measurable hS
  have hP := map_measureReal_apply (μ := (radiiLaw n h).prod (directionsLaw n h))
    (assembleSample_preserving n h hh).measurable hS
  rw [(actualNormalizedPairs_preserving n h hh s t).map_eq] at hA
  rw [(assembleSample_preserving n h hh).map_eq] at hP
  simpa only [S, Set.preimage_setOf_eq, gaussianCovariance_actual_eq,
    polarLaw, polarCovarianceNorm] using hA.symm.trans hP

/-- Actual four-independent-real Gaussian ensemble, fixed Boolean sign pair.
Only `SpherePowerEntropyBound n h` remains as an analytic premise. -/
theorem actual_relative_deviation_of_powerEntropy (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (hEntropy : SpherePowerEntropyBound n h)
    (s t : Bool) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) := by
  rw [actual_polar_deviation_probability_eq n h hh s t]
  exact polar_relative_deviation_of_powerEntropy n h hn hh hEntropy e he he1

/-- Exact requested AHH (11), with the literal independent Gaussian law,
Haar unit-vector mean, original constants, and inclusive deviation event.
This is conditional on the concrete sphere entropy inequality, not a proof of it.
The empty sample case is included because Δ is strictly positive. -/
theorem actual_equation11_of_powerEntropy (n h : ℕ)
    (hh : 0 < h) (hEntropy : SpherePowerEntropyBound n h)
    (s t : Bool) (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hμ : unitCovarianceMean 0 h = 0 := by
      simp [unitCovarianceMean]
    have hz (x : FourEntries 0 h) : actualComplexCovariance 0 h s t x = 0 := by
      simp [actualComplexCovariance, complexCov]
    have hevent : {x : FourEntries 0 h | e*unitCovarianceMean 0 h+Δ ≤
        |‖cMatrixCLM (actualComplexCovariance 0 h s t x)‖-unitCovarianceMean 0 h|} = ∅ := by
      ext x
      simp [hμ, hz, not_le.mpr hΔ, cMatrixCLM]
    rw [hevent, measureReal_empty]
    positivity
  · exact AHHExactEquation11.additive_threshold_bound (fourGaussianLaw n h)
      (fun x => ‖cMatrixCLM (actualComplexCovariance n h s t x)‖) n
      (unitCovarianceMean n h) h e Δ hΔ.le
      (actual_relative_deviation_of_powerEntropy n h hn hh hEntropy s t e he he1)

/-- Source-facing real signs ±1, with the literal product-state denominator 2h.
No entropy bound, gradient statement, or concentration estimate is hidden in
an instance or an opaque axiom: the single analytic premise is explicit. -/
theorem paper_equation11_of_powerEntropy (n h : ℕ)
    (hh : 0 < h) (hEntropy : SpherePowerEntropyBound n h)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact actual_equation11_of_powerEntropy n h hh hEntropy b c e Δ he he1 hΔ

#print axioms polar_relative_deviation_of_powerEntropy
#print axioms actual_polar_deviation_probability_eq
#print axioms actual_relative_deviation_of_powerEntropy
#print axioms actual_equation11_of_powerEntropy
#print axioms paper_equation11_of_powerEntropy
end AHHRadial
