import AHHExactEquation11EntropyEndpoint

/-! Parameter closure for the actual AHH equation (11), k=2.

The zero-sample, small-parameter, one-dimensional, and one-sample cases below
are unconditional. The final paper-facing endpoint requires the concrete
sphere power-entropy inequality only when both n and h are at least two.
It does not prove that remaining analytic inequality. No frozen predecessor
is changed, and no new analytic estimate is introduced here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges AHHGaussian
namespace AHHRadial

/-- Empty samples give the empty inclusive deviation event when Δ is positive.
This endpoint does not require a positive dimension or any entropy premise. -/
theorem actual_equation11_zero_samples (h : ℕ) (s t : Bool)
    (e Δ : ℝ) (hΔ : 0 < Δ) :
    (fourGaussianLaw 0 h).real {x | e*unitCovarianceMean 0 h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance 0 h s t x)‖-unitCovarianceMean 0 h|} ≤
        4*0*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  have hμ : unitCovarianceMean 0 h = 0 := by
    simp [unitCovarianceMean]
  have hz (x : FourEntries 0 h) : actualComplexCovariance 0 h s t x = 0 := by
    simp [actualComplexCovariance, complexCov]
  have hevent : {x : FourEntries 0 h | e*unitCovarianceMean 0 h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance 0 h s t x)‖-unitCovarianceMean 0 h|} = ∅ := by
    ext x
    simp [hμ, hz, not_le.mpr hΔ, cMatrixCLM]
  rw [hevent, measureReal_empty]
  positivity

/-- The existing tail assembly already proves the small regime without sphere
entropy: both large-regime callbacks have contradictory assumptions. -/
theorem polar_relative_deviation_small_regime (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (e : ℝ) (he : 0 < e) (he1 : e ≤ 1)
    (hsmall : (h : ℝ)*e^2 ≤ 20) :
    (polarLaw n h).real {w | e*unitCovarianceMean n h ≤
      |polarCovarianceNorm n h w-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) := by
  let := polarLaw_probability n h hh
  have hμ : 0 < unitCovarianceMean n h :=
    lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceMean n h hn hh)
  apply AHHExactEquation11.relative_deviation_from_tails (polarLaw n h) n hn
    (polarCovarianceNorm n h) (unitCovarianceMean n h) h e hμ he he1
    (polarCovarianceNorm_pos n h hn)
  · intro hlarge
    exact False.elim ((not_lt_of_ge hsmall) hlarge)
  · intro hlarge _
    exact False.elim ((not_lt_of_ge hsmall) hlarge)

/-- Entropy-free small-regime relative bound for the actual four-Gaussian law. -/
theorem actual_relative_deviation_small_regime (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (s t : Bool)
    (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hsmall : (h : ℝ)*e^2 ≤ 20) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) := by
  rw [actual_polar_deviation_probability_eq n h hh s t]
  exact polar_relative_deviation_small_regime n h hn hh e he he1 hsmall

/-- Exact equation (11) without entropy throughout the small-parameter regime. -/
theorem actual_equation11_small_regime (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h) (s t : Bool)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ)
    (hsmall : (h : ℝ)*e^2 ≤ 20) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  exact AHHExactEquation11.additive_threshold_bound (fourGaussianLaw n h)
    (fun x => ‖cMatrixCLM (actualComplexCovariance n h s t x)‖) n
    (unitCovarianceMean n h) h e Δ hΔ.le
    (actual_relative_deviation_small_regime n h hn hh s t e he he1 hsmall)

/-- Every admissible epsilon lies in the small regime when h=1. -/
theorem actual_equation11_one_dimension (n : ℕ) (s t : Bool)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n 1).real {x | e*unitCovarianceMean n 1+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance n 1 s t x)‖-unitCovarianceMean n 1|} ≤
        4*n*Real.exp (-(1 : ℝ)*e^2/16) +
          2*Real.exp (-((1 : ℝ)-1)*Δ^2/8) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa only [Nat.cast_zero, Nat.cast_one] using
      actual_equation11_zero_samples 1 s t e Δ hΔ
  · have hsmall : (1 : ℝ)*e^2 ≤ 20 := by nlinarith
    simpa only [Nat.cast_one] using
      actual_equation11_small_regime n 1 hn (by decide) s t e Δ he he1 hΔ
        (by simpa only [Nat.cast_one] using hsmall)

/-- The one-sample case uses its already proved sphere entropy bound for h≥2,
and the unconditional small regime for h=1. -/
theorem actual_equation11_one_sample (h : ℕ) (hh : 0 < h) (s t : Bool)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw 1 h).real {x | e*unitCovarianceMean 1 h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance 1 h s t x)‖-unitCovarianceMean 1 h|} ≤
        4*1*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  by_cases hh1 : h = 1
  · subst h
    simpa only [Nat.cast_one] using
      actual_equation11_one_dimension 1 s t e Δ he he1 hΔ
  · simpa only [Nat.cast_one] using actual_equation11_of_powerEntropy 1 h hh
      (spherePowerEntropyBound_one_sample h (by omega)) s t e Δ he he1 hΔ

/-- At fixed n,h the only potentially needed analytic premise is restricted
to the genuinely unresolved range n≥2 and h≥2. -/
theorem actual_equation11_of_large_parameters_powerEntropy (n h : ℕ)
    (hh : 0 < h)
    (hEntropy : 2 ≤ n → 2 ≤ h → SpherePowerEntropyBound n h)
    (s t : Bool) (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  by_cases hn0 : n = 0
  · subst n
    simpa only [Nat.cast_zero] using actual_equation11_zero_samples h s t e Δ hΔ
  by_cases hn1 : n = 1
  · subst n
    simpa only [Nat.cast_one] using actual_equation11_one_sample h hh s t e Δ he he1 hΔ
  by_cases hh1 : h = 1
  · subst h
    simpa only [Nat.cast_one] using actual_equation11_one_dimension n s t e Δ he he1 hΔ
  exact actual_equation11_of_powerEntropy n h hh
    (hEntropy (by omega) (by omega)) s t e Δ he he1 hΔ

/-- Source-facing real signs ±1: the empty-sample case is unconditional. -/
theorem paper_equation11_zero_samples (h : ℕ)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (hΔ : 0 < Δ) :
    (fourGaussianLaw 0 h).real {x | e*unitCovarianceMean 0 h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance 0 h s t x)‖-unitCovarianceMean 0 h|} ≤
        4*0*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact actual_equation11_zero_samples h b c e Δ hΔ

/-- Source-facing small-regime equation (11), with inclusive event and exact
constants 16 and 8, independent of the remaining entropy obligation. -/
theorem paper_equation11_small_regime (n h : ℕ)
    (hn : 0 < n) (hh : 0 < h)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ)
    (hsmall : (h : ℝ)*e^2 ≤ 20) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact actual_equation11_small_regime n h hn hh b c e Δ he he1 hΔ hsmall

/-- Unconditional source-facing equation (11) for h=1 and every sample count. -/
theorem paper_equation11_one_dimension (n : ℕ)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n 1).real {x | e*unitCovarianceMean n 1+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance n 1 s t x)‖-unitCovarianceMean n 1|} ≤
        4*n*Real.exp (-(1 : ℝ)*e^2/16) +
          2*Real.exp (-((1 : ℝ)-1)*Δ^2/8) := by
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact actual_equation11_one_dimension n b c e Δ he he1 hΔ

/-- Unconditional source-facing equation (11) for n=1 and every h≥1. -/
theorem paper_equation11_one_sample (h : ℕ) (hh : 0 < h)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw 1 h).real {x | e*unitCovarianceMean 1 h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance 1 h s t x)‖-unitCovarianceMean 1 h|} ≤
        4*1*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact actual_equation11_one_sample h hh b c e Δ he he1 hΔ

/-- Exact paper-facing equation (11). Its sole analytic premise is required
only for n≥2 and h≥2; all excluded parameter cases are proved above. -/
theorem paper_equation11_of_large_parameters_powerEntropy (n h : ℕ)
    (hh : 0 < h)
    (hEntropy : 2 ≤ n → 2 ≤ h → SpherePowerEntropyBound n h)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  obtain ⟨b, rfl⟩ := exists_bool_sign s hs
  obtain ⟨c, rfl⟩ := exists_bool_sign t ht
  simp_rw [paperComplexCovariance_eq_actual]
  exact actual_equation11_of_large_parameters_powerEntropy n h hh hEntropy b c e Δ he he1 hΔ

/-- A single family on n≥2,h≥2 suffices for the complete paper-facing parameter
range. The family is an explicit hypothesis, not an axiom or instance. -/
theorem paper_equation11_of_powerEntropy_family
    (hEntropy : ∀ n h : ℕ, 2 ≤ n → 2 ≤ h → SpherePowerEntropyBound n h)
    (n h : ℕ) (hh : 0 < h)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) := by
  exact paper_equation11_of_large_parameters_powerEntropy n h hh (hEntropy n h)
    s t hs ht e Δ he he1 hΔ

#print axioms actual_equation11_zero_samples
#print axioms polar_relative_deviation_small_regime
#print axioms actual_relative_deviation_small_regime
#print axioms actual_equation11_small_regime
#print axioms actual_equation11_one_dimension
#print axioms actual_equation11_one_sample
#print axioms actual_equation11_of_large_parameters_powerEntropy
#print axioms paper_equation11_zero_samples
#print axioms paper_equation11_small_regime
#print axioms paper_equation11_one_dimension
#print axioms paper_equation11_one_sample
#print axioms paper_equation11_of_large_parameters_powerEntropy
#print axioms paper_equation11_of_powerEntropy_family
end AHHRadial
