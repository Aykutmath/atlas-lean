import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! Closed moment calculus for a bounded positive observable. The entropy
inequality used at the end is an explicit hypothesis, not an axiom and not a
proved product-sphere log-Sobolev theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace AHHBoundedPositiveMoments
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ)

/-- Entropy of the positive random variable `exp (p X)`. -/
def powerEntropy (p : ℝ) : ℝ :=
  p * (∫ w, X w * Real.exp (p * X w) ∂P) -
    mgf X P p * Real.log (mgf X P p)

/-- Logarithm of the generalized power mean, continuously extended at zero. -/
def logMean : ℝ → ℝ := dslope (cgf X P) 0

theorem integrable_exp_of_bounded (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (p : ℝ) :
    Integrable (fun w => Real.exp (p * X w)) P := by
  apply (integrable_const (Real.exp (|p| * b))).mono'
    (hX.const_mul p |>.exp.aestronglyMeasurable)
  exact ae_of_all _ fun w => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; gcongr; exact hbound w)

theorem integrableExpSet_eq_univ (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) : integrableExpSet X P = univ := by
  ext p
  simp only [mem_univ, iff_true]
  exact integrable_exp_of_bounded P X hX hbound p

theorem mgf_pos (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (p : ℝ) : 0 < mgf X P p := by
  exact ProbabilityTheory.mgf_pos (integrable_exp_of_bounded P X hX hbound p)

theorem hasDerivAt_mgf_all (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (p : ℝ) :
    HasDerivAt (mgf X P) (∫ w, X w * Real.exp (p * X w) ∂P) p := by
  apply hasDerivAt_mgf
  simp [integrableExpSet_eq_univ P X hX hbound]

theorem hasDerivAt_cgf_all (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (p : ℝ) :
    HasDerivAt (cgf X P)
      ((∫ w, X w * Real.exp (p * X w) ∂P) / mgf X P p) p := by
  exact (hasDerivAt_mgf_all P X hX hbound p).log (mgf_pos P X hX hbound p).ne'

@[simp] theorem cgf_zero : cgf X P 0 = 0 := by simp [cgf, mgf]

theorem logMean_eq_div {p : ℝ} (hp : p ≠ 0) :
    logMean P X p = cgf X P p / p := by
  simp [logMean, dslope_of_ne _ hp, slope, cgf_zero, div_eq_mul_inv, mul_comm]

theorem continuous_logMean (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) : Continuous (logMean P X) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = 0
  · subst p
    exact continuousAt_dslope_same.mpr (hasDerivAt_cgf_all P X hX hbound 0).differentiableAt
  · exact (continuousAt_dslope_of_ne hp).mpr
      (hasDerivAt_cgf_all P X hX hbound p).continuousAt

theorem hasDerivAt_logMean (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (logMean P X) (powerEntropy P X p / (p^2 * mgf X P p)) p := by
  have h := (hasDerivAt_cgf_all P X hX hbound p).div (hasDerivAt_id p) hp
  have heq : logMean P X =ᶠ[𝓝 p] fun q => cgf X P q / q := by
    filter_upwards [eventually_ne_nhds hp] with q hq
    exact logMean_eq_div P X hq
  have he : powerEntropy P X p / (p^2 * mgf X P p) =
      (((∫ w, X w * Real.exp (p * X w) ∂P) / mgf X P p) * p - cgf X P p) / p^2 := by
    dsimp [powerEntropy, cgf]
    field_simp [(mgf_pos P X hX hbound p).ne', hp]
    <;> ring
  rw [he]
  simpa only [id_eq, mul_one] using h.congr_of_eventuallyEq heq

theorem mgf_previous_le (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (hpos : ∀ w, 0 ≤ X w) (p : ℝ) :
    mgf X P (p-1) ≤ mgf X P p := by
  apply integral_mono (integrable_exp_of_bounded P X hX hbound (p-1))
    (integrable_exp_of_bounded P X hX hbound p)
  intro w
  apply Real.exp_le_exp.mpr
  nlinarith [hpos w]

/-- The Hölder comparison needed to bound the derivative of a power mean. -/
theorem mgf_previous_le_exp (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) {p : ℝ} (hp : 1 ≤ p) :
    mgf X P (p-1) ≤ Real.exp (((p-1)/p) * cgf X P p) := by
  have hp0 : 0 < p := by linarith
  let r := (p-1)/p
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hp0.le
  have hr1 : r ≤ 1 := (div_le_one hp0).mpr (by linarith)
  have heq (w : Ω) : (Real.exp (p*X w)) ^ r = Real.exp ((p-1)*X w) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    dsimp [r]
    field_simp
    <;> ring
  have hi : Integrable ((fun z : ℝ => z ^ r) ∘ fun w => Real.exp (p*X w)) P := by
    simpa only [Function.comp_def, heq] using
      integrable_exp_of_bounded P X hX hbound (p-1)
  have hj := (Real.concaveOn_rpow hr0 hr1).le_map_integral
    (Real.continuous_rpow_const hr0).continuousOn isClosed_Ici
    (ae_of_all P fun w => (Real.exp_pos (p*X w)).le)
    (integrable_exp_of_bounded P X hX hbound p) hi
  simp only [heq] at hj
  change mgf X P (p-1) ≤ (mgf X P p)^r at hj
  rw [Real.rpow_def_of_pos (mgf_pos P X hX hbound p)] at hj
  simpa [r, cgf, mul_comm] using hj

#print axioms hasDerivAt_logMean
#print axioms mgf_previous_le_exp
end AHHBoundedPositiveMoments
