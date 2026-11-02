import CenteredDiagonalTail

open MeasureTheory GaussianTensorMoments
open scoped ENNReal
namespace GaussianEllipsoidCandidate

/-- The deterministic inverse threshold for the two-tailed quadratic gauge. -/
theorem quadratic_gauge_threshold {v D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t)
    (hv : t < min (v^2) (D*|v|)/16) :
    max (4*Real.sqrt t) (16*t/D) ≤ |v| := by
  have hmin : 16*t < min (v^2) (D*|v|) := by linarith
  have h1 := lt_of_lt_of_le hmin (min_le_left _ _)
  have h2 := lt_of_lt_of_le hmin (min_le_right _ _)
  apply max_le
  · have hs := Real.sq_sqrt ht
    have ha := sq_abs v
    have hn := abs_nonneg v
    have hsn := Real.sqrt_nonneg t
    nlinarith
  · exact (div_le_iff₀ hD).2 (by linarith)

theorem quadratic_threshold_gauge_lower {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) :
    16*t ≤ min ((max (4*Real.sqrt t) (16*t/D))^2)
      ((max (4*Real.sqrt t) (16*t/D))*D) := by
  apply le_min
  · have h := le_max_left (4*Real.sqrt t) (16*t/D)
    have hs := Real.sq_sqrt ht
    have hp : 0 ≤ 4*Real.sqrt t := by positivity
    have hsq := pow_le_pow_left₀ hp h 2
    nlinarith
  · have h := le_max_right (4*Real.sqrt t) (16*t/D)
    exact (div_le_iff₀ hD).1 h

/-- Actual Gaussian gauge tail in real measure, suited to integer moment
integration without invoking a general Hanson--Wright theorem. -/
theorem centeredDiagonal_gauge_tail {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {d t : ℝ} (hd : 0 < d)
    (hw : ∀ i, |w i| ≤ 1/Real.sqrt d) (hs : (∑ i, (w i)^2) ≤ 1) (ht : 0 ≤ t) :
    (gaussianProductLaw ι).real
      {z | t < min ((centeredDiagonal w z)^2) (Real.sqrt d * |centeredDiagonal w z|)/16} ≤
      2*Real.exp (-t) := by
  let r := max (4*Real.sqrt t) (16*t/Real.sqrt d)
  have hr : 0 ≤ r := le_trans (by positivity) (le_max_left _ _)
  have hD : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have htail := centeredDiagonal_normalized_abs_tail w hd hw hs hr
  have hsub : {z | t < min ((centeredDiagonal w z)^2)
      (Real.sqrt d * |centeredDiagonal w z|)/16} ⊆
      {z | r ≤ |centeredDiagonal w z|} := by
    intro z hz
    exact quadratic_gauge_threshold hD ht hz
  have hg := quadratic_threshold_gauge_lower hD ht
  calc
    _ ≤ (gaussianProductLaw ι).real {z | r ≤ |centeredDiagonal w z|} := measureReal_mono hsub
    _ ≤ 2*Real.exp (-min (r^2) (r*Real.sqrt d)/16) := htail
    _ ≤ 2*Real.exp (-t) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      dsimp [r]
      linarith

/-- The same exact gauge tail in ENNReal, for the existing exponential-tail
moment integrators. -/
theorem centeredDiagonal_gauge_tail_ennreal {ι : Type*} [Fintype ι]
    (w : ι → ℝ) {d t : ℝ} (hd : 0 < d)
    (hw : ∀ i, |w i| ≤ 1/Real.sqrt d) (hs : (∑ i, (w i)^2) ≤ 1) (ht : 0 ≤ t) :
    (gaussianProductLaw ι)
      {z | t < min ((centeredDiagonal w z)^2) (Real.sqrt d * |centeredDiagonal w z|)/16} ≤
      ENNReal.ofReal (2*Real.exp (-t)) := by
  have h := ENNReal.ofReal_le_ofReal (centeredDiagonal_gauge_tail w hd hw hs ht)
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

#print axioms quadratic_gauge_threshold
#print axioms quadratic_threshold_gauge_lower
#print axioms centeredDiagonal_gauge_tail
#print axioms centeredDiagonal_gauge_tail_ennreal
end GaussianEllipsoidCandidate
