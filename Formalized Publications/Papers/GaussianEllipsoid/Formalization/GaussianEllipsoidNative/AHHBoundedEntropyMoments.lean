import AHHBoundedPositiveMoments
import Mathlib.Order.Monotone.Union

/-! Consequences of a self-bounding power-entropy inequality. All calculus and
integration steps are proved here. The entropy hypothesis is visible and is
not supplied for the product-sphere covariance norm by this module. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace AHHBoundedPositiveMoments
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ)

theorem entropy_ratio_le (hX : Measurable X) {b a : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (hpos : ∀ w, 0 ≤ X w) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P X p ≤ p^2/a * mgf X P (p-1))
    {p : ℝ} (hp : p ≠ 0) :
    powerEntropy P X p / (p^2 * mgf X P p) ≤ 1/a := by
  have hM := mgf_pos P X hX hbound p
  have hpp : 0 < p^2 := sq_pos_of_ne_zero hp
  apply (div_le_iff₀ (mul_pos hpp hM)).mpr
  calc
    powerEntropy P X p ≤ p^2/a * mgf X P (p-1) := hEnt p
    _ ≤ p^2/a * mgf X P p := mul_le_mul_of_nonneg_left
      (mgf_previous_le P X hX hbound hpos p) (by positivity)
    _ = _ := by ring

theorem adjusted_logMean_antitone (hX : Measurable X) {b a : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (hpos : ∀ w, 0 ≤ X w) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P X p ≤ p^2/a * mgf X P (p-1)) :
    Antitone (fun p => logMean P X p - p/a) := by
  have hc : Continuous (fun p => logMean P X p - p/a) :=
    (continuous_logMean P X hX hbound).sub (continuous_id.div_const a)
  have hd (p : ℝ) (hp : p ≠ 0) :
      HasDerivAt (fun q => logMean P X q - q/a)
        (powerEntropy P X p / (p^2 * mgf X P p) - 1/a) p :=
    (hasDerivAt_logMean P X hX hbound hp).sub ((hasDerivAt_id p).div_const a)
  have hb (p : ℝ) (hp : p ≠ 0) :
      powerEntropy P X p / (p^2 * mgf X P p) - 1/a ≤ 0 :=
    sub_nonpos.mpr (entropy_ratio_le P X hX hbound hpos ha hEnt hp)
  have hleft : AntitoneOn (fun p => logMean P X p - p/a) (Iic 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic _) hc.continuousOn
      (f' := fun p => powerEntropy P X p / (p^2 * mgf X P p) - 1/a)
    · intro p hp
      have hp' : p < 0 := by simpa using hp
      exact (hd p (ne_of_lt hp')).hasDerivWithinAt
    · intro p hp
      have hp' : p < 0 := by simpa using hp
      exact hb p (ne_of_lt hp')
  have hright : AntitoneOn (fun p => logMean P X p - p/a) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _) hc.continuousOn
      (f' := fun p => powerEntropy P X p / (p^2 * mgf X P p) - 1/a)
    · intro p hp
      have hp' : 0 < p := by simpa using hp
      exact (hd p (ne_of_gt hp')).hasDerivWithinAt
    · intro p hp
      have hp' : 0 < p := by simpa using hp
      exact hb p (ne_of_gt hp')
  exact hleft.Iic_union_Ici hright

/-- Negative normalized logarithmic moments, including exponent zero. -/
theorem negative_cgf_le (hX : Measurable X) {b a : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (hpos : ∀ w, 0 ≤ X w) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P X p ≤ p^2/a * mgf X P (p-1))
    {t : ℝ} (ht : 0 ≤ t) :
    cgf X P (-t) + t * cgf X P 1 ≤ t*(t+1)/a := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    simp
  have h := adjusted_logMean_antitone P X hX hbound hpos ha hEnt
    (show -t ≤ 1 by linarith)
  dsimp only at h
  rw [logMean_eq_div P X one_ne_zero, logMean_eq_div P X (neg_ne_zero.mpr htpos.ne')] at h
  simp only [div_one] at h
  have hm := mul_le_mul_of_nonneg_left h ht
  field_simp [htpos.ne', ha.ne'] at hm ⊢
  nlinarith

theorem root_mgf_times_previous_le (hX : Measurable X) {b : ℝ}
    (hbound : ∀ w, |X w| ≤ b) {p : ℝ} (hp : 1 ≤ p) :
    Real.exp (logMean P X p) * mgf X P (p-1) ≤ mgf X P p := by
  have hp0 : p ≠ 0 := by linarith
  calc
    Real.exp (logMean P X p) * mgf X P (p-1) ≤
        Real.exp (logMean P X p) * Real.exp (((p-1)/p)*cgf X P p) :=
      mul_le_mul_of_nonneg_left (mgf_previous_le_exp P X hX hbound hp)
        (Real.exp_pos _).le
    _ = Real.exp (cgf X P p) := by
      rw [← Real.exp_add, logMean_eq_div P X hp0]
      congr 1
      field_simp
      <;> ring
    _ = mgf X P p := Real.exp_log (mgf_pos P X hX hbound p)

theorem root_mgf_derivative_le (hX : Measurable X) {b a : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P X p ≤ p^2/a * mgf X P (p-1))
    {p : ℝ} (hp : 1 ≤ p) :
    Real.exp (logMean P X p) *
      (powerEntropy P X p / (p^2 * mgf X P p)) ≤ 1/a := by
  have hp0 : 0 < p := by linarith
  have hM := mgf_pos P X hX hbound p
  have hE := Real.exp_pos (logMean P X p)
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hp0) hM)).mpr
  calc
    Real.exp (logMean P X p) * powerEntropy P X p ≤
        Real.exp (logMean P X p) * (p^2/a * mgf X P (p-1)) :=
      mul_le_mul_of_nonneg_left (hEnt p) hE.le
    _ = p^2/a * (Real.exp (logMean P X p) * mgf X P (p-1)) := by ring
    _ ≤ p^2/a * mgf X P p := mul_le_mul_of_nonneg_left
      (root_mgf_times_previous_le P X hX hbound hp) (by positivity)
    _ = _ := by ring

/-- Positive power-mean growth with the sharp self-bounding constant. -/
theorem root_mgf_le (hX : Measurable X) {b a : ℝ}
    (hbound : ∀ w, |X w| ≤ b) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P X p ≤ p^2/a * mgf X P (p-1))
    {q : ℝ} (hq : 1 ≤ q) :
    Real.exp (cgf X P q / q) ≤ mgf X P 1 + (q-1)/a := by
  have hc : Continuous (fun p => Real.exp (logMean P X p) - p/a) :=
    (Real.continuous_exp.comp (continuous_logMean P X hX hbound)).sub (continuous_id.div_const a)
  have hm : AntitoneOn (fun p => Real.exp (logMean P X p) - p/a) (Ici 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _) hc.continuousOn
      (f' := fun p => Real.exp (logMean P X p) *
        (powerEntropy P X p / (p^2 * mgf X P p)) - 1/a)
    · intro p hp
      have hp1 : 1 < p := by simpa using hp
      exact ((hasDerivAt_logMean P X hX hbound (by linarith)).exp.sub
        ((hasDerivAt_id p).div_const a)).hasDerivWithinAt
    · intro p hp
      have hp1 : 1 < p := by simpa using hp
      exact sub_nonpos.mpr (root_mgf_derivative_le P X hX hbound ha hEnt hp1.le)
  have hh := hm (show (1 : ℝ) ∈ Ici 1 by simp) hq hq
  dsimp only at hh
  rw [logMean_eq_div P X one_ne_zero, logMean_eq_div P X (by linarith)] at hh
  simp only [div_one] at hh
  rw [show Real.exp (cgf X P 1) = mgf X P 1 from
    Real.exp_log (mgf_pos P X hX hbound 1)] at hh
  rw [sub_div]
  linarith

#print axioms negative_cgf_le
#print axioms root_mgf_le
end AHHBoundedPositiveMoments
