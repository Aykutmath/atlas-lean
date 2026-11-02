import AHHExactEquation11Scalars
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Conditional probabilistic assembly for the new k=2 argument.
The sphere/Gamma moment estimates and the radial-angular representation are
explicit hypotheses. This module is NOT an unconditional theorem about AHH
random matrices. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace AHHExactEquation11

theorem exponential_markov
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (q T B : ℝ) (hq : 0 ≤ q)
    (hInt : Integrable (fun w => Real.exp (q*X w)) P)
    (hMoment : (∫ w, Real.exp (q*X w) ∂P) ≤ Real.exp B) :
    P.real {w | T ≤ X w} ≤ Real.exp (B-q*T) := by
  have hsub : {w | T ≤ X w} ⊆ {w | Real.exp (q*T) ≤ Real.exp (q*X w)} := by
    intro w hw
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hq)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun w => Real.exp (q*X w))
    (Filter.Eventually.of_forall (fun w => (Real.exp_pos _).le)) hInt (Real.exp (q*T))
  have hm' : Real.exp (q*T) * P.real {w | T ≤ X w} ≤ Real.exp B :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le).trans
      (hm.trans hMoment)
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm] using hm'

theorem finite_exponential_markov
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (X : Fin N → Ω → ℝ) (q T B : ℝ) (hq : 0 ≤ q)
    (hInt : ∀ s, Integrable (fun w => Real.exp (q*X s w)) P)
    (hMoment : ∀ s, (∫ w, Real.exp (q*X s w) ∂P) ≤ Real.exp B) :
    P.real {w | ∃ s, T ≤ X s w} ≤ N*Real.exp (B-q*T) := by
  have heq : {w | ∃ s, T ≤ X s w} = ⋃ s, {w | T ≤ X s w} := by ext w; simp
  rw [heq]
  calc
    P.real (⋃ s, {w | T ≤ X s w}) ≤ ∑ s, P.real {w | T ≤ X s w} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _s : Fin N, Real.exp (B-q*T) :=
      Finset.sum_le_sum (fun s _ => exponential_markov P (X s) q T B hq (hInt s) (hMoment s))
    _ = N*Real.exp (B-q*T) := by simp

/-- Upper-tail assembly from the explicit joint logarithmic moment estimate. -/
theorem upper_tail_from_joint_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (X : Fin N → Ω → ℝ) (Y : Ω → ℝ) (h e : ℝ)
    (hh : 0 ≤ h) (he : 0 ≤ e) (he1 : e ≤ 1)
    (hSelect : ∀ w, 1+e ≤ Y w → ∃ s, Real.log (1+e) ≤ X s w)
    (hInt : ∀ s, Integrable (fun w => Real.exp ((h*e/5)*X s w)) P)
    (hMoment : ∀ s, (∫ w, Real.exp ((h*e/5)*X s w) ∂P) ≤
      Real.exp (h*((2+3*e/5)*Real.log (1+e/5)-2*e/5))) :
    P.real {w | 1+e ≤ Y w} ≤ N*Real.exp (-h*e^2/16) := by
  have hm := finite_exponential_markov P N X (h*e/5) (Real.log (1+e))
    (h*((2+3*e/5)*Real.log (1+e/5)-2*e/5)) (by positivity) hInt hMoment
  have hr := mul_le_mul_of_nonneg_left (upper_rate_ge e he he1) hh
  have heq :
      h*((2+3*e/5)*Real.log (1+e/5)-2*e/5) -
        h*e/5*Real.log (1+e) = -h*upperRate e := by dsimp [upperRate]; ring
  rw [heq] at hm
  calc
    P.real {w | 1+e ≤ Y w} ≤ P.real {w | ∃ s, Real.log (1+e) ≤ X s w} :=
      measureReal_mono (fun w hw => hSelect w hw)
    _ ≤ N*Real.exp (-h*upperRate e) := hm
    _ ≤ N*Real.exp (-h*e^2/16) := by
      gcongr
      nlinarith

/-- Lower-tail assembly from the explicit inverse joint moment estimate. -/
theorem lower_tail_from_joint_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (X : Fin N → Ω → ℝ) (Y : Ω → ℝ) (h e : ℝ)
    (hh : 1 < h) (he : 0 ≤ e) (he1 : e < 1) (hlarge : 20 < h*e^2)
    (hSelect : ∀ w, Y w ≤ 1-e → ∃ s, X s w ≤ Real.log (1-e))
    (hInt : ∀ s, Integrable (fun w => Real.exp (-((h-1)*e/8)*X s w)) P)
    (hMoment : ∀ s, (∫ w, Real.exp (-((h-1)*e/8)*X s w) ∂P) ≤
      Real.exp (((15/7)*((h-1)*e/8)^2+(23/7)*((h-1)*e/8))/(h-1))) :
    P.real {w | Y w ≤ 1-e} ≤ N*Real.exp (-h*e^2/16) := by
  let t : ℝ := (h-1)*e/8
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hint' : ∀ s, Integrable (fun w => Real.exp (t*(-X s w))) P := by
    intro s
    convert hInt s using 1 <;> ext w <;> dsimp [t] <;> ring
  have hmom' : ∀ s, (∫ w, Real.exp (t*(-X s w)) ∂P) ≤
      Real.exp (((15/7)*t^2+(23/7)*t)/(h-1)) := by
    intro s
    convert hMoment s using 1 <;> congr 1 <;> ext w <;> dsimp [t] <;> ring
  have hm := finite_exponential_markov P N (fun s w => -X s w) t
    (-Real.log (1-e)) (((15/7)*t^2+(23/7)*t)/(h-1)) ht hint' hmom'
  have hlog : Real.log (1-e) ≤ -e := by
    have hz := Real.log_le_sub_one_of_pos (show 0 < 1-e by linarith)
    linarith
  have hexp :
      ((15/7)*t^2+(23/7)*t)/(h-1)-t*(-Real.log (1-e)) ≤ -h*e^2/16 := by
    calc
      _ ≤ ((15/7)*t^2+(23/7)*t)/(h-1)-t*e := by
        nlinarith [mul_le_mul_of_nonneg_left hlog ht]
      _ = -(41/448)*(h-1)*e^2+(23/56)*e := by
        dsimp [t]
        field_simp [show h-1 ≠ 0 by linarith]
        <;> ring
      _ ≤ _ := lower_rate_le h e he he1.le hlarge
  calc
    P.real {w | Y w ≤ 1-e} ≤ P.real {w | ∃ s, -Real.log (1-e) ≤ -X s w} :=
      measureReal_mono (fun w hw => by
        obtain ⟨s, hs⟩ := hSelect w hw
        exact ⟨s, neg_le_neg hs⟩)
    _ ≤ N*Real.exp (((15/7)*t^2+(23/7)*t)/(h-1)-t*(-Real.log (1-e))) := hm
    _ ≤ N*Real.exp (-h*e^2/16) := by gcongr

#print axioms exponential_markov
#print axioms finite_exponential_markov
#print axioms upper_tail_from_joint_moments
#print axioms lower_tail_from_joint_moments

end AHHExactEquation11
