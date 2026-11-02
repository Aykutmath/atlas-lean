import AHHBoundedEntropyMoments

/-! Real-power and almost-everywhere interfaces for the proved moment calculus.
The power-entropy estimate remains an explicit analytic hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace AHHBoundedPositiveMoments
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

theorem powerEntropy_congr {X Y : Ω → ℝ} (h : X =ᵐ[P] Y) (p : ℝ) :
    powerEntropy P X p = powerEntropy P Y p := by
  unfold powerEntropy
  rw [mgf_congr h]
  congr 1
  congr 1
  exact integral_congr_ae (h.mono fun w hw => by dsimp only; rw [hw])

theorem powerEntropy_eq_entropy (X : Ω → ℝ) (p : ℝ) :
    powerEntropy P X p =
      (∫ w, Real.exp (p*X w) * Real.log (Real.exp (p*X w)) ∂P) -
        (∫ w, Real.exp (p*X w) ∂P) * Real.log (∫ w, Real.exp (p*X w) ∂P) := by
  unfold powerEntropy mgf
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by dsimp only; rw [Real.log_exp]; ring

theorem mgf_log_eq_rpow_integral (F : Ω → ℝ) (hFpos : ∀ w, 0 < F w) (p : ℝ) :
    mgf (fun w => Real.log (F w)) P p = ∫ w, (F w)^p ∂P := by
  unfold mgf
  apply integral_congr_ae
  exact ae_of_all _ fun w => by dsimp only; rw [Real.rpow_def_of_pos (hFpos w)]; congr 1; ring

theorem log_bounded (F : Ω → ℝ) {B : ℝ}
    (hlower : ∀ w, 1 ≤ F w) (hupper : ∀ w, F w ≤ B) :
    ∀ w, |Real.log (F w)| ≤ Real.log B := by
  intro w
  rw [abs_of_nonneg (Real.log_nonneg (hlower w))]
  exact Real.log_le_log (by linarith [hlower w]) (hupper w)

/-- The requested positive moment inequality, assuming precisely the
self-bounding power-entropy inequality. -/
theorem positive_moment_le (F : Ω → ℝ) (hF : Measurable F) {B a : ℝ}
    (hlower : ∀ w, 1 ≤ F w) (hupper : ∀ w, F w ≤ B) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P (fun w => Real.log (F w)) p ≤
      p^2/a * (∫ w, (F w)^(p-1) ∂P))
    {q : ℝ} (hq : 1 ≤ q) :
    (∫ w, (F w)^q ∂P)^(1/q) ≤ (∫ w, F w ∂P) + (q-1)/a := by
  have hpos : ∀ w, 0 < F w := fun w => by linarith [hlower w]
  have hbound := log_bounded F hlower hupper
  have hEnt' : ∀ p : ℝ, powerEntropy P (fun w => Real.log (F w)) p ≤
      p^2/a * mgf (fun w => Real.log (F w)) P (p-1) := by
    intro p
    simpa only [mgf_log_eq_rpow_integral P F hpos] using hEnt p
  have h := root_mgf_le P (fun w => Real.log (F w)) hF.log hbound ha hEnt' hq
  have hm : 0 < ∫ w, (F w)^q ∂P := by
    rw [← mgf_log_eq_rpow_integral P F hpos]
    exact mgf_pos P _ hF.log hbound q
  rw [Real.rpow_def_of_pos hm]
  simpa only [cgf, mgf_log_eq_rpow_integral P F hpos, Real.rpow_one,
    mul_one_div] using h

/-- The requested inverse moment inequality, assuming precisely the
self-bounding power-entropy inequality. -/
theorem negative_moment_le (F : Ω → ℝ) (hF : Measurable F) {B a : ℝ}
    (hlower : ∀ w, 1 ≤ F w) (hupper : ∀ w, F w ≤ B) (ha : 0 < a)
    (hEnt : ∀ p : ℝ, powerEntropy P (fun w => Real.log (F w)) p ≤
      p^2/a * (∫ w, (F w)^(p-1) ∂P))
    {t : ℝ} (ht : 0 ≤ t) :
    Real.log (∫ w, (F w / (∫ z, F z ∂P))^(-t) ∂P) ≤ t*(t+1)/a := by
  have hpos : ∀ w, 0 < F w := fun w => by linarith [hlower w]
  let X := fun w => Real.log (F w)
  have hbound := log_bounded F hlower hupper
  have hEnt' : ∀ p : ℝ, powerEntropy P X p ≤ p^2/a * mgf X P (p-1) := by
    intro p
    simpa only [X, mgf_log_eq_rpow_integral P F hpos] using hEnt p
  have h := negative_cgf_le P X hF.log hbound
    (fun w => Real.log_nonneg (hlower w)) ha hEnt' ht
  have hmean : mgf X P 1 = ∫ w, F w ∂P := by
    simp only [X, mgf_log_eq_rpow_integral P F hpos, Real.rpow_one]
  have hmeanpos : 0 < ∫ w, F w ∂P := hmean ▸ mgf_pos P X hF.log hbound 1
  have heq (w : Ω) : (F w / (∫ z, F z ∂P))^(-t) =
      Real.exp (t*Real.log (∫ z, F z ∂P)) * Real.exp (-t * X w) := by
    rw [Real.rpow_def_of_pos (div_pos (hpos w) hmeanpos),
      Real.log_div (hpos w).ne' hmeanpos.ne', ← Real.exp_add]
    congr 1
    dsimp [X]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  change Real.log (Real.exp (t*Real.log (∫ z, F z ∂P)) * mgf X P (-t)) ≤ _
  rw [Real.log_mul (Real.exp_pos _).ne'
    (mgf_pos P X hF.log hbound (-t)).ne', Real.log_exp]
  simpa only [cgf, hmean, add_comm] using h

#print axioms positive_moment_le
#print axioms negative_moment_le
end AHHBoundedPositiveMoments
