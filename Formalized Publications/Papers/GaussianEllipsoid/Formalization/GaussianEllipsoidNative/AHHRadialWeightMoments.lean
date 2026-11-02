import AHHActualRadialSelection
import AHHRadialGammaPairs

/-! Exact transport of the proven Gamma-pair moments to every weight in the
actual polar sample. All coordinate independence is supplied by `radiiLaw`. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers
namespace AHHRadial

def squaredRadiiAt (n : ℕ) (i : Fin n) (r : Fin n → Radius × Radius) : ℝ × ℝ :=
  (((r i).1 : ℝ)^2, ((r i).2 : ℝ)^2)

theorem complex_radius_sq_preserving (h : ℕ) (hh : 0 < h) :
    MeasurePreserving (fun r : Radius => (r : ℝ)^2)
      (radiusLaw (volume : Measure (CE h)) h) (gammaMeasure h h) := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  refine ⟨by fun_prop, ?_⟩
  rw [radiusLaw_map_sq _ (by exact_mod_cast hh), complex_finrank_real]
  congr 1
  push_cast
  ring

theorem squaredRadiiAt_preserving (n h : ℕ) (hh : 0 < h) (i : Fin n) :
    MeasurePreserving (squaredRadiiAt n i) (radiiLaw n h)
      ((gammaMeasure h h).prod (gammaMeasure h h)) := by
  letI := radiusPairLaw_probability h hh
  exact ((complex_radius_sq_preserving h hh).prod (complex_radius_sq_preserving h hh)).comp
    (measurePreserving_eval (fun _ : Fin n => radiusPairLaw h) i)

theorem log_radialWeight (n : ℕ) (r : Fin n → Radius × Radius) (i : Fin n) :
    Real.log (radialWeight r i) =
      Real.log (squaredRadiiAt n i r).1 + Real.log (squaredRadiiAt n i r).2 := by
  exact Real.log_mul (sq_pos_of_pos (r i).1.property).ne'
    (sq_pos_of_pos (r i).2.property).ne'

theorem radialWeight_exp_integrable (n h : ℕ) (hh : 0 < h) (i : Fin n)
    (q : ℝ) (hq : 0 < (h : ℝ)+q) :
    Integrable (fun r => Real.exp (q*Real.log (radialWeight r i))) (radiiLaw n h) := by
  have hi := (squaredRadiiAt_preserving n h hh i).integrable_comp_of_integrable
    (gamma_pair_integrable_exp_log (by exact_mod_cast hh) hq)
  simpa only [Function.comp_def, ← log_radialWeight] using hi

theorem radialWeight_exp_integral (n h : ℕ) (hh : 0 < h) (i : Fin n) (q : ℝ) :
    (∫ r, Real.exp (q*Real.log (radialWeight r i)) ∂radiiLaw n h) =
      ∫ p : ℝ × ℝ, Real.exp (q*(Real.log p.1+Real.log p.2))
        ∂((gammaMeasure h h).prod (gammaMeasure h h)) := by
  have hm := integral_map (μ := radiiLaw n h) (φ := squaredRadiiAt n i)
    (f := fun p : ℝ × ℝ => Real.exp (q*(Real.log p.1+Real.log p.2)))
    (squaredRadiiAt_preserving n h hh i).measurable.aemeasurable
    (by fun_prop)
  rw [(squaredRadiiAt_preserving n h hh i).map_eq] at hm
  simpa only [← log_radialWeight] using hm.symm

theorem radialWeight_upper_exp_le (n h : ℕ) (hh : 0 < h) (i : Fin n)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ r, Real.exp (q*Real.log (radialWeight r i)) ∂radiiLaw n h) ≤
      Real.exp (2*(h : ℝ)*((1+q/h)*Real.log (1+q/h)-q/h)) := by
  rw [radialWeight_exp_integral n h hh]
  exact gamma_pair_exp_moment_upper (by exact_mod_cast hh) hq

theorem radialWeight_lower_exp_le (n h : ℕ) (hh : 2 ≤ h) (i : Fin n)
    (t : ℝ) (ht : 0 ≤ t) (hth : t < (h : ℝ)-1) :
    (∫ r, Real.exp (-t*Real.log (radialWeight r i)) ∂radiiLaw n h) ≤
      Real.exp ((2*t+t^2)/((h : ℝ)-1-t)) := by
  rw [radialWeight_exp_integral n h (by omega)]
  exact gamma_pair_exp_moment_lower (by exact_mod_cast hh) ht hth

#print axioms squaredRadiiAt_preserving
#print axioms radialWeight_exp_integrable
#print axioms radialWeight_upper_exp_le
#print axioms radialWeight_lower_exp_le
end AHHRadial
