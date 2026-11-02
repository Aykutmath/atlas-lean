import CyclicRiskRestriction

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BMCyclicRiskRestriction

/-- Integrating equally distributed, possibly dependent finite events. -/
theorem probability_le_of_average_indicators {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ} [NeZero N]
    (E : Fin N → Set Ω) (F : Set Ω) (hE : ∀ j, MeasurableSet (E j))
    (hF : MeasurableSet F) (p c : ℝ) (hp : ∀ j, μ.real (E j) = p)
    (hpoint : ∀ x, (∑ j, (E j).indicator (fun _ => (1:ℝ)) x) / N ≤
      c + F.indicator (fun _ => (1:ℝ)) x) :
    p ≤ c + μ.real F := by
  have hi (j : Fin N) : Integrable ((E j).indicator (fun _ => (1:ℝ))) μ :=
    (integrable_const 1).indicator (hE j)
  have hsum : Integrable (fun x => ∑ j, (E j).indicator (fun _ => (1:ℝ)) x) μ :=
    integrable_finset_sum _ (fun j _ => hi j)
  have h := integral_mono (hsum.div_const (N:ℝ))
    ((integrable_const c).add ((integrable_const 1).indicator hF)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_div, integral_finset_sum _ (fun j _ => hi j),
    integral_add (integrable_const c) ((integrable_const 1).indicator hF),
    integral_const, integral_indicator_const (1:ℝ) hF] at h
  simp_rw [integral_indicator_const (1:ℝ) (hE _), smul_eq_mul, mul_one, hp] at h
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simpa [hN] using h

end BMCyclicRiskRestriction
