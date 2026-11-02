import AHHExactEquation11MomentAssembly
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Finishing arithmetic and event assembly. No statement here discharges
sphere entropy or asserts that generic moment hypotheses hold for an ensemble. -/
noncomputable section
open MeasureTheory
namespace AHHExactEquation11

/-- The chosen prefactor covers the small-parameter regime. -/
theorem trivial_regime_bound (N : ℕ) (hN : 0 < N) (h e : ℝ)
    (hsmall : h*e^2 ≤ 20) : 1 ≤ 4*N*Real.exp (-h*e^2/16) := by
  have hlog2 : (2/3 : ℝ) ≤ Real.log 2 := by
    have hl := log_lower_cubic 1 (by norm_num)
    norm_num at hl
    linarith
  have hlog4 : (5/4 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hex : Real.exp (h*e^2/16) ≤ 4 := by
    calc
      _ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr (by linarith)
      _ = 4 := Real.exp_log (by norm_num)
  have hid : Real.exp (-h*e^2/16) * Real.exp (h*e^2/16) = 1 := by
    rw [← Real.exp_add]
    have hz : -h*e^2/16+h*e^2/16 = 0 := by ring
    rw [hz, Real.exp_zero]
  have h4 : 1 ≤ 4*Real.exp (-h*e^2/16) := by
    have hm := mul_le_mul_of_nonneg_left hex (Real.exp_pos (-h*e^2/16)).le
    rw [hid] at hm
    linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith [Real.exp_pos (-h*e^2/16)]

/-- Conversion from the two inclusive normalized tails to a relative-deviation
bound, including epsilon=1 when the random variable is positive. -/
theorem relative_deviation_from_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 0 < N) (Z : Ω → ℝ) (μ h e : ℝ)
    (hμ : 0 < μ) (he : 0 < e) (he1 : e ≤ 1)
    (hZ : ∀ w, 0 < Z w)
    (hupper : 20 < h*e^2 → P.real {w | 1+e ≤ Z w/μ} ≤ N*Real.exp (-h*e^2/16))
    (hlower : 20 < h*e^2 → e < 1 → P.real {w | Z w/μ ≤ 1-e} ≤ N*Real.exp (-h*e^2/16)) :
    P.real {w | e*μ ≤ |Z w-μ|} ≤ 4*N*Real.exp (-h*e^2/16) := by
  by_cases hlarge : 20 < h*e^2
  · have hu := hupper hlarge
    have hl : P.real {w | Z w/μ ≤ 1-e} ≤ N*Real.exp (-h*e^2/16) := by
      rcases lt_or_eq_of_le he1 with he1 | rfl
      · exact hlower hlarge he1
      · have heq : {w | Z w/μ ≤ 1-(1:ℝ)} = ∅ := by
          ext w
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, sub_self, not_le]
          exact div_pos (hZ w) hμ
        rw [heq, measureReal_empty]
        positivity
    have hsub : {w | e*μ ≤ |Z w-μ|} ⊆
        {w | 1+e ≤ Z w/μ} ∪ {w | Z w/μ ≤ 1-e} := by
      intro w hw
      change e*μ ≤ |Z w-μ| at hw
      rcases le_abs.mp hw with hw | hw
      · exact Or.inl ((le_div_iff₀ hμ).mpr (by nlinarith))
      · exact Or.inr ((div_le_iff₀ hμ).mpr (by nlinarith))
    calc
      _ ≤ P.real ({w | 1+e ≤ Z w/μ} ∪ {w | Z w/μ ≤ 1-e}) := measureReal_mono hsub
      _ ≤ P.real {w | 1+e ≤ Z w/μ} + P.real {w | Z w/μ ≤ 1-e} := measureReal_union_le _ _
      _ ≤ N*Real.exp (-h*e^2/16) + N*Real.exp (-h*e^2/16) := add_le_add hu hl
      _ ≤ _ := by nlinarith [Real.exp_pos (-h*e^2/16), Nat.cast_nonneg (α := ℝ) N]
  · exact measureReal_le_one.trans (trivial_regime_bound N hN h e (le_of_not_gt hlarge))

/-- The paper's additional positive threshold and additional nonnegative
error term follow from the stronger relative-deviation estimate. -/
theorem additive_threshold_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (N : ℕ) (μ h e Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hb : P.real {w | e*μ ≤ |Z w-μ|} ≤ 4*N*Real.exp (-h*e^2/16)) :
    P.real {w | e*μ+Δ ≤ |Z w-μ|} ≤
      4*N*Real.exp (-h*e^2/16) + 2*Real.exp (-(h-1)*Δ^2/8) := by
  calc
    _ ≤ P.real {w | e*μ ≤ |Z w-μ|} := measureReal_mono (fun w hw => by
      change e*μ+Δ ≤ |Z w-μ| at hw
      exact le_trans (le_add_of_nonneg_right hΔ) hw)
    _ ≤ 4*N*Real.exp (-h*e^2/16) := hb
    _ ≤ _ := le_add_of_nonneg_right (by positivity)

#print axioms trivial_regime_bound
#print axioms relative_deviation_from_tails
#print axioms additive_threshold_bound
end AHHExactEquation11
