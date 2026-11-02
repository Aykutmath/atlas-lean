import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real

namespace GaussianEllipsoidCandidate

/-- Exact scalar optimization for a quadratic MGF bound on a finite interval. -/
theorem exists_mgf_tail_parameter (V b x : ℝ)
    (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam ≤ 1 / b ∧
      -lam * x + lam ^ 2 * V ≤ -(1 / 4 : ℝ) * min (x ^ 2 / V) (x / b) := by
  by_cases hcase : x * b ≤ V
  · refine ⟨x / (2 * V), div_nonneg hx (by positivity), ?_, ?_⟩
    · apply (le_div_iff₀ hb).2
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 2 * V)).2
      nlinarith
    · have heq : -(x / (2 * V)) * x + (x / (2 * V)) ^ 2 * V =
          -(1 / 4 : ℝ) * (x ^ 2 / V) := by
        field_simp [ne_of_gt hV, ne_of_gt hb]
        <;> ring
      rw [heq]
      exact mul_le_mul_of_nonpos_left (min_le_left _ _) (by norm_num)
  · have hcase' : V ≤ x * b := le_of_lt (lt_of_not_ge hcase)
    refine ⟨1 / (2 * b), by positivity, ?_, ?_⟩
    · apply one_div_le_one_div_of_le hb
      linarith
    · have hscaled := mul_le_mul_of_nonneg_left hcase' (sq_nonneg (1 / (2 * b)))
      have heq : -(1 / (2 * b)) * x + (1 / (2 * b)) ^ 2 * (x * b) =
          -(1 / 4 : ℝ) * (x / b) := by
        field_simp [ne_of_gt hV, ne_of_gt hb]
        <;> ring
      calc
        -(1 / (2 * b)) * x + (1 / (2 * b)) ^ 2 * V
            ≤ -(1 / (2 * b)) * x + (1 / (2 * b)) ^ 2 * (x * b) := by linarith
        _ = -(1 / 4 : ℝ) * (x / b) := heq
        _ ≤ -(1 / 4 : ℝ) * min (x ^ 2 / V) (x / b) :=
          mul_le_mul_of_nonpos_left (min_le_right _ _) (by norm_num)

/-- A lower subexponential tail from an MGF bound on a finite radius.
No bounded-increment assumption is present. The integral hypotheses are
exactly what conditional-MGF iteration supplies in the multiscale proof. -/
theorem lower_tail_of_mgf_radius {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)
    (V b x : ℝ) (hV : 0 < V) (hb : 0 < b) (hx : 0 ≤ x)
    (hint : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      Integrable (fun ω => Real.exp ((-lam) * X ω)) μ)
    (hmgf : ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 / b →
      mgf X μ (-lam) ≤ Real.exp (lam ^ 2 * V)) :
    μ.real {ω | X ω ≤ -x} ≤
      Real.exp (-(1 / 4 : ℝ) * min (x ^ 2 / V) (x / b)) := by
  obtain ⟨lam, hlam, hlamb, hopt⟩ := exists_mgf_tail_parameter V b x hV hb hx
  calc
    μ.real {ω | X ω ≤ -x}
        ≤ Real.exp (-(-lam) * (-x)) * mgf X μ (-lam) :=
      measure_le_le_exp_mul_mgf (-x) (neg_nonpos.mpr hlam) (hint lam hlam hlamb)
    _ ≤ Real.exp (-(-lam) * (-x)) * Real.exp (lam ^ 2 * V) :=
      mul_le_mul_of_nonneg_left (hmgf lam hlam hlamb) (Real.exp_nonneg _)
    _ = Real.exp (-lam * x + lam ^ 2 * V) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(1 / 4 : ℝ) * min (x ^ 2 / V) (x / b)) :=
      Real.exp_le_exp.mpr hopt

#print axioms exists_mgf_tail_parameter
#print axioms lower_tail_of_mgf_radius

end GaussianEllipsoidCandidate
