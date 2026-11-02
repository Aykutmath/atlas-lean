import GaussianMatrixOperator
import Mathlib.Tactic

/-! Explicit constants and the final Markov conversion for tensor covariance.
The scalar conversion keeps its hypotheses visible; actual matrix moment inputs
are supplied by the proved Gaussian covariance modules. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace GaussianTensorMoments

theorem log_nine_le_three : log 9 ≤ 3 := by
  apply (log_le_iff_le_exp (by norm_num : (0:ℝ)<9)).2
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤3) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_two_le_one : log 2 ≤ 1 :=
  (log_lt_sub_one_of_pos (by norm_num) (by norm_num)).le.trans (by norm_num)

/-- The entropy shift plus the h-th moment index has an absolute linear bound. -/
theorem gaussianNetShift_add_dimension_le (q h : ℕ) (hq : 1 ≤ q) :
    gaussianNetShift q h + h ≤ 4*(q+h : ℕ) := by
  have hlog := mul_le_mul_of_nonneg_left log_nine_le_three
    (Nat.cast_nonneg (q+h) : (0:ℝ)≤(q+h:ℕ))
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  unfold gaussianNetShift
  push_cast at hlog ⊢
  linarith [log_two_le_one]

/-- Convenient dimension-scale Gaussian moment bound with explicit constant 32. -/
theorem gaussianMatrixCLM_dimension_moment_le (q h : ℕ) (hq : 1 ≤ q) :
    (∫ x, ‖gaussianMatrixCLM q h x‖^(2*h)
      ∂gaussianProductLaw (Fin q × Fin h)) ≤ (32*(q+h : ℕ))^h := by
  apply (gaussianMatrixCLM_even_moment_le q h h).trans
  apply pow_le_pow_left₀ (mul_nonneg (by norm_num)
    (add_nonneg (gaussianNetShift_nonneg q h) (Nat.cast_nonneg h)))
  have hh := gaussianNetShift_add_dimension_le q h hq
  nlinarith

/-- Explicit Markov conversion from a dominating nonnegative moment. -/
theorem measureReal_lt_of_dominated_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F O : Ω → ℝ} {A B : ℝ} (hB : 0 < B) (m : ℕ)
    (hFnn : 0 ≤ᵐ[μ] F) (hFi : Integrable F μ)
    (hdom : ∀ ω, O ω^m ≤ F ω)
    (hmoment : (∫ ω, F ω ∂μ) ≤ A*B^m) :
    μ.real {ω | 2*B < O ω} ≤ A/(2:ℝ)^m := by
  have hbase : 0 ≤ 2*B := by positivity
  have hsub : {ω | 2*B < O ω} ⊆ {ω | (2*B)^m ≤ F ω} := by
    intro ω hω
    exact (pow_le_pow_left₀ hbase (le_of_lt hω) m).trans (hdom ω)
  have hmark := mul_meas_ge_le_integral_of_nonneg hFnn hFi ((2*B)^m)
  have hm : (2*B)^m * μ.real {ω | 2*B < O ω} ≤ A*B^m := by
    calc
      _ ≤ (2*B)^m * μ.real {ω | (2*B)^m ≤ F ω} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsub) (pow_nonneg hbase _)
      _ ≤ ∫ ω, F ω ∂μ := hmark
      _ ≤ _ := hmoment
  apply (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) m)).2
  apply (mul_le_mul_iff_left₀ (pow_pos hB m)).mp
  calc
    μ.real {ω | 2*B < O ω} * (2:ℝ)^m * B^m =
        (2*B)^m * μ.real {ω | 2*B < O ω} := by rw [mul_pow]; ring
    _ ≤ _ := hm

#print axioms gaussianMatrixCLM_dimension_moment_le
#print axioms measureReal_lt_of_dominated_moment

end GaussianTensorMoments
