import AHHActualRadialSelection

/-! Inclusive logarithmic event selectors for the concrete polar sample. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges
namespace AHHRadial

def polarLog (n h : ℕ) (i : Fin n) (w : PolarSample n h) : ℝ :=
  Real.log (radialWeight w.1 i) +
    Real.log (unitCovarianceNorm n h w.2 / unitCovarianceMean n h)

theorem polarLog_eq_log (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (i : Fin n) (w : PolarSample n h) :
    polarLog n h i w = Real.log
      (radialWeight w.1 i * (unitCovarianceNorm n h w.2 / unitCovarianceMean n h)) := by
  unfold polarLog
  rw [Real.log_mul (radialWeight_pos w.1 i).ne'
    (div_pos (lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceNorm n h hn w.2))
      (lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceMean n h hn hh))).ne']

theorem polar_upper_log_select (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (a : ℝ) (ha : 0 < a) (w : PolarSample n h)
    (hw : a ≤ polarCovarianceNorm n h w / unitCovarianceMean n h) :
    ∃ i : Fin n, Real.log a ≤ polarLog n h i w := by
  have hμ : 0 < unitCovarianceMean n h :=
    lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceMean n h hn hh)
  obtain ⟨i, hi⟩ := polar_upper_select n h hn w
  refine ⟨i, ?_⟩
  rw [polarLog_eq_log n h hn hh]
  apply Real.log_le_log ha
  calc
    a ≤ polarCovarianceNorm n h w / unitCovarianceMean n h := hw
    _ ≤ (radialWeight w.1 i * unitCovarianceNorm n h w.2) / unitCovarianceMean n h :=
      div_le_div_of_nonneg_right hi hμ.le
    _ = _ := mul_div_assoc _ _ _

theorem polar_lower_log_select (n h : ℕ) (hn : 0 < n) (hh : 0 < h)
    (a : ℝ) (w : PolarSample n h)
    (hw : polarCovarianceNorm n h w / unitCovarianceMean n h ≤ a) :
    ∃ i : Fin n, polarLog n h i w ≤ Real.log a := by
  have hμ : 0 < unitCovarianceMean n h :=
    lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceMean n h hn hh)
  obtain ⟨i, hi⟩ := polar_lower_select n h hn w
  refine ⟨i, ?_⟩
  rw [polarLog_eq_log n h hn hh]
  apply Real.log_le_log (mul_pos (radialWeight_pos w.1 i)
    (div_pos (lt_of_lt_of_le zero_lt_one (one_le_unitCovarianceNorm n h hn w.2)) hμ))
  calc
    radialWeight w.1 i * (unitCovarianceNorm n h w.2 / unitCovarianceMean n h) =
        (radialWeight w.1 i * unitCovarianceNorm n h w.2) / unitCovarianceMean n h :=
      (mul_div_assoc _ _ _).symm
    _ ≤ polarCovarianceNorm n h w / unitCovarianceMean n h :=
      div_le_div_of_nonneg_right hi hμ.le
    _ ≤ a := hw

#print axioms polar_upper_log_select
#print axioms polar_lower_log_select
end AHHRadial
