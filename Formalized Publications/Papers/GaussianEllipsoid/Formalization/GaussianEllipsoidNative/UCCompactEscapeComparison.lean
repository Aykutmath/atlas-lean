import UCFiniteEscapeComparison
import BMGordonProcesses
import GordonCompactPassage

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle BMGordon
namespace UCEscape

lemma coefficient_abs_le {n d : ℕ} (S : HMat d) (u : Euclid n)
    (hS : ‖S‖ = 1) (hu : ‖u‖ = 1) (ω : Space n d) :
    |⟪auxiliaryCoefficient u S,ω⟫_ℝ| ≤ 2*‖ω‖ ∧
    |⟪primaryCoefficient u S,ω⟫_ℝ| ≤ 2*‖ω‖ := by
  have ha : ‖auxiliaryCoefficient u S‖^2 = 2 := by
    rw [← real_inner_self_eq_norm_sq, auxiliaryCoefficient_inner,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hS, hu]
    norm_num
  have hb : ‖primaryCoefficient u S‖^2 = 2 := by
    rw [← real_inner_self_eq_norm_sq, primaryCoefficient_inner,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hS, hu]
    norm_num
  have hna : ‖auxiliaryCoefficient u S‖ ≤ 2 := by nlinarith [norm_nonneg (auxiliaryCoefficient u S)]
  have hnb : ‖primaryCoefficient u S‖ ≤ 2 := by nlinarith [norm_nonneg (primaryCoefficient u S)]
  exact ⟨(abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hna (norm_nonneg _)),
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hnb (norm_nonneg _))⟩

/-- Compact expected escape comparison for any compact family of unit matrices
and unit measurement directions. Every finite comparison and analytic envelope
is proved; positivity is needed only for the later sharp width estimate. -/
theorem compact_escape_comparison {n d : ℕ}
    (K L : Type) [MetricSpace K] [MetricSpace L]
    [CompactSpace K] [CompactSpace L] [Nonempty K] [Nonempty L]
    (S : K → HMat d) (u : K × L → Euclid n)
    (hSc : Continuous S) (huc : Continuous u)
    (hS : ∀ k, ‖S k‖ = 1) (hu : ∀ p, ‖u p‖ = 1) :
    (∫ ω, BMGordonCompact.compactMinMax
      (fun p : K × L => fun ω => ⟪auxiliaryCoefficient (u p) (S p.1),ω⟫_ℝ) ω ∂law n d) ≤
    ∫ ω, BMGordonCompact.compactMinMax
      (fun p : K × L => fun ω => ⟪primaryCoefficient (u p) (S p.1),ω⟫_ℝ) ω ∂law n d := by
  apply BMGordonCompact.compact_comparison_of_finite K L (Space n d) (law n d)
  · exact ae_of_all _ fun ω =>
      (auxiliaryCoefficient_continuous.comp
        (huc.prodMk (hSc.comp continuous_fst))).inner continuous_const
  · exact ae_of_all _ fun ω =>
      (primaryCoefficient_continuous.comp
        (huc.prodMk (hSc.comp continuous_fst))).inner continuous_const
  · intro tK tL htK htL _ _ _ _
    exact finite_escape_comparison ↥tK ↥tL (fun k => S k.1) (fun k l => u (k.1,l.1))
      (fun k => hS k.1) (fun k l => hu (k.1,l.1))
  · intro tK tL htK htL _ _ _ _
    constructor
    · exact finiteValue_integrable _ _ (fun ω => 2*‖ω‖)
        (fun _ _ => continuous_const.inner continuous_id) (envelope_integrable n d)
        (fun k l ω => (coefficient_abs_le (S k.1) (u (k.1,l.1)) (hS k.1) (hu (k.1,l.1)) ω).1)
    · exact finiteValue_integrable _ _ (fun ω => 2*‖ω‖)
        (fun _ _ => continuous_const.inner continuous_id) (envelope_integrable n d)
        (fun k l ω => (coefficient_abs_le (S k.1) (u (k.1,l.1)) (hS k.1) (hu (k.1,l.1)) ω).2)
  · refine ⟨(fun ω => 2*‖ω‖), (fun ω => 2*‖ω‖),
      envelope_integrable n d, envelope_integrable n d, ?_⟩
    intro tK tL htK htL _ _ _ _
    constructor
    · exact ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs, finiteValue, BMGordonCompact.finMin, BMGordonCompact.finMax] using finiteValue_abs_le
          (fun k : ↥tK => fun l : ↥tL => fun ω =>
            ⟪auxiliaryCoefficient (u (k.1,l.1)) (S k.1),ω⟫_ℝ)
          (fun ω => 2*‖ω‖)
          (fun k l ω => (coefficient_abs_le (S k.1) (u (k.1,l.1)) (hS k.1) (hu (k.1,l.1)) ω).1) ω
    · exact ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs, finiteValue, BMGordonCompact.finMin, BMGordonCompact.finMax] using finiteValue_abs_le
          (fun k : ↥tK => fun l : ↥tL => fun ω =>
            ⟪primaryCoefficient (u (k.1,l.1)) (S k.1),ω⟫_ℝ)
          (fun ω => 2*‖ω‖)
          (fun k l ω => (coefficient_abs_le (S k.1) (u (k.1,l.1)) (hS k.1) (hu (k.1,l.1)) ω).2) ω

#print axioms compact_escape_comparison
end UCEscape
