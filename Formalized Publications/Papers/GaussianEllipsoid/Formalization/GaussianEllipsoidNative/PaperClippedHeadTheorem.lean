import PaperMultiscaleTheorem

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers
open scoped Topology
namespace GaussianEllipsoidCandidate

/-- Literal strict bad-infimum probability from the clipped-head restatement. -/
theorem paper_clipped_head_failure_tendsto_zero (A K : ℝ)
    (hA : 0 < A) (hK : 0 < K) (n : ℕ → ℕ)
    (hn : ∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
      {X | paperMultiscaleRatioInf d (n d) (d/2) K X < (multiscaleConstant K:EReal)})
      atTop (𝓝 0) := by
  have hgood := paper_multiscale_uniform_good_tendsto_one A K hA hK n hn
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub hgood
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with d hd
  have heq : {X | paperMultiscaleRatioInf d (n d) (d/2) K X < (multiscaleConstant K:EReal)} =
      (multiscaleGoodDimension d (n d) (d/2) K)ᶜ := by
    ext X
    change paperMultiscaleRatioInf d (n d) (d/2) K X < (multiscaleConstant K:EReal) ↔
      ¬ X ∈ multiscaleGoodDimension d (n d) (d/2) K
    rw [← paperMultiscaleRatioInf_ge_iff d (n d) (d/2) (by omega) K X]
    exact lt_iff_not_ge
  rw [heq,measureReal_compl (multiscaleGoodDimension_isClosed d (n d) (d/2) K).measurableSet]
  simp

/-- Full positive-constant/K-dependence package of the paper's clipped-head theorem. -/
theorem paper_clipped_head_theorem (A : ℝ) (hA : 0 < A) :
    ∃ c_ms : ℝ, 0 < c_ms ∧ ∀ K : ℝ, 0 < K →
      ∃ c : ℝ, 0 < c ∧ c_ms/(Real.sqrt (max K 1)*(1+Real.log (max K 1))) ≤ c ∧
        ∀ n : ℕ → ℕ, (∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) →
          Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
            {X | paperMultiscaleRatioInf d (n d) (d/2) K X < (c:EReal)}) atTop (𝓝 0) := by
  refine ⟨(1/2:ℝ)^30,by positivity,?_⟩
  intro K hK
  refine ⟨multiscaleConstant K,multiscaleConstant_pos K,le_rfl,?_⟩
  intro n hn
  exact paper_clipped_head_failure_tendsto_zero A K hA hK n hn
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_clipped_head_theorem
