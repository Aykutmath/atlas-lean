import PaperMultiscaleInfimum

noncomputable section
open MeasureTheory Filter GaussianEllipsoid GaussianMixedNormHelpers
open scoped Topology
namespace GaussianEllipsoidCandidate

/-- Full paper Theorem7.1 quantifier package: a positive c_ms depending only
on A (here universal), positive c_KA with the displayed K dependence, exact
h=floor(d/2), extended-real infimum, and uniformity over integer sequences. -/
theorem paper_multiscale_theorem (A : ℝ) (hA : 0 < A) :
    ∃ c_ms : ℝ, 0 < c_ms ∧ ∀ K : ℝ, 0 < K →
      ∃ c : ℝ, 0 < c ∧ c_ms/(Real.sqrt (max K 1)*(1+Real.log (max K 1))) ≤ c ∧
        ∀ n : ℕ → ℕ, (∀ᶠ d in atTop, (n d:ℝ) ≤ A*(d:ℝ)^2) →
          Tendsto (fun d => (gaussianBilinearSampleLaw (Fin (n d)) (d/2) (d/2)).real
            {X | (c:EReal) ≤ paperMultiscaleRatioInf d (n d) (d/2) K X}) atTop (𝓝 1) := by
  refine ⟨(1/2:ℝ)^30, by positivity, ?_⟩
  intro K hK
  refine ⟨multiscaleConstant K, multiscaleConstant_pos K, le_rfl, ?_⟩
  intro n hn
  exact paper_multiscale_infimum_tendsto_one A K hA hK n hn
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_multiscale_theorem
