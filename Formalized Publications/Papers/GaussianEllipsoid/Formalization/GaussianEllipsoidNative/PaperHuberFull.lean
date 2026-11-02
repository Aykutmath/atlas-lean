import PaperHuberResiduals
import PaperHuberInfinity
import BMProjectFinal

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace GaussianEllipsoid

/-- Exact Section3 aspect premise is derived from the manuscript's real ratio
limit, with an explicit intermediate margin. -/
theorem paper_limsup_of_aspect_limit (n : ℕ → ℕ) (α : ℝ)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α))
    (hα : 0 < α) (hα4 : α < 1/4) :
    limsup (dimensionRatio n) atTop < (1/4:ℝ≥0∞) := by
  let β := (α+1/4)/2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ4 : β < 1/4 := by dsimp [β]; linarith
  have hβ : 0 < β := hα.trans hαβ
  have ht := hconv.eventually (gt_mem_nhds hαβ)
  have hb : ∀ᶠ d in atTop, dimensionRatio n d ≤ ENNReal.ofReal β := by
    filter_upwards [ht,eventually_ge_atTop 1] with d hratio hd
    exact ((dimensionRatio_lt_ofReal hd hβ).mpr hratio).le
  apply (limsup_le_of_eventually_le' hb).trans_lt
  rw [ennreal_quarter_eq_ofReal, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  exact hβ4

/-- Full literal three-conclusion Proposition4.1. The spectral box is supplied
by the proved approximate-fitting theorem, and every single minimizer family
in that fixed box has all three conclusions simultaneously. -/
theorem paper_huber_full_residuals
    (n : ℕ → ℕ) (α : ℝ) (hn : ∀ d, 0 < n d)
    (hconv : Tendsto (fun d => (n d:ℝ)/(d:ℝ)^2) atTop (𝓝 α))
    (hα : 0 < α) (hα4 : α < 1/4) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMminRisk n lo hi ∧
      ∀ Sstar : ∀ d, Sample d (n d) → Square d,
      (∀ d x, IsHuberMinimizer lo hi x (Sstar d x)) →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun d => (gaussianSampleLaw d (n d)).real
        {x | ε < (1/(n d:ℝ))*∑ i, (residual x (Sstar d x) i)^2}) atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε → Tendsto (fun d => (gaussianSampleLaw d (n d)).real
        {x | ε < euclidNorm (center (residual x (Sstar d x)))/(d:ℝ)}) atTop (𝓝 0)) ∧
      (∃ C : ℝ, 0 < C ∧ Tendsto (fun d => (gaussianSampleLaw d (n d)).real
        {x | C*Real.sqrt (Real.log (d:ℝ)) < ‖center (residual x (Sstar d x))‖})
        atTop (𝓝 0)) := by
  obtain ⟨lo,hi,hlo,hle,hBM⟩ := bmApproximateFitting_unconditional n hn
    (paper_limsup_of_aspect_limit n α hconv hα hα4)
  refine ⟨lo,hi,hlo,hle,hBM,?_⟩
  intro Sstar hStar
  refine ⟨?_,?_,?_⟩
  · intro ε hε
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using
      paper_huber_raw_energy n α hn hconv hα hα4 lo hi hlo hle hBM Sstar hStar ε hε
  · exact paper_huber_centered_l2 n α hn hconv hα hα4 lo hi hlo hle hBM Sstar hStar
  · exact paper_huber_centered_linf n α hn hconv hα lo hi hlo hle hBM Sstar hStar

end GaussianEllipsoid
#print axioms GaussianEllipsoid.paper_huber_full_residuals
