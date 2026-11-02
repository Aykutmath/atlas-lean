import CyclicMinRiskRestriction

/-!
# Small-slack limits for actual Gaussian cyclic risk restriction

The elementary limit argument below is deliberately independent of sample
sizes.  In particular, its conclusion does not require the original sample
sequence to have any positive lower aspect ratio.
-/
noncomputable section
open MeasureTheory Filter

namespace BMCyclicRiskRestriction

/-- A nonnegative sequence bounded by a vanishing sequence plus arbitrarily
small positive slack tends to zero. -/
theorem tendsto_zero_of_arbitrarily_small_slack
    {f : ℕ → ℝ} {g : ℝ → ℕ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hf : ∀ d, 0 ≤ f d)
    (hg : ∀ δ > 0, Tendsto (g δ) atTop (nhds 0))
    (hbound : ∀ δ > 0, ∀ d, f d ≤ g δ d + δ/ε) :
    Tendsto f atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun d => hb.trans_le (hf d)
  · intro b hb
    have hδ : 0 < b*ε/2 := by positivity
    have hsmall : ∀ᶠ d in atTop, g (b*ε/2) d < b/2 :=
      (tendsto_order.1 (hg (b*ε/2) hδ)).2 (b/2) (by positivity)
    filter_upwards [hsmall] with d hd
    have h := hbound (b*ε/2) hδ d
    have he : (b*ε/2)/ε = b/2 := by field_simp
    rw [he] at h
    linarith

/-- The all-exponent BM interface transfers whenever the exact probability
small-slack comparison holds.  This separates the elementary limit argument
from the finite-sample Gaussian restriction theorem. -/
theorem BMminRiskAllR_of_probability_comparison
    (n N : ℕ → ℕ) (lo hi : ℝ)
    (hbound : ∀ d (r : ℝ), 1 ≤ r → r < 4/3 → ∀ ε > 0, ∀ δ > 0,
      (BMBoxRiskAssembly.coordinateSampleLaw d (n d)).real
        {x | ε < BMBoxRiskAssembly.minFittingRisk d (n d) x lo hi r} ≤
      (BMBoxRiskAssembly.coordinateSampleLaw d (N d)).real
        {x | δ < BMBoxRiskAssembly.minFittingRisk d (N d) x lo hi r} + δ/ε)
    (hN : BMBoxRiskAssembly.BMminRiskAllR N lo hi) :
    BMBoxRiskAssembly.BMminRiskAllR n lo hi := by
  intro r hr hrq ε hε
  apply tendsto_zero_of_arbitrarily_small_slack hε
    (fun d => measureReal_nonneg) (fun δ hδ => hN r hr hrq δ hδ)
  exact fun δ hδ d => hbound d r hr hrq ε hε δ hδ

/-- Actual Gaussian smaller-sample risk inherits the same fixed-box all-r
limit from every pointwise dominating sample sequence.  No lower aspect
ratio is required for the original sequence. -/
theorem BMminRiskAllR_of_dominating
    (n N : ℕ → ℕ) (hn : ∀ d, 0 < n d) (hdom : ∀ d, n d ≤ N d)
    {lo hi : ℝ} (hlohi : lo ≤ hi)
    (hN : BMBoxRiskAssembly.BMminRiskAllR N lo hi) :
    BMBoxRiskAssembly.BMminRiskAllR n lo hi := by
  apply BMminRiskAllR_of_probability_comparison n N lo hi ?_ hN
  intro d r hr hrq ε hε δ hδ
  exact minRisk_probability_le (hn d) (hdom d) hlohi (by linarith) hε hδ.le

#print axioms BMminRiskAllR_of_dominating
#print axioms tendsto_zero_of_arbitrarily_small_slack
#print axioms BMminRiskAllR_of_probability_comparison
end BMCyclicRiskRestriction
