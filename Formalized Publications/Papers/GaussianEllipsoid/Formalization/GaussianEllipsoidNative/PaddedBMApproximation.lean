import CyclicRiskLimit
import QuadraticSamplePadding

/-!
# Removing a lower aspect assumption from the original BM interface

The source laws and the real-power infimum risks are the actual Gaussian
objects throughout.  The original sample sequence has only positive counts
and the strict ENNReal limsup threshold.  A dominating padded sequence is
used internally; no positive lower aspect assumption is added to the target.

The analytic input below is explicitly conditional.  This file does not
prove Gaussian Gordon feasibility.
-/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace BMCyclicRiskRestriction

/-- The standalone exact-risk counterpart of the original
`GaussianEllipsoid.bmApproximateFitting`, with the same quantifier order,
strict limsup threshold, actual iid Gaussian law, and literal real-power
infimum risk. -/
def BMApproximateFitting : Prop :=
  ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
    limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMBoxRiskAssembly.BMminRiskAllR n lo hi

/-- A positive-aspect theorem suffices as an analytic interface.  Its
endpoints may depend on the sample sequence, but must be chosen before r. -/
def ProportionalBMApproximateFitting : Prop :=
  ∀ (N : ℕ → ℕ), (∀ d, 0 < N d) → ∀ a : ℝ, 0 < a → a < 1/4 →
    Tendsto (fun d => (N d:ℝ)/(d:ℝ)^2) atTop (nhds a) →
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMBoxRiskAssembly.BMminRiskAllR N lo hi

/-- Every convergent quadratic sample ratio admits a global upper window on
positive dimensions.  No restriction on a finite prefix is needed. -/
theorem exists_global_quadratic_upper_bound_of_ratio_tendsto
    (N : ℕ → ℕ) {a : ℝ}
    (hlim : Tendsto (fun d => (N d:ℝ)/(d:ℝ)^2) atTop (nhds a)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ d : ℕ, 0 < d → (N d:ℝ) ≤ A*(d:ℝ)^2 := by
  apply GaussianEllipsoidFinalPassage.exists_global_quadratic_upper_bound N (a+1)
  have he : ∀ᶠ d in atTop, (N d:ℝ)/(d:ℝ)^2 < a+1 :=
    (tendsto_order.1 hlim).2 (a+1) (by linarith)
  filter_upwards [he, eventually_gt_atTop (0:ℕ)] with d hd hdim
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hdim
  exact ((div_lt_iff₀ (sq_pos_of_pos hdR)).1 hd).le

/-- Positive-aspect BM bounds and an exact same-box domination implication
suffice for the original strict-limsup interface. -/
theorem BMApproximateFitting_of_proportional_and_domination
    (hproportional : ProportionalBMApproximateFitting)
    (hrestrict : ∀ (n N : ℕ → ℕ), (∀ d, 0 < n d) → (∀ d, n d ≤ N d) →
      ∀ lo hi : ℝ, lo ≤ hi → BMBoxRiskAssembly.BMminRiskAllR N lo hi →
        BMBoxRiskAssembly.BMminRiskAllR n lo hi) :
    BMApproximateFitting := by
  intro n hn haspect
  obtain ⟨a,ha,haq,N,hdom,hN,hlim,hsub,hlower⟩ :=
    GaussianEllipsoidFinalPassage.exists_dominating_subcritical_sequence n hn haspect
  obtain ⟨lo,hi,hlo,hlohi,hrisk⟩ := hproportional N hN a ha haq hlim
  exact ⟨lo,hi,hlo,hlohi,hrestrict n N hn hdom lo hi hlohi hrisk⟩

/-- Full strict-limsup BM approximation follows from only its positive-aspect
version: the cyclic Gaussian restriction theorem discharges domination. -/
theorem BMApproximateFitting_of_proportional
    (hproportional : ProportionalBMApproximateFitting) :
    BMApproximateFitting := by
  apply BMApproximateFitting_of_proportional_and_domination hproportional
  intro n N hn hdom lo hi hlohi hN
  exact BMminRiskAllR_of_dominating n N hn hdom hlohi hN

#print axioms exists_global_quadratic_upper_bound_of_ratio_tendsto
#print axioms BMApproximateFitting_of_proportional_and_domination
#print axioms BMApproximateFitting_of_proportional
end BMCyclicRiskRestriction
