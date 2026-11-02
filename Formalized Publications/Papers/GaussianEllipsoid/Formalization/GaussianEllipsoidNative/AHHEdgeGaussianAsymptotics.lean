import AHHEdgeAsymptotics

/-! Optional analytic bridge retaining the Gaussian inflation factor from the
Haar-first finite comparison.  The direct Gaussian recurrence can instead use
`AHHEdgeAsymptotics` without this factor. -/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace AHH

/-- Exact Gaussian inflation in the Haar-first comparison route. -/
def edgeGaussianFactor (h : ℕ) : ℝ :=
  Real.exp (((edgeMomentOrder h : ℝ) - 1) / (h : ℝ))

/-- Finite Gaussian upper bound, including every displayed factor. -/
def edgeGaussianFiniteBound (p : ℕ → ℕ) (h : ℕ) : ℝ :=
  edgeGaussianFactor h * edgeFiniteBound p h

theorem edgeMomentOrder_div_dimension_tendsto :
    Tendsto (fun h : ℕ => (edgeMomentOrder h : ℝ) / (h : ℝ)) atTop (𝓝 0) := by
  have hn : Tendsto (fun h : ℕ => (h : ℝ) ^ (-(11 / 12 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 11 / 12)).comp tendsto_natCast_atTop_atTop
  have ht := edgeMomentOrder_div_root_tendsto.mul hn
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with h hh
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  have hr : (h : ℝ) ^ (1 / 12 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh' _)
  rw [show (-(11 / 12 : ℝ)) = (1 / 12 : ℝ) - 1 by norm_num,
    Real.rpow_sub_one (ne_of_gt hh')]
  field_simp

theorem edgeGaussianFactor_tendsto : Tendsto edgeGaussianFactor atTop (𝓝 1) := by
  have hi : Tendsto (fun h : ℕ => (1 : ℝ) / (h : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : Tendsto (fun h : ℕ => ((edgeMomentOrder h : ℝ) - 1) / (h : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_div, sub_self] using edgeMomentOrder_div_dimension_tendsto.sub hi
  change Tendsto (fun h : ℕ => Real.exp (((edgeMomentOrder h : ℝ) - 1) / (h : ℝ))) atTop (𝓝 1)
  simpa only [Function.comp_def] using
    Real.tendsto_exp_nhds_zero_nhds_one.comp he

theorem edgeGaussianFiniteBound_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (edgeGaussianFiniteBound p) atTop (𝓝 ((1 + Real.sqrt x) ^ 2)) := by
  change Tendsto (fun h : ℕ => edgeGaussianFactor h * edgeFiniteBound p h)
    atTop (𝓝 ((1 + Real.sqrt x) ^ 2))
  simpa only [one_mul] using edgeGaussianFactor_tendsto.mul (edgeFiniteBound_tendsto p hp)

/-- An explicit nonnegative Gaussian-route error. -/
def edgeGaussianError (p : ℕ → ℕ) (x : ℝ) (h : ℕ) : ℝ :=
  |edgeGaussianFiniteBound p h - (1 + Real.sqrt x) ^ 2|

theorem edgeGaussianError_nonneg (p : ℕ → ℕ) (x : ℝ) (h : ℕ) :
    0 ≤ edgeGaussianError p x h := abs_nonneg _

theorem edgeGaussianError_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (edgeGaussianError p x) atTop (𝓝 0) := by
  have ht : Tendsto (fun h : ℕ => |edgeGaussianFiniteBound p h - (1 + Real.sqrt x) ^ 2|)
      atTop (𝓝 |(1 + Real.sqrt x) ^ 2 - (1 + Real.sqrt x) ^ 2|) :=
    ((edgeGaussianFiniteBound_tendsto p hp).sub
      (tendsto_const_nhds (x := ((1 + Real.sqrt x) ^ 2)))).abs
  change Tendsto (fun h : ℕ => |edgeGaussianFiniteBound p h - (1 + Real.sqrt x) ^ 2|) atTop (𝓝 0)
  simpa only [sub_self, abs_zero] using ht

/-- Optional paper-facing bridge for a supplied finite bound with the additional
Gaussian factor.  No stochastic finite bound is asserted by this theorem. -/
theorem gaussian_expectation_upper_edge_o1 (p : ℕ → ℕ) (μ : ℕ → ℝ) {x : ℝ} (_hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x))
    (hfinite : ∀ h : ℕ, 1 ≤ h → μ h ≤ edgeGaussianFiniteBound p h) :
    (∀ h, 0 ≤ edgeGaussianError p x h) ∧
    edgeGaussianError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ h : ℕ, 1 ≤ h → μ h ≤ (1 + Real.sqrt x) ^ 2 + edgeGaussianError p x h) := by
  refine ⟨edgeGaussianError_nonneg p x,
    (Asymptotics.isLittleO_one_iff ℝ).2 (edgeGaussianError_tendsto p hp), ?_⟩
  intro h hh
  have he := le_abs_self (edgeGaussianFiniteBound p h - (1 + Real.sqrt x) ^ 2)
  have hf := hfinite h hh
  change μ h ≤ (1 + Real.sqrt x) ^ 2 + |edgeGaussianFiniteBound p h - (1 + Real.sqrt x) ^ 2|
  linarith

end AHH
