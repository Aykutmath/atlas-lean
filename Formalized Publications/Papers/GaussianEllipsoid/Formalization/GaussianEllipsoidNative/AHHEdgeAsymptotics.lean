import AHHGeneratingBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Exact analytic bridge to the AHH upper expectation edge

The moment order is `max 1 ⌊h^(1/12)⌋₊`.  All constants in the finite upper
bound are retained.  This module is an analytic implication: it does not claim
to establish the probability-theoretic finite bound supplied as its hypothesis.
-/
noncomputable section
open Filter Asymptotics
open scoped Topology
namespace AHH

/-- Positive integer moment order used in the asymptotic passage. -/
def edgeMomentOrder (h : ℕ) : ℕ := max 1 ⌊(h : ℝ) ^ (1 / 12 : ℝ)⌋₊

/-- Exact coefficient of the convolution in the finite recurrence. -/
def edgeA (h : ℕ) : ℝ := 1 + 1 / Real.sqrt (h : ℝ)

/-- Exact coefficient of the linear term in the finite recurrence. -/
def edgeB (p : ℕ → ℕ) (h : ℕ) : ℝ :=
  (p h : ℝ) / (h : ℝ) ^ 2 + 4 * (edgeMomentOrder h : ℝ) ^ 5 / Real.sqrt (h : ℝ)

/-- The finite-dimensional factor before the edge, without asymptotic simplification. -/
def edgePrefactor (p : ℕ → ℕ) (h : ℕ) : ℝ :=
  ((h : ℝ) ^ 2 * edgeR (edgeA h) (edgeB p h)) ^ (1 / (edgeMomentOrder h : ℝ))

/-- Exact scalar upper bound to which the probabilistic estimate is connected. -/
def edgeFiniteBound (p : ℕ → ℕ) (h : ℕ) : ℝ :=
  edgePrefactor p h * edgeL (edgeA h) (edgeB p h)

theorem edgeMomentOrder_pos (h : ℕ) : 0 < edgeMomentOrder h := by
  unfold edgeMomentOrder
  omega

theorem edgeA_pos (h : ℕ) : 0 < edgeA h := by
  unfold edgeA
  positivity

theorem edgeB_nonneg (p : ℕ → ℕ) (h : ℕ) : 0 ≤ edgeB p h := by
  unfold edgeB
  positivity

private theorem nat_real_atTop : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

private theorem root12_atTop :
    Tendsto (fun h : ℕ => (h : ℝ) ^ (1 / 12 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp nat_real_atTop

private theorem eventually_edgeMomentOrder_eq_floor :
    ∀ᶠ h : ℕ in atTop, edgeMomentOrder h = ⌊(h : ℝ) ^ (1 / 12 : ℝ)⌋₊ := by
  filter_upwards [root12_atTop.eventually (eventually_ge_atTop 1)] with h hh
  exact max_eq_right (Nat.le_floor (by simpa using hh))

/-- The floor and the positive cutoff do not alter the leading scale. -/
theorem edgeMomentOrder_div_root_tendsto :
    Tendsto (fun h : ℕ => (edgeMomentOrder h : ℝ) / (h : ℝ) ^ (1 / 12 : ℝ))
      atTop (𝓝 1) := by
  apply (tendsto_nat_floor_div_atTop.comp root12_atTop).congr'
  filter_upwards [eventually_edgeMomentOrder_eq_floor] with h hh
  simp only [Function.comp_apply, hh]

theorem edgeMomentOrder_atTop : Tendsto edgeMomentOrder atTop atTop := by
  unfold edgeMomentOrder
  apply tendsto_atTop_mono (fun h : ℕ => le_max_right 1 ⌊(h : ℝ) ^ (1 / 12 : ℝ)⌋₊)
  exact tendsto_nat_floor_atTop.comp root12_atTop

theorem inv_edgeMomentOrder_tendsto :
    Tendsto (fun h : ℕ => (edgeMomentOrder h : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (nat_real_atTop.comp edgeMomentOrder_atTop)

/-- The degree-five recurrence loss vanishes for the specified moment order. -/
theorem edgeMomentOrder_fifth_div_sqrt_tendsto :
    Tendsto (fun h : ℕ => (edgeMomentOrder h : ℝ) ^ 5 / Real.sqrt (h : ℝ))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun h : ℕ => (h : ℝ) ^ (-(1 / 12 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp nat_real_atTop
  have ht := (edgeMomentOrder_div_root_tendsto.pow 5).mul hn
  simp only [one_pow, one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with h hh
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  have hr : (h : ℝ) ^ (1 / 12 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh' _)
  rw [show (-(1 / 12 : ℝ)) = (1 / 12 : ℝ) * (5 : ℕ) - 1 / 2 by norm_num,
    Real.rpow_sub hh', Real.rpow_mul_natCast hh'.le, ← Real.sqrt_eq_rpow]
  simp only [div_pow]
  field_simp

/-- Exact `A_h → 1`. -/
theorem edgeA_tendsto : Tendsto edgeA atTop (𝓝 1) := by
  have hs : Tendsto (fun h : ℕ => Real.sqrt (h : ℝ)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp nat_real_atTop
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_inv_atTop_zero.comp hs)
  change Tendsto (fun h : ℕ => 1 + 1 / Real.sqrt (h : ℝ)) atTop (𝓝 1)
  simpa only [edgeA, one_div, add_zero, Function.comp_def] using ht

/-- Exact `B_h → x`, with the material constant `4` and fifth power retained. -/
theorem edgeB_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (edgeB p) atTop (𝓝 x) := by
  have ht := hp.add ((tendsto_const_nhds (x := (4 : ℝ))).mul edgeMomentOrder_fifth_div_sqrt_tendsto)
  change Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2 + 4 * (edgeMomentOrder h : ℝ) ^ 5 / Real.sqrt (h : ℝ)) atTop (𝓝 x)
  simpa only [mul_zero, add_zero, mul_div_assoc] using ht

/-- The finite edge itself converges to the paper's sharp upper edge. -/
theorem edgeL_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (fun h => edgeL (edgeA h) (edgeB p h)) atTop (𝓝 ((1 + Real.sqrt x) ^ 2)) := by
  simpa only [edgeL, Real.sqrt_one] using (edgeA_tendsto.sqrt.add (edgeB_tendsto p hp).sqrt).pow 2

/-- The fixed point has the finite positive limit `1 + √x`. -/
theorem edgeR_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (fun h => edgeR (edgeA h) (edgeB p h)) atTop (𝓝 (1 + Real.sqrt x)) := by
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add ((edgeB_tendsto p hp).div edgeA_tendsto one_ne_zero).sqrt
  simpa only [edgeR, div_one, Pi.div_apply] using ht

/-- The logarithmic dimension factor is negligible compared with the moment order. -/
theorem log_div_edgeMomentOrder_tendsto :
    Tendsto (fun h : ℕ => Real.log (h : ℝ) / (edgeMomentOrder h : ℝ)) atTop (𝓝 0) := by
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).tendsto_div_nhds_zero.comp nat_real_atTop
  have ht := hl.div edgeMomentOrder_div_root_tendsto one_ne_zero
  simp only [zero_div] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with h hh
  have hr : (h : ℝ) ^ (1 / 12 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast hh) _)
  simp only [Pi.div_apply, Function.comp_apply]
  field_simp

/-- The exact dimension/fixed-point root factor tends to one. -/
theorem edgePrefactor_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (edgePrefactor p) atTop (𝓝 1) := by
  have hx : 0 < 1 + Real.sqrt x := by positivity
  have hl := ((edgeR_tendsto p hp).log (ne_of_gt hx)).mul inv_edgeMomentOrder_tendsto
  have ht := ((tendsto_const_nhds (x := (2 : ℝ))).mul log_div_edgeMomentOrder_tendsto).add hl
  simp only [mul_zero, add_zero] at ht
  apply (Real.tendsto_exp_nhds_zero_nhds_one.comp ht).congr'
  filter_upwards [eventually_gt_atTop 0] with h hh
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  have hR : 0 < edgeR (edgeA h) (edgeB p h) := lt_of_lt_of_le zero_lt_one (edgeR_ge_one _ _)
  simp only [Function.comp_apply]
  rw [edgePrefactor, Real.rpow_def_of_pos (mul_pos (sq_pos_of_pos hh') hR),
    Real.log_mul (ne_of_gt (sq_pos_of_pos hh')) (ne_of_gt hR), Real.log_pow]
  congr 1
  push_cast
  ring

/-- Convergence of the complete finite upper bound, with no dropped prefactor. -/
theorem edgeFiniteBound_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (edgeFiniteBound p) atTop (𝓝 ((1 + Real.sqrt x) ^ 2)) := by
  change Tendsto (fun h : ℕ => edgePrefactor p h * edgeL (edgeA h) (edgeB p h)) atTop (𝓝 ((1 + Real.sqrt x) ^ 2))
  simpa only [one_mul] using (edgePrefactor_tendsto p hp).mul (edgeL_tendsto p hp)

/-- A fully explicit nonnegative error; this is the paper-facing `o(1)`. -/
def edgeError (p : ℕ → ℕ) (x : ℝ) (h : ℕ) : ℝ :=
  |edgeFiniteBound p h - (1 + Real.sqrt x) ^ 2|

theorem edgeError_nonneg (p : ℕ → ℕ) (x : ℝ) (h : ℕ) : 0 ≤ edgeError p x h :=
  abs_nonneg _

theorem edgeError_tendsto (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    Tendsto (edgeError p x) atTop (𝓝 0) := by
  change Tendsto (fun h : ℕ => |edgeFiniteBound p h - (1 + Real.sqrt x) ^ 2|) atTop (𝓝 0)
  have ht : Tendsto (fun h : ℕ => |edgeFiniteBound p h - (1 + Real.sqrt x) ^ 2|) atTop (𝓝 |(1 + Real.sqrt x) ^ 2 - (1 + Real.sqrt x) ^ 2|) :=
    ((edgeFiniteBound_tendsto p hp).sub (tendsto_const_nhds (x := ((1 + Real.sqrt x) ^ 2)))).abs
  simpa only [sub_self, abs_zero] using ht

theorem edgeError_isLittleO (p : ℕ → ℕ) {x : ℝ}
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x)) :
    edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  (Asymptotics.isLittleO_one_iff ℝ).2 (edgeError_tendsto p hp)

/-- Analytic upper-expectation bridge. The finite probabilistic estimate remains
an explicit input, rather than being concealed in a newly defined moment. -/
theorem expectation_le_edge_add_error (p : ℕ → ℕ) (μ : ℕ → ℝ) (x : ℝ)
    (hfinite : ∀ h : ℕ, 1 ≤ h → μ h ≤ edgeFiniteBound p h) :
    ∀ h : ℕ, 1 ≤ h → μ h ≤ (1 + Real.sqrt x) ^ 2 + edgeError p x h := by
  intro h hh
  have he := le_abs_self (edgeFiniteBound p h - (1 + Real.sqrt x) ^ 2)
  have hf := hfinite h hh
  change μ h ≤ (1 + Real.sqrt x) ^ 2 + |edgeFiniteBound p h - (1 + Real.sqrt x) ^ 2|
  linarith

/-- Paper-facing upper edge plus a specified nonnegative `o(1)` for `x > 0`.
This theorem does not establish the supplied finite bound on `μ`. -/
theorem expectation_upper_edge_o1 (p : ℕ → ℕ) (μ : ℕ → ℝ) {x : ℝ} (_hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x))
    (hfinite : ∀ h : ℕ, 1 ≤ h → μ h ≤ edgeFiniteBound p h) :
    (∀ h, 0 ≤ edgeError p x h) ∧
    edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ h : ℕ, 1 ≤ h → μ h ≤ (1 + Real.sqrt x) ^ 2 + edgeError p x h) :=
  ⟨edgeError_nonneg p x, edgeError_isLittleO p hp, expectation_le_edge_add_error p μ x hfinite⟩

end AHH
