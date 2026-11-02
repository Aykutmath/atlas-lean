import AHHEdgeAsymptotics

/-! Exact scalar passage from a power-moment inequality to the finite root bound
and then the sharp upper edge.  Every probability input is an explicit hypothesis. -/
noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics
namespace AHH

/-- Taking a positive-order root preserves the exact dimension and fixed-point
factors. Zero dimension or zero edge is permitted by the scalar lemma. -/
theorem scalar_root_bound {μ d R L : ℝ} (hμ : 0 ≤ μ) (hd : 0 ≤ d)
    (hR : 0 ≤ R) (hL : 0 ≤ L) {m : ℕ} (hm : 0 < m)
    (hpow : μ ^ m ≤ d * (R * L ^ m)) :
    μ ≤ (d * R) ^ (1 / (m : ℝ)) * L := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hroot (a : ℝ) (ha : 0 ≤ a) : (a ^ m) ^ (1 / (m : ℝ)) = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div_cancel hm', Real.rpow_one]
  have ht := Real.rpow_le_rpow (pow_nonneg hμ m) hpow
    (by positivity : 0 ≤ 1 / (m : ℝ))
  rw [hroot μ hμ] at ht
  have hr : (d * (R * L ^ m)) ^ (1 / (m : ℝ)) =
      (d * R) ^ (1 / (m : ℝ)) * L := by
    rw [← mul_assoc, Real.mul_rpow (mul_nonneg hd hR) (pow_nonneg hL m), hroot L hL]
  exact ht.trans_eq hr

/-- A normalized-moment upper bound and a Jensen/trace power inequality give
the exact finite AHH norm bound. -/
theorem expectation_le_edge_of_moment {μ d e A B : ℝ} (hμ : 0 ≤ μ) (hd : 0 ≤ d)
    (hA : 0 < A) (hB : 0 ≤ B) {m : ℕ} (hm : 0 < m)
    (hpower : μ ^ m ≤ d * e) (hmoment : e ≤ edgeR A B * edgeL A B ^ m) :
    μ ≤ (d * edgeR A B) ^ (1 / (m : ℝ)) * edgeL A B := by
  exact scalar_root_bound hμ hd (le_trans zero_le_one (edgeR_ge_one _ _))
    (edgeL_pos hA hB).le hm (hpower.trans (mul_le_mul_of_nonneg_left hmoment hd))

/-- The scalar recurrence and a separately supplied power-moment inequality
imply the finite root bound at an arbitrary positive order. -/
theorem expectation_le_edge_of_recurrence (e : ℕ → ℝ) (he : ∀ j, 0 ≤ e j)
    (hzero : e 0 = 1) {μ d A B : ℝ} (hμ : 0 ≤ μ) (hd : 0 ≤ d)
    (hA : 0 < A) (hB : 0 ≤ B) {m : ℕ} (hm : 0 < m)
    (hrec : ∀ j < m, e (j + 1) ≤ B * e j + A * ∑ i ∈ Finset.range j, e i * e (j - i))
    (hpower : μ ^ m ≤ d * e m) :
    μ ≤ (d * edgeR A B) ^ (1 / (m : ℝ)) * edgeL A B :=
  expectation_le_edge_of_moment hμ hd hA hB hm hpower (moment_le_edge e he hzero hA hB m hrec)

/-- Natural dimension and sample counts, exact chosen moment order, full square
dimension factor, and every finite recurrence endpoint remain explicit. -/
theorem expectation_le_edgeFiniteBound_of_recurrence (p : ℕ → ℕ) (μ : ℕ → ℝ)
    (e : ℕ → ℕ → ℝ)
    (hμ : ∀ h : ℕ, 1 ≤ h → 0 ≤ μ h)
    (he : ∀ h : ℕ, 1 ≤ h → ∀ j, 0 ≤ e h j)
    (hzero : ∀ h : ℕ, 1 ≤ h → e h 0 = 1)
    (hrec : ∀ h : ℕ, 1 ≤ h → ∀ j < edgeMomentOrder h,
      e h (j + 1) ≤ edgeB p h * e h j +
        edgeA h * ∑ i ∈ Finset.range j, e h i * e h (j - i))
    (hpower : ∀ h : ℕ, 1 ≤ h →
      μ h ^ edgeMomentOrder h ≤ (h : ℝ) ^ 2 * e h (edgeMomentOrder h)) :
    ∀ h : ℕ, 1 ≤ h → μ h ≤ edgeFiniteBound p h := by
  intro h hh
  exact expectation_le_edge_of_recurrence (e h) (he h hh) (hzero h hh)
    (hμ h hh) (sq_nonneg _) (edgeA_pos h) (edgeB_nonneg p h) (edgeMomentOrder_pos h)
    (hrec h hh) (hpower h hh)

/-- Complete analytic recurrence-to-upper-edge implication. This endpoint still
requires an actual recurrence and power-moment inequality for the chosen `μ,e`;
it does not assert that a probabilistic model satisfies either hypothesis. -/
theorem expectation_upper_edge_o1_of_recurrence (p : ℕ → ℕ) (μ : ℕ → ℝ)
    (e : ℕ → ℕ → ℝ) {x : ℝ} (hx : 0 < x)
    (hp : Tendsto (fun h : ℕ => (p h : ℝ) / (h : ℝ) ^ 2) atTop (𝓝 x))
    (hμ : ∀ h : ℕ, 1 ≤ h → 0 ≤ μ h)
    (he : ∀ h : ℕ, 1 ≤ h → ∀ j, 0 ≤ e h j)
    (hzero : ∀ h : ℕ, 1 ≤ h → e h 0 = 1)
    (hrec : ∀ h : ℕ, 1 ≤ h → ∀ j < edgeMomentOrder h,
      e h (j + 1) ≤ edgeB p h * e h j +
        edgeA h * ∑ i ∈ Finset.range j, e h i * e h (j - i))
    (hpower : ∀ h : ℕ, 1 ≤ h →
      μ h ^ edgeMomentOrder h ≤ (h : ℝ) ^ 2 * e h (edgeMomentOrder h)) :
    (∀ h, 0 ≤ edgeError p x h) ∧
    edgeError p x =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
    (∀ h : ℕ, 1 ≤ h → μ h ≤ (1 + Real.sqrt x) ^ 2 + edgeError p x h) :=
  expectation_upper_edge_o1 p μ hx hp
    (expectation_le_edgeFiniteBound_of_recurrence p μ e hμ he hzero hrec hpower)

end AHH
