import CappedSimplex
import InverseQuadratic

noncomputable section
open Finset

namespace GaussianEllipsoid.CappedSimplex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem round_two_direction {a b : ℝ} {w : ι → ℝ} (hw : w ∈ slice a b)
    {i j : ι} (hij : i ≠ j) (hi : i ∈ interior a w) (hj : j ∈ interior a w) :
    ∃ tp tm : ℝ, ∃ wp wm : ι → ℝ, ∃ p q : ℝ,
      wp = transfer w i j tp ∧ wm = transfer w i j tm ∧
      wp ∈ slice a b ∧ wm ∈ slice a b ∧
      0 < p ∧ 0 < q ∧ p + q = 1 ∧ w = p • wp + q • wm ∧
      (interior a wp).card < (interior a w).card ∧
      (interior a wm).card < (interior a w).card := by
  let α := min (a - w i) (w j)
  let β := min (w i) (a - w j)
  have hi' := mem_interior.mp hi
  have hj' := mem_interior.mp hj
  have ha : 0 < α := lt_min (sub_pos.mpr hi'.2) hj'.1
  have hb : 0 < β := lt_min hi'.1 (sub_pos.mpr hj'.2)
  have hαi : α ≤ a - w i := min_le_left _ _
  have hαj : α ≤ w j := min_le_right _ _
  have hβi : β ≤ w i := min_le_left _ _
  have hβj : β ≤ a - w j := min_le_right _ _
  have hsumpos : 0 < α + β := add_pos ha hb
  let wp := transfer w i j α
  let wm := transfer w i j (-β)
  have hp : wp ∈ slice a b := by
    refine ⟨?_, by simpa [wp] using hw.2⟩
    intro k
    by_cases hki : k = i
    · subst k
      simp only [wp, transfer_self_left w hij]
      constructor <;> linarith
    by_cases hkj : k = j
    · subst k
      simp only [wp, transfer_self_right w hij]
      constructor <;> linarith
    simpa [wp, transfer_other w hki hkj α] using hw.1 k
  have hm : wm ∈ slice a b := by
    refine ⟨?_, by simpa [wm] using hw.2⟩
    intro k
    by_cases hki : k = i
    · subst k
      simp only [wm, transfer_self_left w hij]
      constructor <;> linarith
    by_cases hkj : k = j
    · subst k
      simp only [wm, transfer_self_right w hij]
      constructor <;> linarith
    simpa [wm, transfer_other w hki hkj (-β)] using hw.1 k
  have hp_end : i ∉ interior a wp ∨ j ∉ interior a wp := by
    rcases le_total (a - w i) (w j) with h | h
    · left
      have he : α = a - w i := min_eq_left h
      simp [mem_interior, wp, transfer_self_left w hij, he]
    · right
      have he : α = w j := min_eq_right h
      simp [mem_interior, wp, transfer_self_right w hij, he]
  have hm_end : i ∉ interior a wm ∨ j ∉ interior a wm := by
    rcases le_total (w i) (a - w j) with h | h
    · left
      have he : β = w i := min_eq_left h
      simp [mem_interior, wm, transfer_self_left w hij, he]
    · right
      have he : β = a - w j := min_eq_right h
      simp [mem_interior, wm, transfer_self_right w hij, he]
  refine ⟨α, -β, wp, wm, β / (α + β), α / (α + β), rfl, rfl, hp, hm,
    div_pos hb hsumpos, div_pos ha hsumpos, ?_, ?_,
    interior_transfer_card_lt hi hj α hp_end,
    interior_transfer_card_lt hi hj (-β) hm_end⟩
  · field_simp
    ring
  · funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wp, wm, transfer]
    split_ifs <;> field_simp <;> ring




/-- The only convexity needed by capped rounding is along coordinate transfers. -/
def PairwiseConvex (a b : ℝ) (F : (ι → ℝ) → ℝ) : Prop :=
  ∀ w ∈ slice a b, ∀ i j : ι, i ≠ j →
    ConvexOn ℝ {t : ℝ | transfer w i j t ∈ slice a b}
      (fun t => F (transfer w i j t))

/-- Pairwise transfer convexity suffices for the finite capped rounding engine. -/
theorem exists_almost_vertex_ge_of_pairwise (a b : ℝ) (F : (ι → ℝ) → ℝ)
    (hF : PairwiseConvex a b F) {w : ι → ℝ} (hw : w ∈ slice a b) :
    ∃ v ∈ slice a b, F w ≤ F v ∧ (interior a v).card ≤ 1 := by
  suffices h : ∀ k : ℕ, ∀ w : ι → ℝ, (interior a w).card = k →
      w ∈ slice a b → ∃ v ∈ slice a b, F w ≤ F v ∧ (interior a v).card ≤ 1 from
    h _ w rfl hw
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro w hcard hw
    by_cases hk : k ≤ 1
    · exact ⟨w, hw, le_rfl, hcard ▸ hk⟩
    have htwo : 1 < (interior a w).card := by omega
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp htwo
    obtain ⟨tp, tm, wp, wm, p, q, hwp, hwm, hp, hm, hpp, hqp, hpq,
      hw_eq, hpc, hmc⟩ := round_two_direction hw hij hi hj
    have hzero : p * tp + q * tm = 0 := by
      have hcoord := congrFun hw_eq i
      rw [hwp, hwm] at hcoord
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        transfer_self_left w hij] at hcoord
      have hwprod := congrArg (fun z : ℝ => z * w i) hpq
      simp only [mul_add, add_mul, one_mul] at hcoord hwprod
      linarith only [hcoord, hwprod]
    have hmax : F w ≤ max (F wp) (F wm) := by
      have hline := hF w hw i j hij
      have htp : tp ∈ {t : ℝ | transfer w i j t ∈ slice a b} := by
        change transfer w i j tp ∈ slice a b
        rw [← hwp]
        exact hp
      have htm : tm ∈ {t : ℝ | transfer w i j t ∈ slice a b} := by
        change transfer w i j tm ∈ slice a b
        rw [← hwm]
        exact hm
      have h := hline.le_on_segment' htp htm (le_of_lt hpp) (le_of_lt hqp) hpq
      have htzero : transfer w i j 0 = w := by ext k; simp [transfer]
      simpa only [smul_eq_mul, hzero, htzero, ← hwp, ← hwm] using h
    rcases le_max_iff.mp hmax with hpF | hmF
    · obtain ⟨v, hv, hFv, hvc⟩ := ih _ (by omega) wp rfl hp
      exact ⟨v, hv, hpF.trans hFv, hvc⟩
    · obtain ⟨v, hv, hFv, hvc⟩ := ih _ (by omega) wm rfl hm
      exact ⟨v, hv, hmF.trans hFv, hvc⟩

/-- The endpoint capped-simplex theorem requires only pairwise convexity. -/
theorem exists_reciprocal_cap_subset_ge_of_pairwise (m : ℕ) (hm : 0 < m)
    (F : (ι → ℝ) → ℝ) (hF : PairwiseConvex ((m : ℝ)⁻¹) 1 F)
    {w : ι → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1) :
    ∃ S : Finset ι, S.card = m ∧
      F w ≤ F (fun i => if i ∈ S then (m : ℝ)⁻¹ else 0) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmul : (m : ℝ) * (m : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hmR)
  obtain ⟨v, hv, hFv, hc⟩ := exists_almost_vertex_ge_of_pairwise _ _ F hF hw
  have hvertex := almost_vertex_is_vertex (inv_pos.mpr hmR) m
    (by simpa [hmul] using hv) hc
  let S : Finset ι := Finset.univ.filter (fun i => v i = (m : ℝ)⁻¹)
  have ha : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  have heq : v = fun i => if i ∈ S then (m : ℝ)⁻¹ else 0 := by
    funext i
    rcases hvertex i with hz | ha'
    · simp [S, hz, ne_of_gt ha, (ne_of_gt ha).symm]
    · simp [S, ha']
  have hcard : S.card = m := by
    have hs : (S.card : ℝ) * (m : ℝ)⁻¹ = (m : ℝ) * (m : ℝ)⁻¹ := by
      simpa [heq, hmul] using hv.2
    have hcast : (S.card : ℝ) = (m : ℝ) :=
      (mul_right_cancel₀ (ne_of_gt ha)) hs
    exact_mod_cast hcast
  exact ⟨S, hcard, heq ▸ hFv⟩

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.exists_reciprocal_cap_subset_ge_of_pairwise
