import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

noncomputable section
open Finset

namespace GaussianEllipsoid.CappedSimplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Move mass from coordinate `j` to coordinate `i`. -/
def transfer (w : ι → ℝ) (i j : ι) (t : ℝ) : ι → ℝ :=
  fun k => w k + (if k = i then t else 0) - (if k = j then t else 0)

/-- A slice of a coordinate cube with a fixed sum. -/
def slice (a b : ℝ) : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i ∧ w i ≤ a) ∧ ∑ i, w i = b}

/-- Coordinates strictly between the two cap endpoints. -/
def interior (a : ℝ) (w : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < w i ∧ w i < a)

@[simp] theorem mem_interior {a : ℝ} {w : ι → ℝ} {i : ι} :
    i ∈ interior a w ↔ 0 < w i ∧ w i < a := by
  simp [interior]

@[simp] theorem transfer_self_left (w : ι → ℝ) {i j : ι} (hij : i ≠ j) (t : ℝ) :
    transfer w i j t i = w i + t := by simp [transfer, hij]

@[simp] theorem transfer_self_right (w : ι → ℝ) {i j : ι} (hij : i ≠ j) (t : ℝ) :
    transfer w i j t j = w j - t := by simp [transfer, hij.symm]

theorem transfer_other (w : ι → ℝ) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j) (t : ℝ) :
    transfer w i j t k = w k := by simp [transfer, hki, hkj]

@[simp] theorem sum_transfer (w : ι → ℝ) (i j : ι) (t : ℝ) :
    ∑ k, transfer w i j t k = ∑ k, w k := by
  simp [transfer, Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem interior_transfer_subset {a : ℝ} {w : ι → ℝ} {i j : ι}
    (hi : i ∈ interior a w) (hj : j ∈ interior a w) (t : ℝ) :
    interior a (transfer w i j t) ⊆ interior a w := by
  intro k hk
  by_cases hki : k = i
  · simpa [hki] using hi
  by_cases hkj : k = j
  · simpa [hkj] using hj
  simpa [mem_interior, transfer_other w hki hkj t] using hk

theorem interior_transfer_card_lt {a : ℝ} {w : ι → ℝ} {i j : ι}
    (hi : i ∈ interior a w) (hj : j ∈ interior a w) (t : ℝ)
    (hend : i ∉ interior a (transfer w i j t) ∨
      j ∉ interior a (transfer w i j t)) :
    (interior a (transfer w i j t)).card < (interior a w).card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨interior_transfer_subset hi hj t, ?_⟩
  intro heq
  rcases hend with h | h
  · exact h (heq ▸ hi)
  · exact h (heq ▸ hj)

/-- The two endpoints produced by moving as far as possible in either direction
remain in the slice, are strictly less fractional, and average to the original. -/
theorem round_two {a b : ℝ} {w : ι → ℝ} (hw : w ∈ slice a b)
    {i j : ι} (hij : i ≠ j) (hi : i ∈ interior a w) (hj : j ∈ interior a w) :
    ∃ wp wm : ι → ℝ, ∃ p q : ℝ,
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
  refine ⟨wp, wm, β / (α + β), α / (α + β), hp, hm,
    div_pos hb hsumpos, div_pos ha hsumpos, ?_, ?_,
    interior_transfer_card_lt hi hj α hp_end,
    interior_transfer_card_lt hi hj (-β) hm_end⟩
  · field_simp
    ring
  · funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, wp, wm, transfer]
    split_ifs <;> field_simp <;> ring



/-- Every point of a capped slice has a point at least as good for a convex
function, with at most one coordinate strictly between zero and the cap.
This uses finite rounding, with no majorization theorem or compact maximum. -/
theorem exists_almost_vertex_ge (a b : ℝ) (F : (ι → ℝ) → ℝ)
    (hF : ConvexOn ℝ (slice a b) F) {w : ι → ℝ} (hw : w ∈ slice a b) :
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
    obtain ⟨wp, wm, p, q, hp, hm, hpp, hqp, hpq, hw_eq, hpc, hmc⟩ :=
      round_two hw hij hi hj
    have hmax : F w ≤ max (F wp) (F wm) := by
      rw [hw_eq]
      exact hF.le_on_segment' hp hm (le_of_lt hpp) (le_of_lt hqp) hpq
    rcases le_max_iff.mp hmax with hpF | hmF
    · obtain ⟨v, hv, hFv, hvc⟩ := ih _ (by omega) wp rfl hp
      exact ⟨v, hv, hpF.trans hFv, hvc⟩
    · obtain ⟨v, hv, hFv, hvc⟩ := ih _ (by omega) wm rfl hm
      exact ⟨v, hv, hmF.trans hFv, hvc⟩



/-- At integral multiples of the cap, a point with at most one fractional
coordinate has no fractional coordinates at all. -/
theorem almost_vertex_is_vertex {a : ℝ} (ha : 0 < a) (m : ℕ) {v : ι → ℝ}
    (hv : v ∈ slice a ((m : ℝ) * a)) (hc : (interior a v).card ≤ 1) :
    ∀ i, v i = 0 ∨ v i = a := by
  intro i
  by_contra hbad
  push_neg at hbad
  have hii : i ∈ interior a v :=
    mem_interior.mpr ⟨lt_of_le_of_ne (hv.1 i).1 hbad.1.symm,
      lt_of_le_of_ne (hv.1 i).2 hbad.2⟩
  have hothers : ∀ j, j ≠ i → v j = 0 ∨ v j = a := by
    intro j hji
    by_contra hbadj
    push_neg at hbadj
    have hjj : j ∈ interior a v :=
      mem_interior.mpr ⟨lt_of_le_of_ne (hv.1 j).1 hbadj.1.symm,
        lt_of_le_of_ne (hv.1 j).2 hbadj.2⟩
    exact hji ((Finset.card_le_one.mp hc) j hjj i hii)
  let S : Finset ι := Finset.univ.filter (fun j => v j = a)
  have hiS : i ∉ S := by simp [S, hbad.2]
  have heq : ∀ j, v j = (if j = i then v i else 0) + (if j ∈ S then a else 0) := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [hiS]
    rcases hothers j hji with hzero | hcap
    · have hjS : j ∉ S := by simp [S, hzero, ne_of_gt ha, (ne_of_gt ha).symm]
      simp [hji, hjS, hzero]
    · have hjS : j ∈ S := by simp [S, hcap]
      simp [hji, hjS, hcap]
  have hsum : ∑ j, v j = v i + (S.card : ℝ) * a := by
    calc
      (∑ j, v j) = ∑ j, ((if j = i then v i else 0) +
          (if j ∈ S then a else 0)) := Finset.sum_congr rfl (fun j _ => heq j)
      _ = v i + (S.card : ℝ) * a := by simp [Finset.sum_add_distrib]
  have hii' := mem_interior.mp hii
  have hkm : (S.card : ℝ) < (m : ℝ) := by
    apply (mul_lt_mul_iff_left₀ ha).mp
    rw [← hv.2, hsum]
    linarith
  have hmk : (m : ℝ) < (S.card : ℝ) + 1 := by
    apply (mul_lt_mul_iff_left₀ ha).mp
    rw [← hv.2, hsum]
    nlinarith
  have hkmN : S.card < m := by exact_mod_cast hkm
  have hmkN : m < S.card + 1 := by exact_mod_cast hmk
  omega

/-- Convex functions on an integral capped simplex attain a dominating value
at a uniform subset. No permutation invariance or maximizing compactness is
assumed: the suitable subset is supplied by finite rounding. -/
theorem exists_uniform_subset_ge {a : ℝ} (ha : 0 < a) (m : ℕ)
    (F : (ι → ℝ) → ℝ) (hF : ConvexOn ℝ (slice a ((m : ℝ) * a)) F)
    {w : ι → ℝ} (hw : w ∈ slice a ((m : ℝ) * a)) :
    ∃ S : Finset ι, S.card = m ∧ F w ≤ F (fun i => if i ∈ S then a else 0) := by
  obtain ⟨v, hv, hFv, hc⟩ := exists_almost_vertex_ge a ((m : ℝ) * a) F hF hw
  have hvertex := almost_vertex_is_vertex ha m hv hc
  let S : Finset ι := Finset.univ.filter (fun i => v i = a)
  have heq : v = fun i => if i ∈ S then a else 0 := by
    funext i
    rcases hvertex i with hz | ha'
    · simp [S, hz, ne_of_gt ha, (ne_of_gt ha).symm]
    · simp [S, ha']
  have hcard : S.card = m := by
    have hs : (S.card : ℝ) * a = (m : ℝ) * a := by
      simpa [heq] using hv.2
    have hcast : (S.card : ℝ) = (m : ℝ) :=
      (mul_right_cancel₀ (ne_of_gt ha)) hs
    exact_mod_cast hcast
  exact ⟨S, hcard, heq ▸ hFv⟩

/-- Endpoint form used for the determinant moment: weights bounded by `1/m`
with sum one can be rounded to exactly `m` equal nonzero weights without
reducing any convex objective. -/
theorem exists_reciprocal_cap_subset_ge (m : ℕ) (hm : 0 < m)
    (F : (ι → ℝ) → ℝ) (hF : ConvexOn ℝ (slice ((m : ℝ)⁻¹) 1) F)
    {w : ι → ℝ} (hw : w ∈ slice ((m : ℝ)⁻¹) 1) :
    ∃ S : Finset ι, S.card = m ∧
      F w ≤ F (fun i => if i ∈ S then (m : ℝ)⁻¹ else 0) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmul : (m : ℝ) * (m : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hmR)
  exact exists_uniform_subset_ge (inv_pos.mpr hmR) m F
    (by simpa [hmul] using hF) (by simpa [hmul] using hw)

end GaussianEllipsoid.CappedSimplex

#print axioms GaussianEllipsoid.CappedSimplex.round_two
#print axioms GaussianEllipsoid.CappedSimplex.exists_almost_vertex_ge
#print axioms GaussianEllipsoid.CappedSimplex.almost_vertex_is_vertex
#print axioms GaussianEllipsoid.CappedSimplex.exists_uniform_subset_ge
#print axioms GaussianEllipsoid.CappedSimplex.exists_reciprocal_cap_subset_ge

