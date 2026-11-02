import CappedPairwise
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section
open Finset
namespace GaussianEllipsoid.CappedSimplex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact cap count and remainder, without assuming the cap is reciprocal-integral. -/
theorem almost_vertex_cap_remainder {a : ℝ} (ha : 0 < a) {v : ι → ℝ}
    (hv : v ∈ slice a 1) (hc : (interior a v).card ≤ 1) :
    let S := Finset.univ.filter (fun i => v i = a)
    S.card = Nat.floor (1 / a) ∧
    ∀ i, v i = 0 ∨ v i = a ∨ v i = 1 - (Nat.floor (1 / a) : ℝ) * a := by
  dsimp only
  let S := Finset.univ.filter (fun i => v i = a)
  have houtside : ∀ i, i ∉ interior a v → v i = 0 ∨ v i = a := by
    intro i hi
    by_contra hh
    push_neg at hh
    exact hi (mem_interior.mpr ⟨lt_of_le_of_ne (hv.1 i).1 hh.1.symm,
      lt_of_le_of_ne (hv.1 i).2 hh.2⟩)
  by_cases hempty : (interior a v) = ∅
  · have hcoord : ∀ i, v i = if i ∈ S then a else 0 := by
      intro i
      rcases houtside i (by simp [hempty]) with hz | he
      · simp [S, hz, ha.ne']
      · simp [S, he]
    have hsum : (S.card : ℝ) * a = 1 := by
      calc
        (S.card : ℝ) * a = ∑ i, (if i ∈ S then a else 0) := by simp
        _ = ∑ i, v i := Finset.sum_congr rfl (fun i _ => (hcoord i).symm)
        _ = 1 := hv.2
    have hfloor : Nat.floor (1 / a) = S.card := by
      have heq : 1 / a = (S.card : ℝ) := (div_eq_iff ha.ne').mpr (by simpa [mul_comm] using hsum.symm)
      rw [heq, Nat.floor_natCast]
    refine ⟨hfloor.symm, ?_⟩
    intro i
    exact (houtside i (by simp [hempty])).imp_right Or.inl
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hj' := mem_interior.mp hj
    have hothers : ∀ i, i ≠ j → v i = 0 ∨ v i = a := by
      intro i hij
      apply houtside
      intro hi
      exact hij ((Finset.card_le_one.mp hc) i hi j hj)
    have hjS : j ∉ S := by simp [S, ne_of_lt hj'.2]
    have hcoord : ∀ i, v i = (if i = j then v j else 0) + (if i ∈ S then a else 0) := by
      intro i
      by_cases hij : i = j
      · subst i; simp [hjS]
      rcases hothers i hij with hz | he
      · simp [S, hz, hij, ha.ne']
      · simp [S, he, hij]
    have hsum : v j + (S.card : ℝ) * a = 1 := by
      calc
        v j + (S.card : ℝ) * a = ∑ i, ((if i = j then v j else 0) + (if i ∈ S then a else 0)) := by simp [Finset.sum_add_distrib]
        _ = ∑ i, v i := Finset.sum_congr rfl (fun i _ => (hcoord i).symm)
        _ = 1 := hv.2
    have hfloor : Nat.floor (1 / a) = S.card := by
      apply (Nat.floor_eq_iff (by positivity : 0 ≤ 1 / a)).mpr
      constructor
      · apply (le_div_iff₀ ha).mpr; linarith
      · apply (div_lt_iff₀ ha).mpr; nlinarith
    refine ⟨hfloor.symm, ?_⟩
    intro i
    by_cases hij : i = j
    · subst i
      right; right
      rw [hfloor]
      linarith
    · exact (hothers i hij).imp_right Or.inl

/-- The finite rounding engine yields exactly floor(1/a) capped entries and
at most one residual entry. This is the arbitrary-cap combinatorial step of
paper Lemma 5.1, valid for any pairwise-convex objective. -/
theorem exists_capped_remainder_ge {a : ℝ} (ha : 0 < a)
    (F : (ι → ℝ) → ℝ) (hF : PairwiseConvex a 1 F)
    {w : ι → ℝ} (hw : w ∈ slice a 1) :
    ∃ v ∈ slice a 1, F w ≤ F v ∧
      (interior a v).card ≤ 1 ∧
      (Finset.univ.filter (fun i => v i = a)).card = Nat.floor (1 / a) ∧
      ∀ i, v i = 0 ∨ v i = a ∨ v i = 1 - (Nat.floor (1 / a) : ℝ) * a := by
  obtain ⟨v, hv, hFv, hc⟩ := exists_almost_vertex_ge_of_pairwise a 1 F hF hw
  exact ⟨v, hv, hFv, hc, almost_vertex_cap_remainder ha hv hc⟩
end GaussianEllipsoid.CappedSimplex

namespace GaussianEllipsoid.CappedSimplex
/-- The paper's residual mass has exactly the claimed range. -/
theorem capped_remainder_range {a : ℝ} (ha : 0 < a) :
    0 ≤ 1 - (Nat.floor (1 / a) : ℝ) * a ∧
      1 - (Nat.floor (1 / a) : ℝ) * a < a := by
  have h := (Nat.floor_eq_iff (by positivity : 0 ≤ 1 / a)).mp
    (rfl : Nat.floor (1 / a) = Nat.floor (1 / a))
  have hl := (le_div_iff₀ ha).mp h.1
  have hu := (div_lt_iff₀ ha).mp h.2
  constructor <;> nlinarith
end GaussianEllipsoid.CappedSimplex
