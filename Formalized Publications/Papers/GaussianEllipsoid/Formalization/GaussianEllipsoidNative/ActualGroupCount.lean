import ActualCrossScalars

namespace GaussianEllipsoidCandidate
open Finset

/-- There are at most n actual retained groups, irrespective of dynamic range.
Each group has a nonempty support and their supports are disjoint. -/
theorem actual_group_count_le_ambient {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) : groups.length ≤ n := by
  have hsize : ∀ r < groups.length, (1:ℝ) ≤ dyadicGroupSize u amp groups T r := by
    intro r hr
    have hb := actual_group_numerical_bounds u amp groups T hreg r hr
    have hpos : (0:ℝ) < (dyadicGroupSupport u amp groups T r).card := hb.1.trans_le hb.2.1
    have hp : 0 < (dyadicGroupSupport u amp groups T r).card := by exact_mod_cast hpos
    change (1:ℝ) ≤ (dyadicGroupSupport u amp groups T r).card
    exact_mod_cast hp
  have hsum : (groups.length:ℝ) ≤ ∑ r ∈ range groups.length, dyadicGroupSize u amp groups T r := by
    calc
      (groups.length:ℝ) = ∑ _r ∈ range groups.length, (1:ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun r hr => hsize r (mem_range.mp hr))
  rw [← actual_group_prefix_card u amp ha groups T hreg hflat groups.length le_rfl] at hsum
  have hc : ((range groups.length).biUnion (dyadicGroupSupport u amp groups T)).card ≤ n := by
    exact (card_le_univ _).trans_eq (Fintype.card_fin n)
  exact_mod_cast hsum.trans (Nat.cast_le.mpr hc)

end GaussianEllipsoidCandidate
