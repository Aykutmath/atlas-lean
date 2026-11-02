import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open scoped BigOperators
namespace GaussianEllipsoid

/-- A convenient support-count bound valid at every n and m, including zero. -/
theorem sum_choose_le_successor_pow (n m : ℕ) :
    (∑ k ∈ Finset.range (m+1), n.choose k) ≤ (n+1)^m := by
  rw [add_pow]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hc : 1 ≤ m.choose k := Nat.succ_le_of_lt (Nat.choose_pos hk')
  calc
    n.choose k ≤ n^k := Nat.choose_le_pow n k
    _ = n^k * 1 := by simp
    _ ≤ n^k * m.choose k := Nat.mul_le_mul_left _ hc
    _ = _ := by simp

/-- The number of subsets of a finite ground set with size at most m. -/
theorem card_small_supports_le {α : Type*} (u : Finset α) (m : ℕ) :
    ((u.powerset).filter (fun s => s.card ≤ m)).card ≤ (u.card+1)^m := by
  classical
  have hsub : (u.powerset).filter (fun s => s.card ≤ m) ⊆
      (Finset.range (m+1)).biUnion (fun k => u.powersetCard k) := by
    intro s hs
    obtain ⟨hsu, hsm⟩ := Finset.mem_filter.mp hs
    apply Finset.mem_biUnion.mpr
    exact ⟨s.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hsm),
      Finset.mem_powersetCard.mpr ⟨Finset.mem_powerset.mp hsu, rfl⟩⟩
  calc
    _ ≤ ((Finset.range (m+1)).biUnion (fun k => u.powersetCard k)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (m+1), (u.powersetCard k).card :=
      Finset.card_biUnion_le
    _ = ∑ k ∈ Finset.range (m+1), u.card.choose k := by
      simp only [Finset.card_powersetCard]
    _ ≤ _ := sum_choose_le_successor_pow u.card m

#print axioms sum_choose_le_successor_pow
#print axioms card_small_supports_le
end GaussianEllipsoid
