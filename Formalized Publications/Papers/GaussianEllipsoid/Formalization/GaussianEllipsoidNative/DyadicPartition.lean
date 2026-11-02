import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace GaussianEllipsoidCandidate

open Finset

/-- Every nonzero bounded coefficient belongs to a half-open dyadic magnitude bin. -/
theorem exists_dyadic_level (amp x : ℝ) (ha : 0 < amp) (hx : x ≠ 0)
    (hcap : |x| ≤ amp) :
    ∃ t : ℕ, amp * (1 / 2 : ℝ)^(t+1) < |x| ∧
      |x| ≤ amp * (1 / 2 : ℝ)^t := by
  have hx0 : 0 < |x| / amp := div_pos (abs_pos.mpr hx) ha
  have hx1 : |x| / amp ≤ 1 := (div_le_iff₀ ha).2 (by simpa using hcap)
  obtain ⟨t, htlo, hthi⟩ := exists_nat_pow_near_of_lt_one hx0 hx1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨t, ?_, ?_⟩
  · simpa [mul_comm] using (lt_div_iff₀ ha).1 htlo
  · simpa [mul_comm] using (div_le_iff₀ ha).1 hthi

/-- The strict lower and weak upper endpoints assign boundary values uniquely. -/
theorem dyadic_level_unique (amp x : ℝ) (ha : 0 ≤ amp) (t s : ℕ)
    (ht : amp * (1 / 2 : ℝ)^(t+1) < |x| ∧ |x| ≤ amp * (1 / 2 : ℝ)^t)
    (hs : amp * (1 / 2 : ℝ)^(s+1) < |x| ∧ |x| ≤ amp * (1 / 2 : ℝ)^s) : t = s := by
  have hnotlt : ∀ a b : ℕ,
      (amp * (1 / 2 : ℝ)^(a+1) < |x|) →
      (|x| ≤ amp * (1 / 2 : ℝ)^b) → ¬ a < b := by
    intro a b hlo hhi hab
    have hp : (1 / 2 : ℝ)^b ≤ (1 / 2 : ℝ)^(a+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_of_lt hab)
    have hm := mul_le_mul_of_nonneg_left hp ha
    linarith
  exact Nat.le_antisymm (Nat.le_of_not_gt (hnotlt s t hs.1 ht.2))
    (Nat.le_of_not_gt (hnotlt t s ht.1 hs.2))

noncomputable def dyadicBin {ι : Type*} [Fintype ι] (u : ι → ℝ) (amp : ℝ)
    (t : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter fun i =>
    amp * (1 / 2 : ℝ)^(t+1) < |u i| ∧ |u i| ≤ amp * (1 / 2 : ℝ)^t

lemma mem_dyadicBin {ι : Type*} [Fintype ι] (u : ι → ℝ) (amp : ℝ)
    (t : ℕ) (i : ι) :
    i ∈ dyadicBin u amp t ↔
      amp * (1 / 2 : ℝ)^(t+1) < |u i| ∧ |u i| ≤ amp * (1 / 2 : ℝ)^t := by
  classical
  simp [dyadicBin]

/-- Different dyadic levels are disjoint, including empty levels. -/
theorem dyadicBin_disjoint {ι : Type*} [Fintype ι] (u : ι → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (t s : ℕ) (hne : t ≠ s) :
    Disjoint (dyadicBin u amp t) (dyadicBin u amp s) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hit his
  apply hne
  exact dyadic_level_unique amp (u i) ha t s
    ((mem_dyadicBin u amp t i).1 hit) ((mem_dyadicBin u amp s i).1 his)

/-- Arbitrary dynamic range still admits a finite dyadic partition. This
proves both coverage of every nonzero coordinate and emptiness after a finite
cutoff, rather than imposing a dynamic-range assumption. -/
theorem finite_dyadic_partition {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) := by
  classical
  have hlevels : ∀ i, ∃ t : ℕ, u i ≠ 0 →
      amp * (1 / 2 : ℝ)^(t+1) < |u i| ∧ |u i| ≤ amp * (1 / 2 : ℝ)^t := by
    intro i
    by_cases hi : u i = 0
    · exact ⟨0, fun h => (h hi).elim⟩
    · obtain ⟨t, ht⟩ := exists_dyadic_level amp (u i) ha hi (hcap i)
      exact ⟨t, fun _ => ht⟩
  choose level hlevel using hlevels
  let N : ℕ := (∑ i, level i) + 1
  have hlt : ∀ i, level i < N := by
    intro i
    have hi : level i ≤ ∑ j, level j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (level j)) (Finset.mem_univ i)
    dsimp [N]
    omega
  have hnonzero : ∀ t i, i ∈ dyadicBin u amp t → u i ≠ 0 := by
    intro t i hi hz
    have h := ((mem_dyadicBin u amp t i).1 hi).1
    have hp : 0 < amp * (1 / 2 : ℝ)^(t+1) := mul_pos ha (pow_pos (by norm_num) _)
    rw [hz, abs_zero] at h
    linarith
  refine ⟨N, by dsimp [N]; omega, ?_, ?_⟩
  · intro i
    constructor
    · intro hi
      exact ⟨level i, Finset.mem_range.mpr (hlt i),
        (mem_dyadicBin u amp (level i) i).2 (hlevel i hi)⟩
    · rintro ⟨t, _, ht⟩
      exact hnonzero t i ht
  · intro t ht
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hz := hnonzero t i hi
    have heq := dyadic_level_unique amp (u i) ha.le t (level i)
      ((mem_dyadicBin u amp t i).1 hi) (hlevel i hz)
    have hil := hlt i
    omega

#print axioms exists_dyadic_level
#print axioms dyadic_level_unique
#print axioms mem_dyadicBin
#print axioms dyadicBin_disjoint
#print axioms finite_dyadic_partition

end GaussianEllipsoidCandidate

