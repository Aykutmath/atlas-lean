import CutoffThresholds
import LateGroupCount

namespace GaussianEllipsoidCandidate
open Finset

/-- Membership in a concrete retained group identifies an original dyadic
level in exactly that record group. -/
theorem actual_group_support_mem_level {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) (i : ι)
    (hi : i ∈ dyadicGroupSupport u amp groups T r) :
    ∃ t ∈ groups[r], i ∈ dyadicBin u amp t := by
  obtain ⟨t, tail, heq, _⟩ := hreg groups[r] (List.getElem_mem hr)
  have hi' : i ∈ recordRetainedSupport u amp t tail T := by
    simpa only [dyadicGroupSupport, List.getElem?_eq_getElem hr,
      Option.getD_some, heq, List.headD_cons, List.tail_cons] using hi
  rw [heq]
  exact retained_mem_level u amp t tail T i hi'

/-- Indexed actual retained supports are pairwise disjoint. -/
theorem actual_group_supports_pairwise {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (n : ℕ) (hn : n ≤ groups.length) :
    Set.PairwiseDisjoint (↑(range n) : Set ℕ) (dyadicGroupSupport u amp groups T) := by
  have hp := (List.nodup_flatten.mp hflat).2
  intro r hr s hs hne
  have hr' : r < groups.length := lt_of_lt_of_le (mem_range.mp hr) hn
  have hs' : s < groups.length := lt_of_lt_of_le (mem_range.mp hs) hn
  have hdis : List.Disjoint groups[r] groups[s] := by
    rcases lt_or_gt_of_ne hne with hrs | hsr
    · exact List.pairwise_iff_getElem.mp hp r s hr' hs' hrs
    · exact (List.pairwise_iff_getElem.mp hp s r hs' hr' hsr).symm
  apply Finset.disjoint_left.mpr
  intro i hir his
  obtain ⟨t, htr, hit⟩ := actual_group_support_mem_level u amp groups T hreg r hr' i hir
  obtain ⟨v, hvs, hiv⟩ := actual_group_support_mem_level u amp groups T hreg s hs' i his
  have heq := dyadic_level_unique amp (u i) ha t v
    ((mem_dyadicBin u amp t i).mp hit) ((mem_dyadicBin u amp v i).mp hiv)
  subst v
  exact List.disjoint_left.mp hdis htr hvs

/-- Prefix support sums are exactly the size of the prefix sample union,
so they bound left and right sample-span dimensions without multiplicity. -/
theorem actual_group_prefix_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (n : ℕ) (hn : n ≤ groups.length) :
    (((range n).biUnion (dyadicGroupSupport u amp groups T)).card : ℝ) =
      ∑ r ∈ range n, dyadicGroupSize u amp groups T r := by
  classical
  rw [card_biUnion (actual_group_supports_pairwise u amp ha groups T hreg hflat n hn)]
  simp only [Nat.cast_sum, dyadicGroupSize]

/-- All retained prefix coordinates are nonzero coordinates of the original
coefficient vector. -/
theorem actual_group_prefix_subset_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (n : ℕ) (hn : n ≤ groups.length) :
    (range n).biUnion (dyadicGroupSupport u amp groups T) ⊆
      Finset.univ.filter (fun i => u i ≠ 0) := by
  classical
  intro i hi
  obtain ⟨r, hr, hir⟩ := mem_biUnion.mp hi
  have hr' : r < groups.length := lt_of_lt_of_le (mem_range.mp hr) hn
  obtain ⟨t, _, hit⟩ := actual_group_support_mem_level u amp groups T hreg r hr' i hir
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  intro hz
  have hh := ((mem_dyadicBin u amp t i).mp hit).1
  rw [hz, abs_zero] at hh
  exact (not_lt_of_ge (by positivity)) hh

/-- In particular the sum of actual group sizes is bounded by the input
support size, as needed for the late-bin support cap. -/
theorem actual_group_total_support_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) :
    (∑ r ∈ range groups.length, dyadicGroupSize u amp groups T r) ≤
      ((Finset.univ.filter fun i => u i ≠ 0).card : ℝ) := by
  classical
  rw [← actual_group_prefix_card u amp ha.le groups T hreg hflat groups.length le_rfl]
  exact_mod_cast card_le_card
    (actual_group_prefix_subset_support u amp ha groups T hreg groups.length le_rfl)

/-- The constructor's exact flatten identity automatically supplies every
no-overlap hypothesis in this module. -/
theorem actual_constructor_flatten_nodup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (N : ℕ)
    (hflat : groups.flatten = dyadicRecordLevels u amp N) : groups.flatten.Nodup := by
  rw [hflat]
  exact List.Nodup.filter _ List.nodup_range

/-- Late bins meet any fixed absolute minimum when the dimension is large
relative to the fixed retention width. -/
theorem late_bin_minimum (s d T B : ℝ) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hd : 1024*T*B ≤ d) (hs : d/(1024*T) < s) : B ≤ min s d := by
  have hT0 : 0 < T := by linarith
  have hsd := (div_lt_iff₀ (by positivity : 0 < 1024*T)).mp hs
  have hBsmall : B ≤ s := by nlinarith
  have hdsmall : B ≤ d := by nlinarith
  exact le_min hBsmall hdsmall

/-- The same first-late estimate yields a uniform quadratic probability
exponent after substituting `min(s,d)` in the macroscopic-bin law. -/
theorem late_bin_minimum_scale (s d T : ℝ) (hd : 0 ≤ d) (hT : 1 ≤ T)
    (hs : d/(1024*T) < s) : d/(1024*T) ≤ min s d := by
  have hT0 : 0 < T := by linarith
  refine le_min hs.le ?_
  apply (div_le_iff₀ (by positivity : 0 < 1024*T)).2
  nlinarith

end GaussianEllipsoidCandidate
