import RealMartingaleRadius

noncomputable section
set_option autoImplicit false
open Finset
namespace GaussianEllipsoidCandidate

/-- Every actual regular group has strictly positive retained mass. -/
theorem real_actual_group_mass_pos {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    0 < dyadicGroupMass u amp groups T r := by
  obtain ⟨t, tail, heq, h⟩ := hreg groups[r] (List.getElem_mem hr)
  dsimp only at h
  rcases h with ⟨hS, ha, hklo, hkhi, hmlo, hmhi, hQlo, hQhi, hm, hrest⟩
  simpa only [dyadicGroupMass, dyadicGroupSupport, List.getElem?_eq_getElem hr,
    Option.getD_some, heq, List.headD_cons, List.tail_cons] using hm

/-- A nonzero coefficient vector has an actual record group. This uses the
bin cover, not a truncation-error bound that might exceed one for small T. -/
theorem real_record_groups_nonempty {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (N : ℕ) (groups : List (List ℕ))
    (hu : u ≠ 0)
    (hcover : ∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u amp t)
    (hflat : groups.flatten = dyadicRecordLevels u amp N) :
    0 < groups.length := by
  classical
  have hex : ∃ i, u i ≠ 0 := by
    by_contra h
    apply hu
    funext i
    simpa only [Pi.zero_apply] using (not_exists_not.mp h i)
  obtain ⟨i, hi⟩ := hex
  obtain ⟨t, ht, hit⟩ := (hcover i).mp hi
  have hlev : t ∈ dyadicRecordLevels u amp N :=
    (mem_dyadicRecordLevels u amp N t).mpr ⟨mem_range.mp ht, ⟨i, hit⟩⟩
  rw [← hflat] at hlev
  cases groups with
  | nil => simp at hlev
  | cons g gs => simp

/-- Actual retained mass is positive for every nonzero vector and every
positive truncation depth admitted by the regular-group construction. -/
theorem real_retained_mass_pos {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (N : ℕ) (groups : List (List ℕ)) (T : ℕ) (hu : u ≠ 0)
    (hcover : ∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u amp t)
    (hflat : groups.flatten = dyadicRecordLevels u amp N)
    (hnodup : groups.flatten.Nodup)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g) :
    0 < coefficientMass (retainedGroupVector u amp groups T) := by
  have hn := real_record_groups_nonempty u amp N groups hu hcover hflat
  exact lt_of_lt_of_le (real_actual_group_mass_pos q u amp groups T hreg 0 hn)
    (real_actual_group_mass_le_total q u amp ha groups T hreg hnodup 0 hn)

#print axioms real_actual_group_mass_pos
#print axioms real_record_groups_nonempty
#print axioms real_retained_mass_pos
end GaussianEllipsoidCandidate
