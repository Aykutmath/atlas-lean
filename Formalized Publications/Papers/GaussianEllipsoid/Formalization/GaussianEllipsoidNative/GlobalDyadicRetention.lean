import MultiscaleIntegrated
import RetainedDecomposition
import RetainedDyadicGroups
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GaussianEllipsoidCandidate

open Finset

/-- Disjoint groups of dyadic levels induce disjoint coefficient supports. -/
theorem dyadic_group_supports_disjoint {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ))
    (hgroups : groups.Pairwise List.Disjoint) (F : List ℕ → Finset ι)
    (hF : ∀ g ∈ groups, ∀ i ∈ F g, ∃ t ∈ g, i ∈ dyadicBin u amp t) :
    Set.PairwiseDisjoint (↑groups.toFinset : Set (List ℕ)) F := by
  classical
  intro g hg h hh hne
  have hg' : g ∈ groups := List.mem_toFinset.mp hg
  have hh' : h ∈ groups := List.mem_toFinset.mp hh
  letI : Std.Symm (List.Disjoint : List ℕ → List ℕ → Prop) := ⟨fun _ _ h => h.symm⟩
  have hgh := hgroups.forall hg' hh' hne
  apply Finset.disjoint_left.mpr
  intro i hig hih
  obtain ⟨s, hsg, his⟩ := hF g hg' i hig
  obtain ⟨t, hth, hit⟩ := hF h hh' i hih
  have heq := dyadic_level_unique amp (u i) ha s t
    ((mem_dyadicBin u amp s i).1 his) ((mem_dyadicBin u amp t i).1 hit)
  subst t
  exact (List.disjoint_left.mp hgh) hsg hth

/-- A scalar weighted partition aggregation, used to sum all omitted groups. -/
theorem omitted_union_mass_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (J : Finset κ) (R O : κ → Finset ι)
    (hR : Set.PairwiseDisjoint (↑J : Set κ) R)
    (hO : Set.PairwiseDisjoint (↑J : Set κ) O)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hpart : ∀ g ∈ J, (∑ i ∈ O g, |u i|) ≤ ε * ∑ i ∈ R g, |u i|) :
    (∑ i ∈ J.biUnion O, |u i|) ≤ ε * coefficientMass u := by
  rw [Finset.sum_biUnion hO]
  calc
    ∑ g ∈ J, ∑ i ∈ O g, |u i| ≤ ∑ g ∈ J, ε * ∑ i ∈ R g, |u i| :=
      Finset.sum_le_sum hpart
    _ = ε * (∑ g ∈ J, ∑ i ∈ R g, |u i|) := (Finset.mul_sum _ _ _).symm
    _ = ε * (∑ i ∈ J.biUnion R, |u i|) := by rw [Finset.sum_biUnion hR]
    _ ≤ ε * coefficientMass u := by
      apply mul_le_mul_of_nonneg_left _ hε
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)

/-- Coverage of every nonzero coordinate controls the l1 residual of retaining R. -/
theorem residual_mass_le_cover_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (R O : Finset ι)
    (hcover : ∀ i, u i ≠ 0 → i ∈ R ∨ i ∈ O) :
    coefficientMass (fun i => if i ∈ R then 0 else u i) ≤ ∑ i ∈ O, |u i| := by
  classical
  unfold coefficientMass
  calc
    ∑ i, |if i ∈ R then 0 else u i| ≤ ∑ i, if i ∈ O then |u i| else 0 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hiR : i ∈ R
      · simp [hiR]
        split_ifs <;> positivity
      · by_cases hiO : i ∈ O
        · simp [hiR, hiO]
        · have hz : u i = 0 := by
            by_contra hn
            exact (hcover i hn).elim hiR hiO
          simp [hiR, hiO, hz]
    _ = ∑ i ∈ O, |u i| := by simp

/-- A member of a retained offset support belongs to a level of its group. -/
theorem retained_mem_level {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T : ℕ)
    (i : ι) (hi : i ∈ recordRetainedSupport u amp t tail T) :
    ∃ s ∈ t :: tail, i ∈ dyadicBin u amp s := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
  dsimp [recordOffsetBin] at hj
  split_ifs at hj with hm
  · exact ⟨t+j, hm, hj⟩
  · simp at hj

/-- A member of an omitted offset support belongs to a level of its group. -/
theorem omitted_mem_level {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (t : ℕ) (tail : List ℕ) (T N : ℕ)
    (i : ι) (hi : i ∈ recordOmittedSupport u amp t tail T N) :
    ∃ s ∈ t :: tail, i ∈ dyadicBin u amp s := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
  dsimp [recordOffsetBin] at hj
  split_ifs at hj with hm
  · exact ⟨t+j, hm, hj⟩
  · simp at hj

noncomputable def retainedGroupUnion {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) : Finset ι := by
  classical
  exact groups.toFinset.biUnion fun g => recordRetainedSupport u amp (g.headD 0) g.tail T

noncomputable def retainedGroupVector {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) : ι → ℝ := by
  classical
  exact fun i => if i ∈ retainedGroupUnion u amp groups T then u i else 0

/-- Complete deterministic retained decomposition: all coefficient partitions,
record groups, retained estimates, and the global omitted-l1 estimate are
constructed and proved for every finite vector, without a dynamic-range
hypothesis or any assumed decomposition. -/
theorem exists_global_dyadic_retention {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp)
    (T : ℕ) (hT : 0 < T) :
    ∃ N : ℕ, ∃ groups : List (List ℕ), 0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ Finset.range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, RegularRetainedGroup u amp T g) ∧
      groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card) ∧
      (∀ i, retainedGroupVector u amp groups T i = 0 ∨
        retainedGroupVector u amp groups T i = u i) ∧
      coefficientMass (u - retainedGroupVector u amp groups T) ≤
        8 * (1 / 2 : ℝ)^T * coefficientMass u := by
  classical
  obtain ⟨N, groups, hN, hcover0, hempty, hflat, hreg, hchain⟩ :=
    exists_dyadic_record_decomposition u amp ha hcap
  have hnodup : groups.flatten.Nodup := by
    rw [hflat]
    exact List.Nodup.filter _ List.nodup_range
  have hgroups := (List.nodup_flatten.mp hnodup).2
  have hsort : groups.flatten.Pairwise (fun s t : ℕ => s < t) := by
    rw [hflat]
    exact List.Pairwise.filter _ List.pairwise_lt_range
  let J := groups.toFinset
  let R : List ℕ → Finset ι := fun g => recordRetainedSupport u amp (g.headD 0) g.tail T
  let O : List ℕ → Finset ι := fun g => recordOmittedSupport u amp (g.headD 0) g.tail T N
  let Rall := J.biUnion R
  let Oall := J.biUnion O
  have hR : Set.PairwiseDisjoint (↑J : Set (List ℕ)) R := by
    apply dyadic_group_supports_disjoint u amp ha.le groups hgroups R
    intro g hg i hi
    obtain ⟨t, tail, heq, _, _⟩ := hreg g hg
    subst g
    exact retained_mem_level u amp t tail T i hi
  have hO : Set.PairwiseDisjoint (↑J : Set (List ℕ)) O := by
    apply dyadic_group_supports_disjoint u amp ha.le groups hgroups O
    intro g hg i hi
    obtain ⟨t, tail, heq, _, _⟩ := hreg g hg
    subst g
    exact omitted_mem_level u amp t tail T N i hi
  have hpart : ∀ g ∈ J, (∑ i ∈ O g, |u i|) ≤
      8 * (1 / 2 : ℝ)^T * ∑ i ∈ R g, |u i| := by
    intro g hg
    obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g (List.mem_toFinset.mp hg)
    subst g
    dsimp [R, O]
    have hall := retained_group_estimates u amp ha t tail hbase hsmall T hT
    dsimp only at hall
    rcases hall with ⟨_, _, _, _, hmlo, _, _, _, _⟩
    have ho := record_omitted_mass u amp ha.le t tail hsmall T N
    dsimp only at ho
    have hh := mul_le_mul_of_nonneg_left hmlo
      (by positivity : 0 ≤ 8 * (1 / 2 : ℝ)^T)
    nlinarith
  have hcover : ∀ i, u i ≠ 0 → i ∈ Rall ∨ i ∈ Oall := by
    intro i hi
    obtain ⟨s, hsN, his⟩ := (hcover0 i).1 hi
    have hsN' : s < N := Finset.mem_range.mp hsN
    have hslevels : s ∈ dyadicRecordLevels u amp N :=
      (mem_dyadicRecordLevels u amp N s).2 ⟨hsN', ⟨i, his⟩⟩
    have hsflat : s ∈ groups.flatten := by rwa [hflat]
    obtain ⟨g, hg, hsg⟩ := List.mem_flatten.mp hsflat
    obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g hg
    subst g
    have hgSorted : (t :: tail).Pairwise (fun s t : ℕ => s < t) :=
      List.Pairwise.sublist (List.sublist_flatten_of_mem hg) hsort
    have htle : t ≤ s := by
      rcases List.mem_cons.mp hsg with heq | hmem
      · omega
      · have hh := (List.pairwise_cons.mp hgSorted).1 s hmem
        omega
    have hts : t + (s - t) = s := Nat.add_sub_of_le htle
    by_cases hret : s - t < T
    · left
      apply Finset.mem_biUnion.mpr
      refine ⟨t :: tail, List.mem_toFinset.mpr hg, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨s-t, Finset.mem_range.mpr hret, ?_⟩
      simpa [recordOffsetBin, hts, hsg] using his
    · right
      apply Finset.mem_biUnion.mpr
      refine ⟨t :: tail, List.mem_toFinset.mpr hg, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨s-t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa [recordOffsetBin, hts, hsg] using his
  have herror : coefficientMass (u - retainedGroupVector u amp groups T) ≤
      8 * (1 / 2 : ℝ)^T * coefficientMass u := by
    have heq : u - retainedGroupVector u amp groups T =
        (fun i => if i ∈ Rall then 0 else u i) := by
      funext i
      change u i - (if i ∈ Rall then u i else 0) = _
      split_ifs <;> simp
    rw [heq]
    exact (residual_mass_le_cover_mass u Rall Oall hcover).trans
      (omitted_union_mass_le u J R O hR hO (8 * (1 / 2 : ℝ)^T) (by positivity) hpart)
  refine ⟨N, groups, hN, hcover0, hempty, hflat, ?_, hchain, ?_, herror⟩
  · intro g hg
    obtain ⟨t, tail, heq, hbase, hsmall⟩ := hreg g hg
    rw [heq]
    exact regularRetainedGroup_of_record u amp ha t tail hbase hsmall T hT
  · intro i
    unfold retainedGroupVector
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

#print axioms exists_global_dyadic_retention

#print axioms dyadic_group_supports_disjoint
#print axioms omitted_union_mass_le
#print axioms residual_mass_le_cover_mass
#print axioms retained_mem_level
#print axioms omitted_mem_level

end GaussianEllipsoidCandidate
