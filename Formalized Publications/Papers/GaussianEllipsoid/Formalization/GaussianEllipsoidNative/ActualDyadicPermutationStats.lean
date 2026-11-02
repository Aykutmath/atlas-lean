import ActualDyadicSupportPermutation

noncomputable section
open Finset GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Actual retained coefficients equal the original coefficients on each
actual retained group. -/
theorem retainedGroupVector_eq_on_group {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T j : ℕ) (hj : j < groups.length) (i : Fin n)
    (hi : i ∈ dyadicGroupSupport u amp groups T j) :
    retainedGroupVector u amp groups T i = u i := by
  classical
  have hmem : i ∈ retainedGroupUnion u amp groups T := by
    rw [retainedGroupUnion_eq_indexed]
    simp only [indexedGroupUnion,mem_biUnion]
    exact ⟨j,mem_range.mpr hj,hi⟩
  simp only [retainedGroupVector,if_pos hmem]

/-- Restricting the actual retained vector to one of its groups discards no
coefficient from that group's original vector. -/
theorem retainedGroupVector_group_restriction {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T j : ℕ) (hj : j < groups.length) :
    (fun i => if i ∈ dyadicGroupSupport u amp groups T j
      then retainedGroupVector u amp groups T i else 0) =
    (fun i => if i ∈ dyadicGroupSupport u amp groups T j then u i else 0) := by
  classical
  funext i
  by_cases hi : i ∈ dyadicGroupSupport u amp groups T j
  · simp only [if_pos hi,retainedGroupVector_eq_on_group u amp groups T j hj i hi]
  · simp only [if_neg hi]

/-- The interval mask of the permuted retained vector is literally the
permutation of the original actual single-group coefficient vector. -/
theorem actualDyadicSupportPermutation_interval_mask {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (j : ℕ) (hj : j < groups.length) :
    (fun i => if supportCut (dyadicGroupSupport u amp groups T) j ≤ i.val ∧
        i.val < supportCut (dyadicGroupSupport u amp groups T) (j+1)
      then permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
        (retainedGroupVector u amp groups T) i else 0) =
    permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
      (fun i => if i ∈ dyadicGroupSupport u amp groups T j then u i else 0) := by
  unfold actualDyadicSupportPermutation
  rw [← permuteRows_group_restriction (dyadicGroupSupport u amp groups T)
    (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl)
    j hj (retainedGroupVector u amp groups T)]
  rw [retainedGroupVector_group_restriction u amp groups T j hj]

/-- Exact original dyadic mass and squared energy on an ordered retained block. -/
theorem actualDyadicSupportPermutation_interval_stats {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (j : ℕ) (hj : j < groups.length) :
    let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
    let V := permuteRows e (retainedGroupVector u amp groups T)
    let I := supportInterval n (supportCut (dyadicGroupSupport u amp groups T) j)
      (supportCut (dyadicGroupSupport u amp groups T) (j+1))
    (∑ i ∈ I, |V i|) = dyadicGroupMass u amp groups T j ∧
      (∑ i ∈ I, (V i)^2) = ∑ i ∈ dyadicGroupSupport u amp groups T j, (u i)^2 := by
  classical
  dsimp only
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let V := permuteRows e (retainedGroupVector u amp groups T)
  let G := dyadicGroupSupport u amp groups T
  let B := fun i : Fin n => if supportCut G j ≤ i.val ∧ i.val < supportCut G (j+1)
    then V i else 0
  have hB : B = permuteRows e (fun i => if i ∈ G j then u i else 0) :=
    actualDyadicSupportPermutation_interval_mask u amp ha groups T hreg hflat j hj
  have habs : (∑ i, |B i|) = dyadicGroupMass u amp groups T j := by
    rw [hB]
    rw [(permuteRows_abs_sq e (fun i => if i ∈ G j then u i else 0)).1]
    simp only [apply_ite abs,abs_zero]
    simp only [sum_ite,mem_univ,filter_true_of_mem,sum_const_zero,add_zero]
    simp [G,dyadicGroupMass]
  have hsq : (∑ i, (B i)^2) = ∑ i ∈ G j, (u i)^2 := by
    rw [hB]
    rw [(permuteRows_abs_sq e (fun i => if i ∈ G j then u i else 0)).2]
    simp only [ite_pow,zero_pow (by decide : 2 ≠ 0)]
    simp
  constructor
  · convert habs using 1
    simp [B,supportInterval,V,e,G,apply_ite abs,sum_filter]
  · convert hsq using 1
    simp [B,supportInterval,V,e,G,apply_ite abs,sum_filter]


/-- The actual group coefficient cap needed for the projected regular-cluster law. -/
theorem actual_group_energy_mass_cap {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (j : ℕ) (hj : j < groups.length) (i : Fin n)
    (hi : i ∈ dyadicGroupSupport u amp groups T j) :
    |u i| ≤ 16 * (∑ k ∈ dyadicGroupSupport u amp groups T j, (u k)^2) /
      dyadicGroupMass u amp groups T j := by
  obtain ⟨t,tail,heq,hS,ha,hklo,hkhi,hmlo,hmhi,hQlo,hQhi,
    hm,hQ,hRlo,hRhi,henergy,hcap,htail⟩ := hreg groups[j] (List.getElem_mem hj)
  have hi' : i ∈ recordRetainedSupport u amp t tail T := by
    simpa only [dyadicGroupSupport,List.getElem?_eq_getElem hj,Option.getD_some,
      heq,List.headD_cons,List.tail_cons] using hi
  simpa only [dyadicGroupSupport,dyadicGroupMass,List.getElem?_eq_getElem hj,
    Option.getD_some,heq,List.headD_cons,List.tail_cons] using (hcap i hi').2.1

/-- Full interval-masked retained coefficients satisfy the actual 16Q/m cap,
including zero coefficients outside the interval. -/
theorem actualDyadicSupportPermutation_interval_cap {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (j : ℕ) (hj : j < groups.length) :
    ∀ i : Fin n,
      |if supportCut (dyadicGroupSupport u amp groups T) j ≤ i.val ∧
          i.val < supportCut (dyadicGroupSupport u amp groups T) (j+1)
        then permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
          (retainedGroupVector u amp groups T) i else 0| ≤
      16 * (∑ k ∈ dyadicGroupSupport u amp groups T j, (u k)^2) /
        dyadicGroupMass u amp groups T j := by
  classical
  intro i
  have heq := congrFun (actualDyadicSupportPermutation_interval_mask
    u amp ha groups T hreg hflat j hj) i
  rw [heq]
  dsimp only [permuteRows]
  split_ifs with hi
  · exact actual_group_energy_mass_cap u amp groups T hreg j hj _ hi
  · simp only [abs_zero]
    apply div_nonneg
    · positivity
    · exact sum_nonneg (fun _ _ => abs_nonneg _)


/-- The same identities as full finite sums of the interval-masked vector. -/
theorem actualDyadicSupportPermutation_mask_stats {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (j : ℕ) (hj : j < groups.length) :
    let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
    let V := permuteRows e (retainedGroupVector u amp groups T)
    let B := fun i : Fin n =>
      if supportCut (dyadicGroupSupport u amp groups T) j ≤ i.val ∧
          i.val < supportCut (dyadicGroupSupport u amp groups T) (j+1)
        then V i else 0
    (∑ i, |B i|) = dyadicGroupMass u amp groups T j ∧
      (∑ i, (B i)^2) = ∑ i ∈ dyadicGroupSupport u amp groups T j, (u i)^2 := by
  have hh := actualDyadicSupportPermutation_interval_stats u amp ha groups T hreg hflat j hj
  dsimp only at hh ⊢
  simpa [supportInterval,sum_filter,apply_ite abs] using hh

end GaussianEllipsoidCandidate
