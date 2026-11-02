import ActualSupportGeometry

namespace GaussianEllipsoidCandidate
open Finset

noncomputable def dyadicGroupMass {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) : ℝ :=
  ∑ i ∈ dyadicGroupSupport u amp groups T r, |u i|

noncomputable def indexedGroupUnion {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T n : ℕ) : Finset ι := by
  classical
  exact (range n).biUnion (dyadicGroupSupport u amp groups T)

/-- The retained vector's support union equals the indexed group union. -/
theorem retainedGroupUnion_eq_indexed {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) :
    retainedGroupUnion u amp groups T =
      indexedGroupUnion u amp groups T groups.length := by
  classical
  unfold retainedGroupUnion indexedGroupUnion
  ext i
  constructor
  · intro hi
    obtain ⟨g, hg, hig⟩ := mem_biUnion.mp hi
    obtain ⟨r, hr, heq⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hg)
    apply mem_biUnion.mpr
    refine ⟨r, mem_range.mpr hr, ?_⟩
    simpa only [dyadicGroupSupport, List.getElem?_eq_getElem hr, Option.getD_some, heq] using hig
  · intro hi
    obtain ⟨r, hr, hir⟩ := mem_biUnion.mp hi
    have hr' := mem_range.mp hr
    apply mem_biUnion.mpr
    refine ⟨groups[r], List.mem_toFinset.mpr (List.getElem_mem hr'), ?_⟩
    simpa only [dyadicGroupSupport, List.getElem?_eq_getElem hr', Option.getD_some] using hir

/-- Disjoint actual groups partition the retained l1 mass exactly. -/
theorem actual_group_mass_sum {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) :
    coefficientMass (retainedGroupVector u amp groups T) =
      ∑ r ∈ range groups.length, dyadicGroupMass u amp groups T r := by
  classical
  have hmass : coefficientMass (retainedGroupVector u amp groups T) =
      ∑ i ∈ retainedGroupUnion u amp groups T, |u i| := by
    classical
    simp only [coefficientMass, retainedGroupVector]
    simp_rw [apply_ite abs]
    simp
  rw [hmass, retainedGroupUnion_eq_indexed, indexedGroupUnion,
    sum_biUnion (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl)]
  rfl

/-- The record bin carries at least an eighth of its retained group mass. -/
theorem actual_base_mass_lower {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    dyadicGroupMass u amp groups T r / 8 ≤
      ∑ i ∈ dyadicBin u amp ((groups[r]?.getD []).headD 0), |u i| := by
  obtain ⟨t, tail, heq, h⟩ := hreg groups[r] (List.getElem_mem hr)
  have hm := h.2.2.2.2.2.1
  have hlo : (amp*(1/2:ℝ)^(t+1))*((dyadicBin u amp t).card:ℝ) ≤
      ∑ i ∈ dyadicBin u amp t, |u i| := by
    calc
      _ = ∑ i ∈ dyadicBin u amp t, amp*(1/2:ℝ)^(t+1) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi => ((mem_dyadicBin u amp t i).mp hi).1.le)
  simp only [dyadicGroupMass, dyadicGroupSupport, List.getElem?_eq_getElem hr,
    Option.getD_some, heq, List.headD_cons, List.tail_cons]
  linarith

/-- If less than half the mass was captured, one of the boundedly many late
groups has the required driver mass. -/
theorem exists_heavy_late_group (m : ℕ → ℝ) (N q : ℕ) (M J : ℝ)
    (hq : q ≤ N) (hM : 0 < M) (hJ : 0 < J)
    (hcount : ((N-q:ℕ):ℝ) ≤ J)
    (hsum : (∑ r ∈ range N, m r) = M)
    (hcapt : (∑ r ∈ range q, m r) < M/2) :
    ∃ r, q ≤ r ∧ r < N ∧ M/(2*J) ≤ m r := by
  have hsplit := sum_range_add_sum_Ico m hq
  have hlate : M/2 < ∑ r ∈ Ico q N, m r := by linarith
  have hqN : q < N := by
    by_contra h
    have : q = N := by omega
    subst q
    simp at hlate
    linarith
  have hne : (Ico q N).Nonempty := nonempty_Ico.mpr hqN
  have hconst : (∑ r ∈ Ico q N, M/(2*J)) ≤ M/2 := by
    simp only [sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hmul := mul_le_mul_of_nonneg_right hcount (by positivity : 0 ≤ M/(2*J))
    have heq : J*(M/(2*J)) = M/2 := by field_simp <;> ring
    exact hmul.trans_eq heq
  obtain ⟨r, hr, hmr⟩ := exists_le_of_sum_le hne (hconst.trans hlate.le)
  exact ⟨r, (mem_Ico.mp hr).1, (mem_Ico.mp hr).2, hmr⟩

/-- An actual late record bin supplies the macroscopic Gaussian driver,
including its mass, size, and factor-two coefficient window. -/
theorem actual_late_driver_selection {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ))
    (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (d J : ℝ) (hJ : 0 < J) (q : ℕ)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (d/256) q)
    (hcount : ((groups.length-q:ℕ):ℝ) ≤ J)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T))
    (hcapt : (∑ r ∈ range q, dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) :
    ∃ r : ℕ, q ≤ r ∧ r < groups.length ∧
      let t := (groups[r]?.getD []).headD 0
      let a := amp*(1/2:ℝ)^(t+1)
      let I := dyadicBin u amp t
      0 < a ∧
      coefficientMass (retainedGroupVector u amp groups T)/(16*J) ≤ ∑ i ∈ I, |u i| ∧
      d/(1024*T) < (I.card:ℝ) ∧
      ∀ i ∈ I, a < |u i| ∧ |u i| ≤ 2*a := by
  have hmass := actual_group_mass_sum u amp ha.le groups T hreg hflat
  obtain ⟨r, hqr, hr, hmr⟩ := exists_heavy_late_group
    (dyadicGroupMass u amp groups T) groups.length q
    (coefficientMass (retainedGroupVector u amp groups T)) J hq.1 hM hJ hcount hmass.symm hcapt
  have hbase := actual_base_mass_lower u amp ha groups T hreg r hr
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hlate := record_scale_after_cutoff (dyadicGroupScale u amp groups)
    (dyadicGroupSize u amp groups T) groups.length q T (d/256) hT'
    (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).1.le)
    (actual_group_doubling u amp groups T hreg hchain)
    (fun i hi => (actual_group_numerical_bounds u amp groups T hreg i hi).2.2.1) hq r hqr hr
  refine ⟨r, hqr, hr, ?_, ?_, ?_, ?_⟩
  · positivity
  · have heq : coefficientMass (retainedGroupVector u amp groups T)/(16*J) =
        (coefficientMass (retainedGroupVector u amp groups T)/(2*J))/8 := by ring
    rw [heq]
    exact (div_le_div_of_nonneg_right hmr (by norm_num)).trans hbase
  · change d/(1024*T) < dyadicGroupScale u amp groups r
    convert hlate using 1 <;> ring
  · intro i hi
    have hh := (mem_dyadicBin u amp _ i).mp hi
    refine ⟨hh.1, ?_⟩
    have heq : amp*(1/2:ℝ)^((groups[r]?.getD []).headD 0) =
        2*(amp*(1/2:ℝ)^((groups[r]?.getD []).headD 0+1)) := by
      rw [pow_succ]
      ring
    exact hh.2.trans_eq heq

end GaussianEllipsoidCandidate
