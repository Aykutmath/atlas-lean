import PaperRhoActual
import ActualLateBranch

noncomputable section
open Finset
namespace GaussianEllipsoidCandidate

/-- The actual real-q base bin is part of the actual retained coefficient vector. -/
theorem real_base_bin_subset_retained {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r<groups.length) :
    dyadicBin u amp ((groups[r]?.getD []).headD 0) ⊆ retainedGroupUnion u amp groups T := by
  classical
  obtain ⟨t,tail,heq,_⟩ := hreg groups[r] (List.getElem_mem hr)
  simp only [List.getElem?_eq_getElem hr,Option.getD_some,heq,List.headD_cons]
  intro i hi
  unfold retainedGroupUnion
  apply Finset.mem_biUnion.mpr
  refine ⟨t::tail,List.mem_toFinset.mpr ?_,?_⟩
  · rw [← heq]
    exact List.getElem_mem hr
  · apply Finset.mem_biUnion.mpr
    refine ⟨0,Finset.mem_range.mpr hT,?_⟩
    simpa only [List.headD_cons,List.tail_cons,recordOffsetBin_zero] using hi

/-- No surrogate mass: the base bin carries at least 1/(4q) of its actual group. -/
theorem real_base_mass_lower {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r<groups.length) :
    dyadicGroupMass u amp groups T r/(4*q) ≤
      ∑ i ∈ dyadicBin u amp ((groups[r]?.getD []).headD 0),|u i| := by
  obtain ⟨t,tail,heq,h⟩ := hreg groups[r] (List.getElem_mem hr)
  have hm := h.2.2.2.2.2.1
  have hlo : (amp*(1/2:ℝ)^(t+1))*((dyadicBin u amp t).card:ℝ) ≤
      ∑ i ∈ dyadicBin u amp t,|u i| := by
    calc
      _ = ∑ i ∈ dyadicBin u amp t,amp*(1/2:ℝ)^(t+1) := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun i hi => ((mem_dyadicBin u amp t i).mp hi).1.le)
  simp only [dyadicGroupMass,dyadicGroupSupport,List.getElem?_eq_getElem hr,
    Option.getD_some,heq,List.headD_cons,List.tail_cons]
  apply (div_le_iff₀ (by linarith : 0<4*q)).mpr
  nlinarith

/-- The empty-late case is impossible in the late branch, using the exact retained mass sum. -/
theorem real_late_branch_nonempty {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T b : ℕ) (hb : b≤groups.length)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup)
    (hcapt : (∑ r ∈ range b,dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) : b<groups.length := by
  have hm := real_actual_group_mass_sum q u amp ha groups T hreg hflat
  have hM : 0≤coefficientMass (retainedGroupVector u amp groups T) :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  by_contra hn
  have he : b=groups.length := by omega
  rw [he,← hm] at hcapt
  linarith

/-- Literal real-q late driver: actual base bin, true retained l1 mass,
source 8q denominator, macroscopic lower size and original upper support size. -/
theorem real_late_driver_selection {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ) (ha : 0<amp)
    (groups : List (List ℕ)) (T : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (hflat : groups.flatten.Nodup) (rho K d J : ℝ) (hrho : 0<rho) (hJ : 0<J)
    (hsupp : ((univ.filter fun i => u i≠0).card:ℝ) ≤ K*d)
    (b : ℕ) (hb : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (rho*d) b)
    (hcount : ((groups.length-b:ℕ):ℝ) ≤ J)
    (hM : 0<coefficientMass (retainedGroupVector u amp groups T))
    (hcapt : (∑ r ∈ range b,dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) :
    ∃ r : ℕ,b≤r ∧ r<groups.length ∧
      let t := (groups[r]?.getD []).headD 0
      let a := amp*(1/2:ℝ)^(t+1)
      let I := dyadicBin u amp t
      0<a ∧
      coefficientMass (retainedGroupVector u amp groups T)/(8*q*J) ≤ ∑ i ∈ I,|u i| ∧
      rho*(q-1)/((T:ℝ)*q^2)*d < (I.card:ℝ) ∧ (I.card:ℝ)≤K*d ∧
      (∀ i ∈ I,a< |u i| ∧ |u i|≤2*a) ∧
      (∀ i ∈ I,retainedGroupVector u amp groups T i=u i) := by
  classical
  have hmass := real_actual_group_mass_sum q u amp ha.le groups T hreg hflat
  obtain ⟨r,hbr,hr,hmr⟩ := exists_heavy_late_group
    (dyadicGroupMass u amp groups T) groups.length b
    (coefficientMass (retainedGroupVector u amp groups T)) J hb.1 hM hJ hcount hmass.symm hcapt
  have hbase := real_base_mass_lower q hq u amp groups T hreg r hr
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  have hlate := rho_first_late_scale q T rho d _ _ hq hT' hrho (hb.2.2 r hbr hr)
    (real_actual_support_through_bound q hq u amp groups T hreg hchain r hr)
  refine ⟨r,hbr,hr,by positivity,?_,hlate,?_,?_,?_⟩
  · have heq : coefficientMass (retainedGroupVector u amp groups T)/(8*q*J) =
        (coefficientMass (retainedGroupVector u amp groups T)/(2*J))/(4*q) := by ring
    rw [heq]
    exact (div_le_div_of_nonneg_right hmr (by linarith)).trans hbase
  · exact (Nat.cast_le.mpr (card_le_card
      (dyadicBin_subset_original_support u amp ha _))).trans hsupp
  · intro i hi
    exact real_record_base_amplitudes u amp _ i hi
  · intro i hi
    exact if_pos (real_base_bin_subset_retained q u amp groups T hT hreg r hr hi)

#print axioms real_base_bin_subset_retained
#print axioms real_base_mass_lower
#print axioms real_late_branch_nonempty
#print axioms real_late_driver_selection
end GaussianEllipsoidCandidate
