import CanonicalMultiscaleLaw
import ActualGroupMass
import ConstructedCutoffGeometry

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Every actual record base bin is among the retained coordinates. -/
theorem actual_base_bin_subset_retained {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    dyadicBin u amp ((groups[r]?.getD []).headD 0) ⊆
      retainedGroupUnion u amp groups T := by
  classical
  obtain ⟨t, tail, heq, _⟩ := hreg groups[r] (List.getElem_mem hr)
  simp only [List.getElem?_eq_getElem hr, Option.getD_some, heq, List.headD_cons]
  intro i hi
  unfold retainedGroupUnion
  apply Finset.mem_biUnion.mpr
  refine ⟨t :: tail, List.mem_toFinset.mpr ?_, ?_⟩
  · rw [← heq]
    exact List.getElem_mem hr
  · apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_range.mpr hT, ?_⟩
    simpa only [List.headD_cons, List.tail_cons, recordOffsetBin_zero] using hi

/-- A positive-amplitude dyadic bin is supported in the original vector. -/
theorem dyadicBin_subset_original_support {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (t : ℕ) :
    dyadicBin u amp t ⊆ Finset.univ.filter (fun i => u i ≠ 0) := by
  classical
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hz
  have hlo := ((mem_dyadicBin u amp t i).mp hi).1
  rw [hz, abs_zero] at hlo
  exact (not_lt_of_ge (by positivity)) hlo

/-- The actual retained-vs-late dichotomy's late branch, directly under the
canonical iid Gaussian pair-row law. The driver, its coefficient amplitudes,
and all independence transports are constructed; none are analytic premises. -/
theorem actual_retained_late_smallball {n d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 < amp)
    (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (K J : ℝ) (hK : 1 ≤ K) (hJ : 0 < J)
    (hd : 65536*(T:ℝ) ≤ d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d)
    (q : ℕ)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (hcount : ((groups.length-q:ℕ):ℝ) ≤ J)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T))
    (hcapt : (∑ r ∈ Finset.range q, dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ •
        bilinearSynthesis (retainedGroupVector u amp groups T) X)) <
        (1/16777216:ℝ) / (Real.sqrt K * J) * Real.sqrt d *
          coefficientMass (retainedGroupVector u amp groups T)} ≤
      Real.exp (-(d:ℝ)^2/(1048576*T)) := by
  classical
  let w := retainedGroupVector u amp groups T
  let M := coefficientMass w
  obtain ⟨r, hqr, hr, ha', hmass, hsize, hwindow⟩ :=
    actual_late_driver_selection u amp ha groups T hT hreg hchain hflat d J hJ q hq hcount hM hcapt
  let t := (groups[r]?.getD []).headD 0
  let I := dyadicBin u amp t
  let a := amp*(1/2:ℝ)^(t+1)
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0:ℝ) < T := by positivity
  have hweq : ∀ i ∈ I, w i = u i := by
    intro i hi
    exact if_pos (actual_base_bin_subset_retained u amp groups T hT hreg r hr hi)
  have hmass' : M/(16*J) ≤ ∑ i ∈ I, |w i| := by
    calc
      M/(16*J) ≤ ∑ i ∈ I, |u i| := hmass
      _ = ∑ i ∈ I, |w i| := Finset.sum_congr rfl (fun i hi => by rw [hweq i hi])
  have hsize' : (I.card:ℝ) ≤ K*(d:ℝ) :=
    (show (I.card:ℝ) ≤ ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) from
      Nat.cast_le.mpr (Finset.card_le_card (dyadicBin_subset_original_support u amp ha t))).trans hsupp
  have hc0 : 0 < 1/(1024*(T:ℝ)) := by positivity
  have hc1 : 1/(1024*(T:ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0:ℝ) < 1024*T)]
    nlinarith
  have hlarge : 64 ≤ min (1/(1024*(T:ℝ))) 1 * (d:ℝ) := by
    rw [min_eq_left hc1]
    have hh : 64 ≤ (d:ℝ)/(1024*T) :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 1024*T)).2 (by nlinarith [hd])
    convert! hh using 1 <;> ring
  have hlow : 1/(1024*(T:ℝ)) * (d:ℝ) ≤ I.card := by
    convert! hsize.le using 1 <;> ring
  have hp := canonical_macroscopic_late_driver_smallball I w hc0 hlarge hlow hsize'
    (show 0 < a from ha')
    (fun i hi => by rw [hweq i hi]; exact (hwindow i hi).1.le)
    (fun i hi => by rw [hweq i hi]; exact (hwindow i hi).2)
  rw [max_eq_left hK, min_eq_left hc1] at hp
  have hroot : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by linarith)
  have hthreshold : (1/16777216:ℝ) / (Real.sqrt K * J) * Real.sqrt d * M ≤
      (1/1048576:ℝ) / Real.sqrt K * Real.sqrt d * (∑ i ∈ I, |w i|) := by
    have hh := mul_le_mul_of_nonneg_left hmass'
      (show 0 ≤ (1/1048576:ℝ) / Real.sqrt K * Real.sqrt d by positivity)
    convert! hh using 1 <;> field_simp [hroot.ne', hJ.ne'] <;> ring <;> simp
  apply (measureReal_mono (fun X (hX : _ < _) => hX.le.trans hthreshold)).trans
    (hp.trans ?_)
  apply Real.exp_le_exp.mpr
  have heq : -(1/(1024*(T:ℝ)))*(d:ℝ)^2/1024 = -(d:ℝ)^2/(1048576*T) := by ring
  exact heq.le

/-- The selected late base bin can also be tested in the original vector,
since the small-ball theorem allows arbitrary coefficients outside that bin.
This stronger late-branch estimate does not need an atom event or tail error. -/
theorem actual_original_late_smallball {n d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 < amp)
    (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (K J : ℝ) (hK : 1 ≤ K) (hJ : 0 < J)
    (hd : 65536*(T:ℝ) ≤ d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d)
    (q : ℕ)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (hcount : ((groups.length-q:ℕ):ℝ) ≤ J)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T))
    (hcapt : (∑ r ∈ Finset.range q, dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ •
        bilinearSynthesis u X)) <
        (1/16777216:ℝ) / (Real.sqrt K * J) * Real.sqrt d *
          coefficientMass (retainedGroupVector u amp groups T)} ≤
      Real.exp (-(d:ℝ)^2/(1048576*T)) := by
  classical
  let w := u
  let M := coefficientMass (retainedGroupVector u amp groups T)
  obtain ⟨r, hqr, hr, ha', hmass, hsize, hwindow⟩ :=
    actual_late_driver_selection u amp ha groups T hT hreg hchain hflat d J hJ q hq hcount hM hcapt
  let t := (groups[r]?.getD []).headD 0
  let I := dyadicBin u amp t
  let a := amp*(1/2:ℝ)^(t+1)
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0:ℝ) < T := by positivity
  have hweq : ∀ i ∈ I, w i = u i := fun _ _ => rfl
  have hmass' : M/(16*J) ≤ ∑ i ∈ I, |w i| := hmass
  have hsize' : (I.card:ℝ) ≤ K*(d:ℝ) :=
    (show (I.card:ℝ) ≤ ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) from
      Nat.cast_le.mpr (Finset.card_le_card (dyadicBin_subset_original_support u amp ha t))).trans hsupp
  have hc0 : 0 < 1/(1024*(T:ℝ)) := by positivity
  have hc1 : 1/(1024*(T:ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0:ℝ) < 1024*T)]
    nlinarith
  have hlarge : 64 ≤ min (1/(1024*(T:ℝ))) 1 * (d:ℝ) := by
    rw [min_eq_left hc1]
    have hh : 64 ≤ (d:ℝ)/(1024*T) :=
      (le_div_iff₀ (by positivity : (0:ℝ) < 1024*T)).2 (by nlinarith [hd])
    convert! hh using 1 <;> ring
  have hlow : 1/(1024*(T:ℝ)) * (d:ℝ) ≤ I.card := by
    convert! hsize.le using 1 <;> ring
  have hp := canonical_macroscopic_late_driver_smallball I w hc0 hlarge hlow hsize'
    (show 0 < a from ha')
    (fun i hi => by rw [hweq i hi]; exact (hwindow i hi).1.le)
    (fun i hi => by rw [hweq i hi]; exact (hwindow i hi).2)
  rw [max_eq_left hK, min_eq_left hc1] at hp
  have hroot : 0 < Real.sqrt K := Real.sqrt_pos.mpr (by linarith)
  have hthreshold : (1/16777216:ℝ) / (Real.sqrt K * J) * Real.sqrt d * M ≤
      (1/1048576:ℝ) / Real.sqrt K * Real.sqrt d * (∑ i ∈ I, |w i|) := by
    have hh := mul_le_mul_of_nonneg_left hmass'
      (show 0 ≤ (1/1048576:ℝ) / Real.sqrt K * Real.sqrt d by positivity)
    convert! hh using 1 <;> field_simp [hroot.ne', hJ.ne'] <;> ring <;> simp
  apply (measureReal_mono (fun X (hX : _ < _) => hX.le.trans hthreshold)).trans
    (hp.trans ?_)
  apply Real.exp_le_exp.mpr
  have heq : -(1/(1024*(T:ℝ)))*(d:ℝ)^2/1024 = -(d:ℝ)^2/(1048576*T) := by ring
  exact heq.le

end GaussianEllipsoidCandidate
