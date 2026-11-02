import PrefixWitnessRankEnergy

noncomputable section
set_option maxHeartbeats 600000
open Finset MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- The actual post-prefix coefficients in deterministic support order have a
rank-weighted variance bound without the old logarithmic loss. -/
theorem actual_postprefix_rank_variance_le {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (d : ℝ) (hd : 0 < d) :
    (∑ i : Fin n,
      (postprefixCoefficients u amp groups T p
        ((actualDyadicSupportPermutation u amp ha groups T hreg hflat).symm i) / Real.sqrt d)^2 * (i.val:ℝ)) ≤
      ((128/3:ℝ)*T/d)*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  classical
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let v := postprefixCoefficients u amp groups T p
  have hsub : postprefixSupport u amp groups T p ⊆ retainedGroupUnion u amp groups T := by
    intro i hi
    rw [postprefixSupport_eq_biUnion] at hi
    obtain ⟨j,hj,hi⟩ := mem_biUnion.mp hi
    rw [retainedGroupUnion_eq_indexed,indexedGroupUnion_eq_biUnion]
    exact mem_biUnion.mpr ⟨j,mem_range.mpr (mem_Ico.mp hj).2,hi⟩
  have hs (i : Fin n) : (v i)^2 ≤ (retainedGroupVector u amp groups T i)^2 := by
    by_cases hi : i ∈ postprefixSupport u amp groups T p
    · simp only [v,postprefixCoefficients,retainedGroupVector,hi,hsub hi,ite_true]
      exact le_rfl
    · simp only [v,postprefixCoefficients,hi,ite_false,zero_pow (by decide : 2 ≠ 0)]
      positivity
  have hbound : (∑ i, (v i)^2*((e i).val:ℝ)) ≤
      (128/3:ℝ)*T*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
    apply le_trans (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hs i) (Nat.cast_nonneg _)))
    exact actual_retained_rank_weighted_energy u amp ha groups T hreg hflat hchain
  have heq : (∑ i : Fin n, (v (e.symm i))^2*(i.val:ℝ)) =
      ∑ i, (v i)^2*((e i).val:ℝ) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun i : Fin n => (v (e.symm i))^2*(i.val:ℝ))).symm
  change (∑ i : Fin n, (v (e.symm i)/Real.sqrt d)^2*(i.val:ℝ)) ≤ _
  calc
    _ = (∑ i : Fin n, (v (e.symm i))^2*(i.val:ℝ))/d := by
      simp_rw [div_pow,Real.sq_sqrt hd.le,div_mul_eq_mul_div]
      rw [Finset.sum_div]
    _ = (∑ i, (v i)^2*((e i).val:ℝ))/d := by rw [heq]
    _ ≤ ((128/3:ℝ)*T*(coefficientMass (retainedGroupVector u amp groups T))^2)/d :=
      div_le_div_of_nonneg_right hbound hd.le
    _ = _ := by ring

/-- Concrete actual cross-term Bernstein inequality with the sharper
predictable variance C*T*M²/d. Ambient dimensions have no parity restriction. -/
theorem actualCapturedCross_rank_aware_tail {n d h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hT : 0 < T) (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hd : 0 < (d:ℝ)) (hlog : 0 < Real.log (d:ℝ))
    (hS : ∀ j, p ≤ j → j < groups.length →
      (d:ℝ)/(65536*T*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups j)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T))
    (x : ℝ) (hx : 0 ≤ x) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | actualCapturedCross u amp ha groups T d p q hreg hflat X ≤ -x} ≤
      Real.exp (-(1/4:ℝ)*min
        (x^2 / (((128/3:ℝ)*T/d)*(coefficientMass (retainedGroupVector u amp groups T))^2))
        (x / ((2:ℝ)^18*T*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)*
          coefficientMass (retainedGroupVector u amp groups T)))) := by
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let U := orderedRetainedCoefficients u amp ha groups T d hreg hflat
  let G := dyadicGroupSupport u amp groups T
  let M := coefficientMass (retainedGroupVector u amp groups T)
  let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
  let V : ℝ := (128/3:ℝ)*T/d*M^2
  let b : ℝ := (2:ℝ)^18*T*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)*M
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd
  have hV : 0 < V := by dsimp [V,M]; positivity
  have hb : 0 < b := by dsimp [b,M]; positivity
  have hc := actual_postprefix_log_cap_energy u amp groups T p hT hreg d hd hlog hS
  have hcoef (i : Fin n) : (v i)^2 ≤ b^2/2 := by
    have habs : |v i| ≤ b/2 := by
      dsimp [v]
      rw [abs_div,abs_of_pos hroot]
      apply (div_le_iff₀ hroot).mpr
      have hi := hc.1 (e.symm i)
      have heq : b/2*Real.sqrt (d:ℝ) =
          131072*T*Real.log (d:ℝ)/(d:ℝ)*M := by
        dsimp [b]
        field_simp [hd.ne',hroot.ne']
        ring
      rw [heq]
      exact hi
    have hs := pow_le_pow_left₀ (abs_nonneg (v i)) habs 2
    rw [sq_abs] at hs
    nlinarith
  have hv : (∑ i, (v i)^2*(i.val:ℝ)) ≤ V :=
    actual_postprefix_rank_variance_le u amp ha groups T p hreg hflat hchain d hd
  let F : Set (Fin n → Euclid h × Euclid h) :=
    {X | prefixWitnessCross U v (capturedBlockLo G p q) (capturedBlockHi G p q) X ≤ -x}
  have hF : MeasurableSet F := measurableSet_le
    (measurable_prefixWitnessCross U v _ _ (capturedBlock_ordered G p q)) measurable_const
  change (gaussianBilinearSampleLaw (Fin n) h h).real (permuteRows e ⁻¹' F) ≤ _
  rw [(permuteRows_preserving e h h).measureReal_preimage hF.nullMeasurableSet]
  exact prefixWitnessCross_rank_weighted_lower_tail U v _ _
    (capturedBlock_ordered G p q) (capturedBlock_separated G p q) V b x hV hb hx hcoef hv
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.actual_postprefix_rank_variance_le

#print axioms GaussianEllipsoidCandidate.actualCapturedCross_rank_aware_tail
