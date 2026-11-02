import ActualSparseBlock
import ActualPostprefixCrossTail

noncomputable section
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

theorem postprefixSupport_eq_biUnion {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T p : ℕ) :
    postprefixSupport u amp groups T p =
      (Ico p groups.length).biUnion (dyadicGroupSupport u amp groups T) := by
  ext i
  simp [postprefixSupport]

/-- The adapted cross coefficients in support order are precisely the retained
coefficients with the merged sparse prefix set to zero. -/
theorem ordered_postprefix_coefficients {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length) :
    (fun i => postprefixCoefficients u amp groups T p
      ((actualDyadicSupportPermutation u amp ha groups T hreg hflat).symm i) / Real.sqrt d) =
    (fun i => if i.val < supportCut (dyadicGroupSupport u amp groups T) p then 0
      else orderedRetainedCoefficients u amp ha groups T d hreg hflat i) := by
  let G := dyadicGroupSupport u amp groups T
  let hdG := actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  have hpost := permuteRows_run_restriction G hdG p groups.length hp le_rfl u
  have hret := actualDyadicSupportPermutation_retained u amp ha groups T hreg hflat
  funext i
  have hp' : postprefixCoefficients u amp groups T p (e.symm i) =
      (if supportCut G p ≤ i.val ∧ i.val < supportCut G groups.length then permuteRows e u i else 0) := by
    simpa only [postprefixCoefficients, postprefixSupport_eq_biUnion, permuteRows, e, G, actualDyadicSupportPermutation] using! congrFun hpost i
  have hr := congrFun hret i
  change permuteRows e (retainedGroupVector u amp groups T) i =
    (if i.val < supportCut G groups.length then permuteRows e u i else 0) at hr
  change postprefixCoefficients u amp groups T p (e.symm i) / Real.sqrt d =
    (if i.val < supportCut G p then 0 else permuteRows e (retainedGroupVector u amp groups T) i/Real.sqrt d)
  rw [hp', hr]
  by_cases hi : i.val < supportCut G p
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi, ite_div]

/-- The actual constructed cross observable on the original row order. -/
def actualCapturedCross {n h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid h × Euclid h) : ℝ :=
  prefixWitnessCross (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
    (fun i => postprefixCoefficients u amp groups T p
      ((actualDyadicSupportPermutation u amp ha groups T hreg hflat).symm i)/Real.sqrt d)
    (capturedBlockLo (dyadicGroupSupport u amp groups T) p q)
    (capturedBlockHi (dyadicGroupSupport u amp groups T) p q)
    (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X)

/-- Actual constructed cross-term probability after the deterministic support
permutation; all law transport, adaptedness and scalar estimates are proved. -/
theorem actualCapturedCross_lower_tail {n d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hT : 0 < T) (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hd : 0 < (d:ℝ)) (hlog : 0 < Real.log (d:ℝ))
    (hS : ∀ r, p ≤ r → r < groups.length →
      (d:ℝ)/(65536*T*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups r)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T)) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | actualCapturedCross u amp ha groups T d p q hreg hflat X ≤
        -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} ≤
      Real.exp (-(d:ℝ)^2/((2:ℝ)^67*T*Real.log (d:ℝ))) := by
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let U := orderedRetainedCoefficients u amp ha groups T d hreg hflat
  let G := dyadicGroupSupport u amp groups T
  let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
  let F : Set (Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4))) :=
    {Y | prefixWitnessCross U v (capturedBlockLo G p q) (capturedBlockHi G p q) Y ≤
      -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)}
  have hF : MeasurableSet F := measurableSet_le
    (measurable_prefixWitnessCross U v _ _ (capturedBlock_ordered G p q)) measurable_const
  change (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real (permuteRows e ⁻¹' F) ≤ _
  rw [(permuteRows_preserving e (2*(d/4)) (2*(d/4))).measureReal_preimage hF.nullMeasurableSet]
  exact actual_postprefix_cross_tail u U amp groups T p hT hreg hd hlog hS hM e.symm
    _ _ (capturedBlock_ordered G p q) (capturedBlock_separated G p q)

end GaussianEllipsoidCandidate
