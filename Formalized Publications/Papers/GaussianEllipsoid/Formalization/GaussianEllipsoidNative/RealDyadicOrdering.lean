/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Native verification pending; proof adaptations preserve arbitrary real ratio. -/
import RealDyadicPaper
import ActualCapturedDeterministic

noncomputable section
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

def real_actualDyadicSupportPermutation {n : ℕ} (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) : Equiv.Perm (Fin n) :=
  supportOrderPermutation (dyadicGroupSupport u amp groups T)
    (real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl)

theorem real_actualDyadicSupportPermutation_group {n : ℕ} (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (j : ℕ) (hj : j < groups.length) (i : Fin n) :
    i ∈ dyadicGroupSupport u amp groups T j ↔
      supportCut (dyadicGroupSupport u amp groups T) j ≤
        (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat i).val ∧
      (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat i).val <
        supportCut (dyadicGroupSupport u amp groups T) (j+1) :=
  supportOrderPermutation_mem_iff _ _ j hj i

theorem real_actualDyadicSupportPermutation_retained {n : ℕ} (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) :
    permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat)
      (retainedGroupVector u amp groups T) =
    fun i => if i.val < supportCut (dyadicGroupSupport u amp groups T) groups.length
      then permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) u i
      else 0 := by
  classical
  have heq : retainedGroupVector u amp groups T =
      fun i => if i ∈ (range groups.length).biUnion (dyadicGroupSupport u amp groups T)
        then u i else 0 := by
    funext i
    simp only [retainedGroupVector,retainedGroupUnion_eq_indexed,indexedGroupUnion,mem_biUnion]
  rw [heq]
  exact permuteRows_prefix_restriction _ _ groups.length le_rfl u

theorem real_actual_prefix_mass_sum {n : ℕ} (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length) :
    coefficientMass (retainedPrefixVector u amp groups T p) =
      ∑ r ∈ range p, dyadicGroupMass u amp groups T r := by
  classical
  have heq : coefficientMass (retainedPrefixVector u amp groups T p) =
      ∑ i ∈ indexedGroupUnion u amp groups T p, |u i| := by
    classical
    dsimp [coefficientMass, retainedPrefixVector]
    simp_rw [apply_ite abs]
    simp
  rw [heq, indexedGroupUnion_eq_biUnion,
    sum_biUnion (real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat p hp)]
  rfl

def real_orderedRetainedCoefficients {n : ℕ} (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) : Fin n → ℝ :=
  fun i => permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat)
    (retainedGroupVector u amp groups T) i / Real.sqrt d

theorem real_ordered_sparse_prefix_synthesis {n h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length)
    (X : Fin n → Euclid h × Euclid h) :
    prefixBilinearSynthesis (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
      (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X)
      (supportCut (dyadicGroupSupport u amp groups T) p) =
    (Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis (retainedPrefixVector u amp groups T p) X := by
  classical
  let G := dyadicGroupSupport u amp groups T
  let hdG := real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  have hret := real_actualDyadicSupportPermutation_retained ratio u amp ha groups T hreg hflat
  have hpre := permuteRows_prefix_restriction G hdG p hp u
  have hc : (fun i => if i.val < supportCut G p then
      real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat i else 0) =
      (Real.sqrt (d:ℝ))⁻¹ • permuteRows e (retainedPrefixVector u amp groups T p) := by
    classical
    funext i
    have hr := congrFun hret i
    have hp' := congrFun hpre i
    change permuteRows e (retainedGroupVector u amp groups T) i =
      (if i.val < supportCut G groups.length then permuteRows e u i else 0) at hr
    have hp'' : permuteRows e (retainedPrefixVector u amp groups T p) i =
        (if i.val < supportCut G p then permuteRows e u i else 0) := by
      simpa only [retainedPrefixVector, permuteRows, indexedGroupUnion_eq_biUnion, e, G, real_actualDyadicSupportPermutation] using hp'
    change (if i.val < supportCut G p then
      permuteRows e (retainedGroupVector u amp groups T) i / Real.sqrt d else 0) =
      (Real.sqrt (d:ℝ))⁻¹ * permuteRows e (retainedPrefixVector u amp groups T p) i
    rw [hp'', hr]
    by_cases hi : i.val < supportCut G p
    · rw [if_pos hi, if_pos (hi.trans_le (supportCut_mono G hp)), if_pos hi]
      ring
    · simp [hi]
  unfold prefixBilinearSynthesis
  rw [hc]
  change synthesis (fun i => bilinearRowOperator (permuteRows e X i))
      ((Real.sqrt (d:ℝ))⁻¹ • permuteRows e (retainedPrefixVector u amp groups T p)) = _
  rw [synthesis_smul]
  exact congrArg (fun S : Euclid h →L[ℝ] Euclid h => (Real.sqrt (d:ℝ))⁻¹ • S)
    (bilinearSynthesis_permuteRows e (retainedPrefixVector u amp groups T p) X)

theorem real_ordered_postprefix_coefficients {n : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length) :
    (fun i => postprefixCoefficients u amp groups T p
      ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i) / Real.sqrt d) =
    (fun i => if i.val < supportCut (dyadicGroupSupport u amp groups T) p then 0
      else real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat i) := by
  let G := dyadicGroupSupport u amp groups T
  let hdG := real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  have hpost := permuteRows_run_restriction G hdG p groups.length hp le_rfl u
  have hret := real_actualDyadicSupportPermutation_retained ratio u amp ha groups T hreg hflat
  funext i
  have hp' : postprefixCoefficients u amp groups T p (e.symm i) =
      (if supportCut G p ≤ i.val ∧ i.val < supportCut G groups.length then permuteRows e u i else 0) := by
    simpa only [postprefixCoefficients, postprefixSupport_eq_biUnion, permuteRows, e, G, real_actualDyadicSupportPermutation] using! congrFun hpost i
  have hr := congrFun hret i
  change permuteRows e (retainedGroupVector u amp groups T) i =
    (if i.val < supportCut G groups.length then permuteRows e u i else 0) at hr
  change postprefixCoefficients u amp groups T p (e.symm i) / Real.sqrt d =
    (if i.val < supportCut G p then 0 else permuteRows e (retainedGroupVector u amp groups T) i/Real.sqrt d)
  rw [hp', hr]
  by_cases hi : i.val < supportCut G p
  · simp [hi, Nat.not_le.mpr hi]
  · simp [hi, Nat.le_of_not_gt hi, ite_div]

theorem real_ordered_retained_synthesis {n h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid h × Euclid h) :
    bilinearSynthesis (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
      (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X) =
      (Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis (retainedGroupVector u amp groups T) X := by
  unfold real_orderedRetainedCoefficients
  rw [bilinearSynthesis_div_coefficients]
  exact congrArg (fun S : Euclid h →L[ℝ] Euclid h => (Real.sqrt (d:ℝ))⁻¹ • S)
    (bilinearSynthesis_permuteRows _ _ _)

end GaussianEllipsoidCandidate
