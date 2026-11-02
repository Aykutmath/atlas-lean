import CapturedBlockGeometry
import ActualDyadicSupportPermutation
import ActualCrossScalars
import SparsePrefixSynthesis
import PrefixBlockInterfaces

noncomputable section
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Expose the concrete union using the ambient decidable equality instance. -/
theorem indexedGroupUnion_eq_biUnion {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T p : ℕ) :
    indexedGroupUnion u amp groups T p = (range p).biUnion (dyadicGroupSupport u amp groups T) := by
  ext i
  simp [indexedGroupUnion]

def retainedPrefixVector {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T p : ℕ) : Fin n → ℝ :=
  fun i => if i ∈ indexedGroupUnion u amp groups T p then u i else 0

theorem actual_prefix_mass_sum {n : ℕ} (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
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
    sum_biUnion (actual_group_supports_pairwise u amp ha groups T hreg hflat p hp)]
  rfl

/-- The exact normalized retained coefficients in the deterministic sample order. -/
def orderedRetainedCoefficients {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) : Fin n → ℝ :=
  fun i => permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
    (retainedGroupVector u amp groups T) i / Real.sqrt d

/-- The first ordered block is exactly the original sparse-prefix synthesis. -/
theorem ordered_sparse_prefix_synthesis {n h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length)
    (X : Fin n → Euclid h × Euclid h) :
    prefixBilinearSynthesis (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
      (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X)
      (supportCut (dyadicGroupSupport u amp groups T) p) =
    (Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis (retainedPrefixVector u amp groups T p) X := by
  classical
  let G := dyadicGroupSupport u amp groups T
  let hdG := actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  have hret := actualDyadicSupportPermutation_retained u amp ha groups T hreg hflat
  have hpre := permuteRows_prefix_restriction G hdG p hp u
  have hc : (fun i => if i.val < supportCut G p then
      orderedRetainedCoefficients u amp ha groups T d hreg hflat i else 0) =
      (Real.sqrt (d:ℝ))⁻¹ • permuteRows e (retainedPrefixVector u amp groups T p) := by
    classical
    funext i
    have hr := congrFun hret i
    have hp' := congrFun hpre i
    change permuteRows e (retainedGroupVector u amp groups T) i =
      (if i.val < supportCut G groups.length then permuteRows e u i else 0) at hr
    have hp'' : permuteRows e (retainedPrefixVector u amp groups T p) i =
        (if i.val < supportCut G p then permuteRows e u i else 0) := by
      simpa only [retainedPrefixVector, permuteRows, indexedGroupUnion_eq_biUnion, e, G, actualDyadicSupportPermutation] using hp'
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

/-- The original simultaneous sparse event supplies the literal first witness
block after deterministic reordering; no new per-vector exceptional event appears. -/
theorem actual_sparse_first_block_lower {n d : ℕ} (hd : 24 ≤ d)
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length)
    (hbudget : (supportCut (dyadicGroupSupport u amp groups T) p) ≤ sparseSupportSize d)
    (X : Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4)))
    (hX : X ∈ sparseRowsGood (2*(d/4)) n (sparseSupportSize d)) :
    Real.sqrt d/12 * (∑ r ∈ range p, dyadicGroupMass u amp groups T r) ≤
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
          (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X)
          0 (supportCut (dyadicGroupSupport u amp groups T) p))) := by
  classical
  rw [projectedPrefixBlock_zero_left, ordered_sparse_prefix_synthesis u amp ha groups T d p hreg hflat hp]
  have hcard : (indexedGroupUnion u amp groups T p).card ≤ sparseSupportSize d := by
    classical
    rw [indexedGroupUnion_eq_biUnion, support_prefix_card _
      (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl) p hp]
    exact hbudget
  have hl := sparseRowsGood_supported_nuclear_lower hd hX
    (indexedGroupUnion u amp groups T p) hcard (retainedPrefixVector u amp groups T p)
    (fun i hi => by simp [retainedPrefixVector, hi])
  rw [← coefficientMass, actual_prefix_mass_sum u amp ha groups T p hreg hflat hp] at hl
  exact hl

end GaussianEllipsoidCandidate
