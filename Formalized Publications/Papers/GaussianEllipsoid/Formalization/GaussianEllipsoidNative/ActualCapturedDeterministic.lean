import ActualCapturedCross
import ActualFixedVectorReduction

noncomputable section
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoid.SparseSupport
open scoped BigOperators
namespace GaussianEllipsoidCandidate

theorem bilinearSynthesis_div_coefficients {n r s : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid s × Euclid r) (c : ℝ) :
    bilinearSynthesis (fun i => u i/c) X = c⁻¹ • bilinearSynthesis u X := by
  have heq : (fun i => u i/c) = c⁻¹ • u := by ext i; simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  exact synthesis_smul (fun i => bilinearRowOperator (X i)) c⁻¹ u

theorem ordered_retained_synthesis {n h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid h × Euclid h) :
    bilinearSynthesis (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
      (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X) =
      (Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis (retainedGroupVector u amp groups T) X := by
  unfold orderedRetainedCoefficients
  rw [bilinearSynthesis_div_coefficients, actualDyadicSupportPermutation_synthesis]

/-- Failure of at least one literal captured projected group on the original
Gaussian sample; the deterministic row permutation is part of the observable. -/
def actualCapturedProjectionBad {n h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) : Set (Fin n → Euclid h × Euclid h) :=
  {X | ∃ r ∈ Ico p q,
    spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock
      (orderedRetainedCoefficients u amp ha groups T d hreg hflat)
      (permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat) X)
      (supportCut (dyadicGroupSupport u amp groups T) r)
      (supportCut (dyadicGroupSupport u amp groups T) (r+1)))) <
        ProjectedClusters.projectedConstant * Real.sqrt d * dyadicGroupMass u amp groups T r}

/-- Sparse and projected diagonals, actual constructed witnesses, and the
actual cross term yield the common retained lower bound pathwise. -/
theorem actual_captured_retained_lower {n d : ℕ} (hd : 24 ≤ d)
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hflat : groups.flatten.Nodup) (hpq : p ≤ q) (hq : q ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 1 ≤ J)
    (hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ r ∈ range q, dyadicGroupMass u amp groups T r)
    (X : Fin n → Euclid (2*(d/4)) × Euclid (2*(d/4)))
    (hX : X ∈ sparseRowsGood (2*(d/4)) n (sparseSupportSize d))
    (hproj : X ∉ actualCapturedProjectionBad u amp ha groups T d p q hreg hflat)
    (hcross : -((1/2:ℝ)^24*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d) ≤
      actualCapturedCross u amp ha groups T d p q hreg hflat X) :
    ((1/2:ℝ)^24/(Real.sqrt K*J))*Real.sqrt d*coefficientMass (retainedGroupVector u amp groups T) ≤
      scaledBilinearNuclear d (retainedGroupVector u amp groups T) X := by
  let G := dyadicGroupSupport u amp groups T
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let U := orderedRetainedCoefficients u amp ha groups T d hreg hflat
  let Y := permuteRows e X
  let mass : CapturedBlockIndex p q → ℝ := fun j => match j with
    | none => ∑ r ∈ range p, dyadicGroupMass u amp groups T r
    | some r => dyadicGroupMass u amp groups T r.val
  have hb (j : CapturedBlockIndex p q) :
      ProjectedClusters.projectedConstant * Real.sqrt d * mass j ≤
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock U Y (capturedBlockLo G p q j) (capturedBlockHi G p q j))) := by
    cases j with
    | none =>
      have hs := actual_sparse_first_block_lower hd u amp ha groups T p hreg hflat
        (hpq.trans hq) hbudget X hX
      have hmass : 0 ≤ ∑ r ∈ range p, dyadicGroupMass u amp groups T r := by
        exact sum_nonneg (fun r _ => sum_nonneg (fun i _ => abs_nonneg _))
      have hc : ProjectedClusters.projectedConstant ≤ 1/12 :=
        ProjectedClusters.projectedConstant_le_exponent.trans (by norm_num)
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg (d:ℝ))) hmass
      apply le_trans _ hs
      convert hh using 1 <;> ring
    | some r =>
      exact le_of_not_gt (fun hbad => hproj ⟨r.val, r.property, hbad⟩)
  have hsum : ProjectedClusters.projectedConstant * Real.sqrt d *
      (∑ r ∈ range q, dyadicGroupMass u amp groups T r) ≤
      ∑ j : CapturedBlockIndex p q, spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock U Y (capturedBlockLo G p q j) (capturedBlockHi G p q j))) := by
    calc
      _ = ∑ j : CapturedBlockIndex p q, ProjectedClusters.projectedConstant * Real.sqrt d * mass j := by
        rw [← mul_sum]
        congr 1
        exact (capturedBlock_mass_sum (dyadicGroupMass u amp groups T) p q hpq).symm
      _ ≤ _ := sum_le_sum (fun j _ => hb j)
  have halg := nuclear_lower_from_captured_blocks G
    (actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl)
    p q hpq hq U Y
  rw [← ordered_postprefix_coefficients u amp ha groups T d p hreg hflat (hpq.trans hq)] at halg
  rw [ordered_retained_synthesis u amp ha groups T d hreg hflat X] at halg
  apply captured_mass_cross_absorption K J d
    (coefficientMass (retainedGroupVector u amp groups T))
    (∑ r ∈ range q, dyadicGroupMass u amp groups T r)
    (scaledBilinearNuclear d (retainedGroupVector u amp groups T) X)
    hK hJ (Nat.cast_nonneg _) (coefficientMass_nonneg _) hcapt
  change _ ≤ spectralNuclearNorm (operatorFrobenius
    ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis (retainedGroupVector u amp groups T) X))
  change _ ≤ actualCapturedCross u amp ha groups T d p q hreg hflat X at hcross
  change _ + actualCapturedCross u amp ha groups T d p q hreg hflat X ≤ _ at halg
  linarith

end GaussianEllipsoidCandidate
