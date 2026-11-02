import RealDyadicOrdering
import PaperFullHalfSparseDiagonal
import PaperExactPolarAggregation
import PaperRhoActual
import ActualRankAwareTail
import CanonicalProjectedPrefix
import RealMartingaleRadius
import PaperChernoffOptimization
import PaperGeneralRegularCluster


noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid GaussianEllipsoid.SparseSupport
open GaussianEllipsoid.PaperCanonicalPolar
open scoped BigOperators InnerProductSpace Topology
namespace GaussianEllipsoidCandidate

/-- Exact-canonical counterpart of the original captured cross observable. -/
def realActualExactCapturedCross {n h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p q : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid h × Euclid h) : ℝ :=
  exactPrefixCross (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
    (fun i => postprefixCoefficients u amp groups T p
      ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)/Real.sqrt d)
    (capturedBlockLo (dyadicGroupSupport u amp groups T) p q)
    (capturedBlockHi (dyadicGroupSupport u amp groups T) p q)
    (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X)


def real_actualCapturedProjectionBad {n h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p q : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (cproj : ℝ) : Set (Fin n → Euclid h × Euclid h) :=
  {X | ∃ r ∈ Ico p q,
    spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock
      (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
      (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X)
      (supportCut (dyadicGroupSupport u amp groups T) r)
      (supportCut (dyadicGroupSupport u amp groups T) (r+1)))) <
        cproj * Real.sqrt d * dyadicGroupMass u amp groups T r}


theorem real_paper_actual_sparse_first_block_lower {n d h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (hp : p ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (X : Fin n → Euclid h × Euclid h)
    (hX : X ∈ paperSparseSingularGood d n h) :
    (1 / 4194304 : ℝ) * Real.sqrt d *
        (∑ r ∈ range p, dyadicGroupMass u amp groups T r) ≤
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
          (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X)
          0 (supportCut (dyadicGroupSupport u amp groups T) p))) := by
  classical
  rw [projectedPrefixBlock_zero_left,
    real_ordered_sparse_prefix_synthesis ratio u amp ha groups T d p hreg hflat hp]
  have hcard : (indexedGroupUnion u amp groups T p).card ≤ sparseSupportSize d := by
    rw [indexedGroupUnion_eq_biUnion, support_prefix_card _
      (real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl) p hp]
    exact hbudget
  have hl := paperSparseSingularGood_supported_nuclear_lower hX
    (indexedGroupUnion u amp groups T p) hcard (retainedPrefixVector u amp groups T p)
    (fun i hi => by simp [retainedPrefixVector, hi])
  rw [real_actual_prefix_mass_sum ratio u amp ha groups T p hreg hflat hp] at hl
  exact hl


/-- The literal full-row E_sp, rather than a compressed subevent, supplies the
sparse diagonal. Exact polar attainment preserves the retained constant. -/
theorem real_actual_captured_retained_lower {n d h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p q : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (hpq : p ≤ q) (hq : q ≤ groups.length)
    (hbudget : supportCut (dyadicGroupSupport u amp groups T) p ≤ sparseSupportSize d)
    (cproj : ℝ) (hcproj : 0 ≤ cproj)
    (hcapt : coefficientMass (retainedGroupVector u amp groups T)/2 ≤
      ∑ j ∈ range q,dyadicGroupMass u amp groups T j)
    (X : Fin n → Euclid h × Euclid h) (hX : X ∈ paperSparseSingularGood d n h)
    (hproj : X ∉ real_actualCapturedProjectionBad ratio u amp ha groups T d p q hreg hflat cproj)
    (hcross : -((min (1/4194304:ℝ) cproj/4)*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d) ≤
      realActualExactCapturedCross ratio u amp ha groups T d p q hreg hflat X) :
    (min (1/4194304:ℝ) cproj/4)*Real.sqrt d*coefficientMass (retainedGroupVector u amp groups T) ≤
      scaledBilinearNuclear d (retainedGroupVector u amp groups T) X := by
  let G := dyadicGroupSupport u amp groups T
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
  let Y := permuteRows e X
  let mass : CapturedBlockIndex p q → ℝ := fun j => match j with
    | none => ∑ j ∈ range p,dyadicGroupMass u amp groups T j
    | some j => dyadicGroupMass u amp groups T j.val
  have hb (j : CapturedBlockIndex p q) :
      (min (1/4194304:ℝ) cproj)*Real.sqrt d*mass j ≤
      spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock U Y (capturedBlockLo G p q j) (capturedBlockHi G p q j))) := by
    cases j with
    | none =>
      have hl := real_paper_actual_sparse_first_block_lower ratio u amp ha groups T p hreg hflat
        (hpq.trans hq) hbudget X hX
      have hm : 0 ≤ mass none := sum_nonneg (fun j _ => sum_nonneg (fun i _ => abs_nonneg _))
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)) hm).trans hl
    | some j =>
      have hj := le_of_not_gt (fun hbad => hproj ⟨j.val,j.property,hbad⟩)
      have hm : 0 ≤ dyadicGroupMass u amp groups T j.val := sum_nonneg (fun i _ => abs_nonneg _)
      exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)) hm).trans hj
  have hsum : (min (1/4194304:ℝ) cproj)*Real.sqrt d*(∑ j ∈ range q,dyadicGroupMass u amp groups T j) ≤
      ∑ j : CapturedBlockIndex p q,spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock U Y (capturedBlockLo G p q j) (capturedBlockHi G p q j))) := by
    calc
      _ = ∑ j : CapturedBlockIndex p q,(min (1/4194304:ℝ) cproj)*Real.sqrt d*mass j := by
        rw [← mul_sum]
        congr 1
        exact (capturedBlock_mass_sum (dyadicGroupMass u amp groups T) p q hpq).symm
      _ ≤ _ := sum_le_sum (fun j _ => hb j)
  have halg := exact_nuclear_lower_from_captured_blocks G
    (real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl)
    p q hpq hq U Y
  rw [← real_ordered_postprefix_coefficients ratio u amp ha groups T d p hreg hflat (hpq.trans hq)] at halg
  rw [real_ordered_retained_synthesis ratio u amp ha groups T d hreg hflat X] at halg
  change _ + realActualExactCapturedCross ratio u amp ha groups T d p q hreg hflat X ≤
    scaledBilinearNuclear d (retainedGroupVector u amp groups T) X at halg
  have hc := mul_le_mul_of_nonneg_left hcapt
    (show (0:ℝ) ≤ (min (1/4194304:ℝ) cproj)*Real.sqrt d by positivity)
  nlinarith

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.real_paper_actual_sparse_first_block_lower
#print axioms GaussianEllipsoidCandidate.real_actual_captured_retained_lower


noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers
open scoped BigOperators
namespace GaussianEllipsoidCandidate

theorem real_actual_group_ordered_energy_le {n : ℕ} (ratio : ℝ) (hratio : 1 < ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio fun t => ((dyadicBin u amp t).card : ℝ)))
    (r : ℕ) (hr : r < groups.length) :
    (∑ i ∈ dyadicGroupSupport u amp groups T r,
      (u i)^2 * ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat i).val:ℝ)) ≤
      ((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))*(dyadicGroupMass u amp groups T r)^2 := by
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  have htime : ∀ i ∈ dyadicGroupSupport u amp groups T r,
      ((e i).val:ℝ) ≤ ((T:ℝ)*ratio^2/(ratio-1))*dyadicGroupScale u amp groups r := by
    intro i hi
    have hh := ((real_actualDyadicSupportPermutation_group ratio u amp ha groups T hreg hflat r hr i).mp hi).2
    have hc : ((e i).val:ℝ) ≤ (supportCut (dyadicGroupSupport u amp groups T) (r+1):ℝ) := by
      exact_mod_cast hh.le
    rw [actual_dyadic_supportCut_cast] at hc
    exact hc.trans (real_actual_support_through_bound ratio hratio u amp groups T hreg hchain r hr)
  calc
    _ ≤ ∑ i ∈ dyadicGroupSupport u amp groups T r,
        (u i)^2*(((T:ℝ)*ratio^2/(ratio-1))*dyadicGroupScale u amp groups r) :=
      sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (htime i hi) (sq_nonneg _))
    _ = ((T:ℝ)*ratio^2/(ratio-1))*((∑ i ∈ dyadicGroupSupport u amp groups T r,(u i)^2)*dyadicGroupScale u amp groups r) := by
      rw [← Finset.sum_mul]; ring
    _ ≤ ((T:ℝ)*ratio^2/(ratio-1))*((16*ratio/3)*(dyadicGroupMass u amp groups T r)^2) :=
      mul_le_mul_of_nonneg_left (real_actual_group_energy_mass_product ratio u amp groups T hreg r hr) (by positivity)
    _ = _ := by ring

/-- Exact rank-weighted deterministic variance envelope. The logarithmic loss
from the ambient-rank estimate disappears at this step. -/
theorem real_actual_retained_rank_weighted_energy {n : ℕ} (ratio : ℝ) (hratio : 1 < ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio fun t => ((dyadicBin u amp t).card : ℝ))) :
    (∑ i, (retainedGroupVector u amp groups T i)^2 *
      ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat i).val:ℝ)) ≤
      ((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  classical
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  have heq : (∑ i, (retainedGroupVector u amp groups T i)^2*((e i).val:ℝ)) =
      ∑ r ∈ range groups.length, ∑ i ∈ dyadicGroupSupport u amp groups T r,
        (u i)^2*((e i).val:ℝ) := by
    simp only [retainedGroupVector]
    simp_rw [ite_pow,zero_pow (by decide : 2 ≠ 0),ite_mul,zero_mul]
    rw [Finset.sum_ite_mem_eq,retainedGroupUnion_eq_indexed,indexedGroupUnion]
    convert! (Finset.sum_biUnion (f := fun i => (u i)^2*((e i).val:ℝ))
      (real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl)) using 1
    congr 1
    ext i
    simp only [Finset.mem_biUnion]
  rw [heq,real_actual_group_mass_sum ratio u amp ha groups T hreg hflat]
  calc
    _ ≤ ∑ r ∈ range groups.length, ((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))*(dyadicGroupMass u amp groups T r)^2 :=
      sum_le_sum (fun r hr => real_actual_group_ordered_energy_le ratio hratio u amp ha groups T hreg hflat hchain r (mem_range.mp hr))
    _ = ((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))*(∑ r ∈ range groups.length,(dyadicGroupMass u amp groups T r)^2) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_sq_le_sq_sum_of_nonneg (fun r _ => sum_nonneg (fun i _ => abs_nonneg (u i)))) (by positivity)

theorem real_actual_postprefix_rank_variance_le {n : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups, RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio fun t => ((dyadicBin u amp t).card : ℝ)))
    (d : ℝ) (hd : 0 < d) :
    (∑ i : Fin n,
      (postprefixCoefficients u amp groups T p
        ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i) / Real.sqrt d)^2 * (i.val:ℝ)) ≤
      (((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))/d)*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  classical
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
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
      ((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
    apply le_trans (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hs i) (Nat.cast_nonneg _)))
    exact real_actual_retained_rank_weighted_energy ratio hratio u amp ha groups T hreg hflat hchain
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
    _ ≤ (((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))*(coefficientMass (retainedGroupVector u amp groups T))^2)/d :=
      div_le_div_of_nonneg_right hbound hd.le
    _ = _ := by ring



/-- Counting actual disjoint nonempty record groups uses the coefficient
support, so the logarithmic prefactor does not require an ambient n bound. -/
theorem real_actual_group_count_le_support {n : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup) :
    groups.length ≤ (univ.filter fun i => u i ≠ 0).card := by
  classical
  let G := dyadicGroupSupport u amp groups T
  have hsize : ∀ j∈range groups.length,1 ≤ (G j).card := by
    intro j hj
    have hb := real_actual_group_numerical_bounds ratio u amp groups T hreg j (mem_range.mp hj)
    have hp : (0:ℝ) < ((G j).card:ℝ) := hb.1.trans_le hb.2.1
    exact Nat.succ_le_of_lt (Nat.cast_pos.mp hp)
  have hsub : (range groups.length).biUnion G ⊆ univ.filter (fun i => u i ≠ 0) := by
    intro i hi
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi
    obtain ⟨t,ht,hit⟩ := real_actual_group_support_mem_level ratio u amp groups T hreg
      j (mem_range.mp hj) i hij
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro hz
    have hl := ((mem_dyadicBin u amp t i).mp hit).1
    rw [hz,abs_zero] at hl
    exact (not_lt_of_ge (by positivity)) hl
  calc
    groups.length = ∑ j∈range groups.length,(1:ℕ) := by simp
    _ ≤ ∑ j∈range groups.length,(G j).card := sum_le_sum hsize
    _ = ((range groups.length).biUnion G).card :=
      (card_biUnion (real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl)).symm
    _ ≤ _ := card_le_card hsub

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.real_actual_group_ordered_energy_le
#print axioms GaussianEllipsoidCandidate.real_actual_retained_rank_weighted_energy
#print axioms GaussianEllipsoidCandidate.real_actual_postprefix_rank_variance_le

#print axioms GaussianEllipsoidCandidate.real_actual_group_count_le_support


noncomputable section
open Finset MeasureTheory GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoid
open GaussianEllipsoid.ProjectedClusters
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- An ordered prefix spans exactly the original selected support, independent
of the enumeration used to expose that support to the conditional law. -/
theorem prefixSpanProjector_permuted_support {n m h p : ℕ}
    (G : ℕ → Finset (Fin n)) (hd : Set.PairwiseDisjoint (↑(range m) : Set ℕ) G)
    (k : ℕ) (hk : k ≤ m) (f : Fin n → Euclid h) (eH : Fin p ↪ Fin n)
    (heH : Set.range eH=((range k).biUnion G : Set (Fin n))) :
    prefixSpanProjector (permuteRows (supportOrderPermutation G hd) f) (supportCut G k) =
      finiteSpanProjector (fun j => f (eH j)) := by
  rw [prefixSpanProjector_eq]
  unfold finiteSpanProjector
  have he : (permuteRows (supportOrderPermutation G hd) f) '' {i : Fin n | i.val < supportCut G k} =
      Set.range (fun j => f (eH j)) := by
    ext y
    constructor
    · rintro ⟨i,hi,rfl⟩
      have hm : (supportOrderPermutation G hd).symm i ∈ (range k).biUnion G := by
        apply (supportOrderPermutation_prefix_iff G hd k hk _).mpr
        simpa using hi
      have hr : (supportOrderPermutation G hd).symm i ∈ Set.range eH := by rw [heH]; exact hm
      obtain ⟨j,hj⟩ := hr
      exact ⟨j,by simp only [permuteRows]; rw [hj]⟩
    · rintro ⟨j,rfl⟩
      have hm : eH j ∈ (range k).biUnion G := by
        change eH j ∈ ((range k).biUnion G : Set (Fin n))
        rw [← heH]
        exact ⟨j,rfl⟩
      refine ⟨supportOrderPermutation G hd (eH j),?_,?_⟩
      · exact (supportOrderPermutation_prefix_iff G hd k hk _).mp hm
      · simp [permuteRows]
  rw [he]

/-- The normalized ordered current interval is the original actual group
synthesis, with every retained coefficient kept at its original value. -/
theorem real_ordered_group_synthesis {n h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d j : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup)
    (hj : j < groups.length) (X : Fin n → Euclid h × Euclid h) :
    bilinearSynthesis
      (fun i => if supportCut (dyadicGroupSupport u amp groups T) j ≤ i.val ∧
          i.val < supportCut (dyadicGroupSupport u amp groups T) (j+1)
        then real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat i else 0)
      (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X) =
    (Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis
      (fun i => if i∈dyadicGroupSupport u amp groups T j then u i else 0) X := by
  classical
  let G := dyadicGroupSupport u amp groups T
  let hdG := real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  have hret := real_actualDyadicSupportPermutation_retained ratio u amp ha groups T hreg hflat
  have hc : (fun i : Fin n => if supportCut G j ≤ i.val ∧ i.val < supportCut G (j+1)
      then real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat i else 0) =
      (fun i => (if supportCut G j ≤ i.val ∧ i.val < supportCut G (j+1)
        then permuteRows e u i else 0)/Real.sqrt d) := by
    funext i
    by_cases hi : supportCut G j ≤ i.val ∧ i.val < supportCut G (j+1)
    · have hlast : i.val < supportCut G groups.length := hi.2.trans_le (supportCut_mono G hj)
      have hh := congrFun hret i
      change permuteRows e (retainedGroupVector u amp groups T) i =
        (if i.val < supportCut G groups.length then permuteRows e u i else 0) at hh
      simp only [hlast,ite_true] at hh
      simp only [if_pos hi,real_orderedRetainedCoefficients]
      rw [hh]
    · simp only [if_neg hi,zero_div]
  rw [hc,bilinearSynthesis_div_coefficients]
  exact congrArg (fun S : Euclid h →L[ℝ] Euclid h => (Real.sqrt (d:ℝ))⁻¹ • S)
    (bilinearSynthesis_ordered_group G hdG j hj u X)


/-- Exact actual-block identity in the original full Gaussian array. The head
may be enumerated by any embedding with precisely the prior-support range. -/
theorem real_projected_ordered_tensor_identity {n h p : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d j : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup)
    (hj : j < groups.length) (eH : Fin p ↪ Fin n)
    (heH : Set.range eH=((range j).biUnion (dyadicGroupSupport u amp groups T) : Set (Fin n)))
    (z : GaussianEntries n h × GaussianEntries n h) :
    operatorFrobenius (projectedPrefixBlock
      (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
      (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat)
        (tensorToCanonicalRows n h z))
      (supportCut (dyadicGroupSupport u amp groups T) j)
      (supportCut (dyadicGroupSupport u amp groups T) (j+1))) =
    projectedBilinear
      (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
      (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
      n d z ((MeasurableEquiv.toLp 2 (Fin n → ℝ))
        (fun i => if i∈dyadicGroupSupport u amp groups T j then u i else 0)) := by
  let G := dyadicGroupSupport u amp groups T
  let hdG := real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  let X := tensorToCanonicalRows n h z
  have hleft : leftPrefixProjector (permuteRows e X) (supportCut G j) =
      finiteSpanProjector (entriesToRows p h (selectSample eH z).1) := by
    exact prefixSpanProjector_permuted_support G hdG j hj.le (fun i => (X i).2) eH heH
  have hright : rightPrefixProjector (permuteRows e X) (supportCut G j) =
      finiteSpanProjector (entriesToRows p h (selectSample eH z).2) := by
    exact prefixSpanProjector_permuted_support G hdG j hj.le (fun i => (X i).1) eH heH
  rw [projectedPrefixBlock_eq_residual _ _ (supportCut_mono _ (Nat.le_succ j)),
    real_ordered_group_synthesis ratio u amp ha groups T d j hreg hflat hj]
  have hobs := congrArg frobeniusOperator
    (scaled_bilinearSynthesis_tensorToCanonicalRows n h d
      (fun i => if i∈G j then u i else 0) z)
  rw [frobeniusOperator_operatorFrobenius] at hobs
  unfold projectedBilinear
  rw [← hobs,hleft,hright]

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.prefixSpanProjector_permuted_support
#print axioms GaussianEllipsoidCandidate.real_ordered_group_synthesis

#print axioms GaussianEllipsoidCandidate.real_projected_ordered_tensor_identity


noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid
open GaussianEllipsoid.PaperCanonicalPolar
open scoped BigOperators
namespace GaussianEllipsoidCandidate

theorem real_postprefix_coefficient_radius {n : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup)
    (d L : ℝ) (hd : 0 < d) (hlog : 0 < Real.log d) (hL : 0 < L)
    (hS : ∀ j,p ≤ j → j < groups.length → d/(L*Real.log d) ≤ dyadicGroupScale u amp groups j)
    (i : Fin n) :
    |postprefixCoefficients u amp groups T p i|/Real.sqrt d ≤
      2*L*coefficientMass (retainedGroupVector u amp groups T)*Real.log d/(d*Real.sqrt d) := by
  classical
  by_cases hi : i∈postprefixSupport u amp groups T p
  · have hi' := hi
    rw [postprefixSupport_eq_biUnion] at hi'
    obtain ⟨j,hj,hij⟩ := mem_biUnion.mp hi'
    have hn := norm_le_pi_norm (realDyadicGroupVector u amp groups T j) i
    have hn' : |u i| ≤ ‖realDyadicGroupVector u amp groups T j‖ := by
      simpa [realDyadicGroupVector,hij,Real.norm_eq_abs] using hn
    simp only [postprefixCoefficients,hi,ite_true]
    exact (div_le_div_of_nonneg_right hn' (Real.sqrt_nonneg d)).trans
      (real_actual_group_mgf_radius_le ratio u amp ha groups T p hreg hflat d L hd hlog hL hS
        j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2)
  · simp only [postprefixCoefficients,hi,ite_false,abs_zero,zero_div]
    have hm := coefficientMass_nonneg (retainedGroupVector u amp groups T)
    positivity

/-- Actual canonical captured-cross probability, arbitrary real record ratio. -/
theorem real_actual_captured_cross_tail {n d h : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T p q : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (L : ℝ) (hL : 0 < L) (hd : 0 < (d:ℝ)) (hlog : 0 < Real.log (d:ℝ))
    (hS : ∀ j,p ≤ j → j < groups.length → (d:ℝ)/(L*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups j)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T)) (x : ℝ) (hx : 0 ≤ x) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | realActualExactCapturedCross ratio u amp ha groups T d p q hreg hflat X ≤ -x} ≤
      Real.exp (-(1/4:ℝ)*min
        (x^2/(((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))/d*(coefficientMass (retainedGroupVector u amp groups T))^2))
        (x/(4*L*coefficientMass (retainedGroupVector u amp groups T)*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)))) := by
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
  let G := dyadicGroupSupport u amp groups T
  let M := coefficientMass (retainedGroupVector u amp groups T)
  let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
  let V : ℝ := ((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))/d*M^2
  let b : ℝ := 4*L*M*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd
  have hV : 0 < V := by dsimp [V,M]; positivity
  have hb : 0 < b := by dsimp [b,M]; positivity
  have hcoef (i : Fin n) : (v i)^2 ≤ b^2/2 := by
    have habs : |v i| ≤ b/2 := by
      dsimp [v]
      rw [abs_div,abs_of_pos hroot]
      have hh := real_postprefix_coefficient_radius ratio u amp ha groups T p hreg hflat d L hd hlog hL hS (e.symm i)
      apply hh.trans_eq
      dsimp [b,M]
      ring
    have hh := pow_le_pow_left₀ (abs_nonneg (v i)) habs 2
    rw [sq_abs] at hh
    nlinarith
  have hvar : (∑ i,(v i)^2*(i.val:ℝ)) ≤ V :=
    real_actual_postprefix_rank_variance_le ratio hratio u amp ha groups T p hreg hflat hchain d hd
  let E : Set (Fin n → Euclid h × Euclid h) :=
    {X | exactPrefixCross U v (capturedBlockLo G p q) (capturedBlockHi G p q) X ≤ -x}
  have hE : MeasurableSet E := measurableSet_le
    (measurable_exactPrefixCross U v _ _ (capturedBlock_ordered G p q)) measurable_const
  change (gaussianBilinearSampleLaw (Fin n) h h).real (permuteRows e ⁻¹' E) ≤ _
  rw [(permuteRows_preserving e h h).measureReal_preimage hE.nullMeasurableSet]
  exact exactPrefixCross_rank_weighted_lower_tail U v _ _ (capturedBlock_ordered G p q)
    (capturedBlock_separated G p q) V b x hV hb hx hcoef hvar


def realCrossRate (ratio : ℝ) (T : ℕ) (L a : ℝ) : ℝ :=
  (1/4)*min (a^2/((16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1)))) (a/(4*L))

theorem realCrossRate_pos (ratio : ℝ) (hratio : 1 < ratio) (T : ℕ) (hT : 0 < T)
    (L a : ℝ) (hL : 0 < L) (ha : 0 < a) : 0 < realCrossRate ratio T L a := by
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  unfold realCrossRate
  positivity

/-- The source d²/log d tail for every real q>1 and fixed positive T,L,a. -/
theorem real_actual_captured_cross_common_tail {n d h : ℕ}
    (ratio : ℝ) (hratio : 1 < ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T p q : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (L a : ℝ) (hL : 0 < L) (ha0 : 0 < a) (hd : 0 < (d:ℝ)) (hlog : 1 ≤ Real.log (d:ℝ))
    (hS : ∀ j,p ≤ j → j < groups.length → (d:ℝ)/(L*Real.log (d:ℝ)) ≤ dyadicGroupScale u amp groups j)
    (hM : 0 < coefficientMass (retainedGroupVector u amp groups T)) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | realActualExactCapturedCross ratio u amp ha groups T d p q hreg hflat X ≤
        -(a*coefficientMass (retainedGroupVector u amp groups T)*Real.sqrt d)} ≤
      Real.exp (-realCrossRate ratio T L a*(d:ℝ)^2/Real.log (d:ℝ)) := by
  let M := coefficientMass (retainedGroupVector u amp groups T)
  let C : ℝ := (16*ratio/3)*((T:ℝ)*ratio^2/(ratio-1))
  let V : ℝ := C/d*M^2
  let b : ℝ := 4*L*M*Real.log (d:ℝ)/((d:ℝ)*Real.sqrt d)
  let x : ℝ := a*M*Real.sqrt d
  have hratio0 : 0 < ratio := by linarith
  have hden : 0 < ratio-1 := by linarith
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hroot : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd
  have hC : 0 < C := by dsimp [C]; positivity
  have hV : 0 < V := by dsimp [V,M]; positivity
  have hb : 0 < b := by dsimp [b,M]; positivity
  have hx : 0 ≤ x := by dsimp [x,M]; positivity
  have ht := real_actual_captured_cross_tail (h:=h) ratio hratio u amp ha groups T p q hT hreg hflat hchain
    L hL hd hlog0 hS hM x hx
  have hr := paper_martingale_threshold_ratios a M d C (4*L) V b ha0.le hM hd hC (by positivity) hV hb
    (by dsimp [V]; ring_nf; exact le_rfl) (by dsimp [b]; exact le_rfl)
  have hrat : min (a^2/C) (a/(4*L))*(d:ℝ)^2/Real.log (d:ℝ) ≤ min (x^2/V) (x/b) := by
    apply le_min
    · calc
        _ ≤ (a^2/C)*(d:ℝ)^2/Real.log (d:ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)) hlog0.le
        _ ≤ (a^2/C)*(d:ℝ)^2 := div_le_self (by positivity) hlog
        _ = a^2*(d:ℝ)^2/C := by ring
        _ ≤ _ := hr.1
    · calc
        _ ≤ (a/(4*L))*(d:ℝ)^2/Real.log (d:ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)) hlog0.le
        _ = a*(d:ℝ)^2/((4*L)*Real.log (d:ℝ)) := by ring
        _ ≤ _ := hr.2
  apply ht.trans
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonpos_left hrat (show -(1/4:ℝ) ≤ 0 by norm_num)
  apply he.trans_eq
  dsimp [realCrossRate,C]
  ring

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.real_postprefix_coefficient_radius
#print axioms GaussianEllipsoidCandidate.real_actual_captured_cross_tail

#print axioms GaussianEllipsoidCandidate.real_actual_captured_cross_common_tail


noncomputable section
open GaussianEllipsoid.ProjectedClusters
namespace GaussianEllipsoidCandidate

/-- Chosen after q's regular-cluster constants and before T,K,d,n,u. -/
def realProofRho (q : ℝ) : ℝ :=
  min (1/8) (generalUp (1/4) (8*q)/(32*q^2))/2

/-- Positive retained numerator, depending only on q and not on T or K. -/
def realRetainedBase (q : ℝ) : ℝ :=
  min (min (1/4194304) (generalProj (1/4) (8*q))/4) ((1/1048576)/(8*q))

def realLateBudget (q : ℝ) (T : ℕ) (K : ℝ) : ℝ :=
  1+Real.log ((q^2/(q-1))*max K 1*T/realProofRho q)/Real.log q

def realRetainedConstant (q : ℝ) (T : ℕ) (K : ℝ) : ℝ :=
  realRetainedBase q/(Real.sqrt (max K 1)*realLateBudget q T K)

theorem realProofRho_admissible (q : ℝ) (hq : 1 < q) :
    0 < realProofRho q ∧ realProofRho q <
      min (1/8) (generalUp (1/4) (8*q)/(32*q^2)) := by
  have hq0 : 0 < q := by linarith
  have hu := (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*q)).2.1
  have hm : 0 < min (1/8:ℝ) (generalUp (1/4) (8*q)/(32*q^2)) := by positivity
  unfold realProofRho
  exact ⟨by positivity,by linarith⟩

theorem realRetainedBase_pos (q : ℝ) (hq : 1 < q) : 0 < realRetainedBase q := by
  have hq0 : 0 < q := by linarith
  have hp := (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*q)).2.2
  unfold realRetainedBase
  positivity

/-- J≥1 is established uniformly before the coefficient vector is chosen;
it does not rely on a nonempty late branch. -/
theorem realLateBudget_ge_one (q : ℝ) (hq : 1 < q) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    1 ≤ realLateBudget q T K := by
  have hqm : 0 < q-1 := by linarith
  have hq0 : 0 < q := by linarith
  have hC : 1 ≤ q^2/(q-1) := (le_div_iff₀ hqm).mpr (by nlinarith [sq_nonneg (q-1)])
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hprod : 1 ≤ (q^2/(q-1))*max K 1*T :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (le_max_right K 1)) hTr
  have hr := realProofRho_admissible q hq
  have hr1 : realProofRho q < 1 := by
    have hh := hr.2.trans_le (min_le_left _ _)
    linarith
  have harg : 1 ≤ ((q^2/(q-1))*max K 1*T)/realProofRho q :=
    (le_div_iff₀ hr.1).mpr (by linarith)
  have hl := Real.log_nonneg harg
  have hlogq : 0 < Real.log q := Real.log_pos hq
  unfold realLateBudget
  exact le_add_of_nonneg_right (div_nonneg hl hlogq.le)

theorem realRetainedConstant_pos (q : ℝ) (hq : 1 < q) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    0 < realRetainedConstant q T K := by
  have hb := realRetainedBase_pos q hq
  have hJ := realLateBudget_ge_one q hq T hT K
  have hK : 0 < max K 1 := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  unfold realRetainedConstant
  positivity

theorem realRetainedConstant_le_captured (q : ℝ) (hq : 1 < q) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    realRetainedConstant q T K ≤ min (1/4194304:ℝ) (generalProj (1/4) (8*q))/4 := by
  have hbase := (realRetainedBase_pos q hq).le
  have hJ := realLateBudget_ge_one q hq T hT K
  have hK : 1 ≤ Real.sqrt (max K 1) := by simpa using Real.sqrt_le_sqrt (le_max_right K 1)
  have hden := one_le_mul_of_one_le_of_one_le hK hJ
  exact (div_le_self hbase hden).trans (min_le_left _ _)

theorem realRetainedConstant_le_late (q : ℝ) (hq : 1 < q) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    realRetainedConstant q T K ≤
      (1/1048576:ℝ)/(8*q*Real.sqrt (max K 1)*realLateBudget q T K) := by
  have hJ := realLateBudget_ge_one q hq T hT K
  have hK : 0 < max K 1 := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hh := div_le_div_of_nonneg_right (min_le_right
    (min (1/4194304:ℝ) (generalProj (1/4) (8*q))/4) ((1/1048576:ℝ)/(8*q)))
    (show 0 ≤ Real.sqrt (max K 1)*realLateBudget q T K by positivity)
  apply hh.trans_eq
  ring

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.realProofRho_admissible
#print axioms GaussianEllipsoidCandidate.realRetainedBase_pos
#print axioms GaussianEllipsoidCandidate.realLateBudget_ge_one
#print axioms GaussianEllipsoidCandidate.realRetainedConstant_pos
#print axioms GaussianEllipsoidCandidate.realRetainedConstant_le_captured
#print axioms GaussianEllipsoidCandidate.realRetainedConstant_le_late

namespace GaussianEllipsoidCandidate
/-- Empty postprefix for arbitrary real-q groups: total retained mass may still
be positive, but the future cross sum vanishes identically. -/
theorem real_actual_zero_future_tail {n d h : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T p b : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup ratio u amp T g) (hflat : groups.flatten.Nodup)
    (hp : groups.length ≤ p) (x : ℝ) (hx : 0 < x) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | realActualExactCapturedCross ratio u amp ha groups T d p b hreg hflat X ≤ -x}=0 := by
  apply paper_zero_future_tail _ _ _ x hx
  apply Filter.Eventually.of_forall
  intro X
  simp [realActualExactCapturedCross,postprefixCoefficients,postprefixSupport,
    Finset.Ico_eq_empty_of_le hp,GaussianEllipsoid.PaperCanonicalPolar.exactPrefixCross]
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.real_actual_zero_future_tail

namespace GaussianEllipsoidCandidate
/-- Free-rho source logarithmic budget; rho is fixed before T,K,d,u. -/
def realLateBudgetAt (q rho : ℝ) (T : ℕ) (K : ℝ) : ℝ :=
  1+Real.log ((q^2/(q-1))*max K 1*T/rho)/Real.log q

def realRetainedConstantAt (q rho : ℝ) (T : ℕ) (K : ℝ) : ℝ :=
  realRetainedBase q/(Real.sqrt (max K 1)*realLateBudgetAt q rho T K)

theorem realLateBudgetAt_ge_one (q : ℝ) (hq : 1 < q) (rho : ℝ)
    (hrho : 0 < rho) (hrcap : rho < 1/8) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    1 ≤ realLateBudgetAt q rho T K := by
  have hqm : 0 < q-1 := by linarith
  have hq0 : 0 < q := by linarith
  have hC : 1 ≤ q^2/(q-1) := (le_div_iff₀ hqm).mpr (by nlinarith [sq_nonneg (q-1)])
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hprod : 1 ≤ (q^2/(q-1))*max K 1*T :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (le_max_right K 1)) hTr
  have harg : 1 ≤ ((q^2/(q-1))*max K 1*T)/rho := (le_div_iff₀ hrho).mpr (by linarith)
  have hl := Real.log_nonneg harg
  unfold realLateBudgetAt
  exact le_add_of_nonneg_right (div_nonneg hl (Real.log_pos hq).le)

theorem realRetainedConstantAt_pos (q : ℝ) (hq : 1 < q) (rho : ℝ)
    (hrho : 0 < rho) (hrcap : rho < 1/8) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    0 < realRetainedConstantAt q rho T K := by
  have hb := realRetainedBase_pos q hq
  have hJ := realLateBudgetAt_ge_one q hq rho hrho hrcap T hT K
  have hK : 0 < max K 1 := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  unfold realRetainedConstantAt
  positivity

theorem realRetainedConstantAt_le_captured (q : ℝ) (hq : 1 < q) (rho : ℝ)
    (hrho : 0 < rho) (hrcap : rho < 1/8) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    realRetainedConstantAt q rho T K ≤ min (1/4194304:ℝ) (generalProj (1/4) (8*q))/4 := by
  have hbase := (realRetainedBase_pos q hq).le
  have hJ := realLateBudgetAt_ge_one q hq rho hrho hrcap T hT K
  have hK : 1 ≤ Real.sqrt (max K 1) := by simpa using Real.sqrt_le_sqrt (le_max_right K 1)
  exact (div_le_self hbase (one_le_mul_of_one_le_of_one_le hK hJ)).trans (min_le_left _ _)

theorem realRetainedConstantAt_le_late (q : ℝ) (hq : 1 < q) (rho : ℝ)
    (hrho : 0 < rho) (hrcap : rho < 1/8) (T : ℕ) (hT : 0 < T) (K : ℝ) :
    realRetainedConstantAt q rho T K ≤
      (1/1048576:ℝ)/(8*q*Real.sqrt (max K 1)*realLateBudgetAt q rho T K) := by
  have hJ := realLateBudgetAt_ge_one q hq rho hrho hrcap T hT K
  have hK : 0 < max K 1 := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  have hh := div_le_div_of_nonneg_right (min_le_right
    (min (1/4194304:ℝ) (generalProj (1/4) (8*q))/4) ((1/1048576:ℝ)/(8*q)))
    (show 0 ≤ Real.sqrt (max K 1)*realLateBudgetAt q rho T K by positivity)
  apply hh.trans_eq
  ring

theorem realRetainedConstantAt_chosen (q : ℝ) (T : ℕ) (K : ℝ) :
    realRetainedConstantAt q (realProofRho q) T K=realRetainedConstant q T K := rfl
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.realLateBudgetAt_ge_one
#print axioms GaussianEllipsoidCandidate.realRetainedConstantAt_pos
#print axioms GaussianEllipsoidCandidate.realRetainedConstantAt_le_captured
#print axioms GaussianEllipsoidCandidate.realRetainedConstantAt_le_late
