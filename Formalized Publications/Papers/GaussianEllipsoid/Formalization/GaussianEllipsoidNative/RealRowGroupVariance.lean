import RealDyadicOrdering
import PaperExactCompensator
import PaperCapturedCompensator
import RealPredictableVariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
open Finset MeasureTheory GaussianEllipsoid GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperCanonicalPolar

/-- No captured block endpoint lies strictly inside an actual group interval.
The none endpoint is the whole sparse prefix, and every some endpoint is a
whole retained-group endpoint. Repeated cuts and empty groups are allowed. -/
theorem captured_endpoint_le_iff_at_group_start {n : ℕ}
    (G : ℕ → Finset (Fin n)) (p b j t : ℕ) (hpj : p≤j)
    (hlo : supportCut G j≤t) (hhi : t<supportCut G (j+1))
    (a : CapturedBlockIndex p b) :
    capturedBlockHi G p b a≤t ↔ capturedBlockHi G p b a≤ supportCut G j := by
  cases a with
  | none =>
    have hc := supportCut_mono G hpj
    simp only [capturedBlockHi]
    exact ⟨fun _ => hc, fun h => h.trans hlo⟩
  | some a =>
    dsimp only [capturedBlockHi]
    by_cases haj : a.val<j
    · have hc := supportCut_mono G (show a.val+1≤j by omega)
      exact ⟨fun _ => hc,fun h => h.trans hlo⟩
    · have hc := supportCut_mono G (show j+1≤a.val+1 by omega)
      have hn : ¬supportCut G (a.val+1)≤t := by omega
      have hn' : ¬supportCut G (a.val+1)≤ supportCut G j := by omega
      simp only [hn,hn']

/-- The exact completed captured witness is constant during each current group,
including groups after the capture cutoff b. The full captured family is fixed. -/
theorem exactCapturedPrefix_constant_on_group {n r q : ℕ}
    (G : ℕ → Finset (Fin n)) (p b j t : ℕ) (hpj : p≤j)
    (hlo : supportCut G j≤t) (hhi : t<supportCut G (j+1))
    (w : Fin n → ℝ) (Y : Fin n → Euclid q × Euclid r) :
    exactCompletedPrefix w (capturedBlockLo G p b) (capturedBlockHi G p b) Y t =
      exactCompletedPrefix w (capturedBlockLo G p b) (capturedBlockHi G p b) Y (supportCut G j) := by
  unfold exactCompletedPrefix completedSupportedPrefix
  apply Finset.sum_congr rfl
  intro a _
  have he := captured_endpoint_le_iff_at_group_start G p b j t hpj hlo hhi a
  by_cases ht : capturedBlockHi G p b a ≤ t
  · have hs := he.mp ht
    simp only [if_pos ht,if_pos hs]
  · have hs : ¬capturedBlockHi G p b a ≤ supportCut G j := fun h => ht (he.mpr h)
    simp only [if_neg ht,if_neg hs]

end GaussianEllipsoid.PaperCanonicalPolar
namespace GaussianEllipsoidCandidate
open GaussianEllipsoid.PaperCanonicalPolar

/-- Exact reindexing and grouping of the actual normalized postprefix coefficient
squares against any weight constant on each actual group interval. -/
theorem real_postprefix_weighted_group_sum {n : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (f : ℕ → ℝ)
    (hf : ∀ j,p≤j → j<groups.length → ∀ t,
      supportCut (dyadicGroupSupport u amp groups T) j≤t →
      t<supportCut (dyadicGroupSupport u amp groups T) (j+1) →
      f t=f (supportCut (dyadicGroupSupport u amp groups T) j)) :
    (∑ i : Fin n,
      (postprefixCoefficients u amp groups T p
        ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)/Real.sqrt d)^2*f i.val) =
    ∑ j ∈ Ico p groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2)*
        f (supportCut (dyadicGroupSupport u amp groups T) j)/(d:ℝ) := by
  let G := dyadicGroupSupport u amp groups T
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  have heq : (∑ i : Fin n,(postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d)^2*f i.val) =
      ∑ i : Fin n,(postprefixCoefficients u amp groups T p i/Real.sqrt d)^2*f (e i).val := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun i : Fin n =>
        (postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d)^2*f i.val)).symm
  have hdis : Set.PairwiseDisjoint (↑(Ico p groups.length) : Set ℕ) G := by
    intro j hj k hk hjk
    exact real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl
      (mem_range.mpr (mem_Ico.mp hj).2) (mem_range.mpr (mem_Ico.mp hk).2) hjk
  change (∑ i : Fin n,(postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d)^2*f i.val)=_
  rw [heq]
  simp only [postprefixCoefficients]
  simp_rw [ite_div,zero_div,ite_pow,zero_pow (by decide : 2≠0),ite_mul,zero_mul]
  rw [Finset.sum_ite_mem_eq,postprefixSupport_eq_biUnion]
  rw [Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := mem_Ico.mp hj
  calc
    _ = ∑ i ∈ G j,(u i)^2*f (supportCut G j)/(d:ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := (real_actualDyadicSupportPermutation_group ratio u amp ha groups T hreg hflat
        j hj'.2 i).mp hi
      have hw := hf j hj'.1 hj'.2 (e i).val he.1 he.2
      rw [hw,div_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
      ring
    _ = _ := by rw [← Finset.sum_div,← Finset.sum_mul]

/-- The exact rowwise compensator equals the paper's groupwise random variance.
Both sides use the same completed canonical partial-polar witnesses; coefficients
are the actual postprefix coefficients, normalized by sqrt(d), in actual support order. -/
theorem real_exactPrefixVariance_eq_group_sum {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (w : Fin n → ℝ)
    (Y : Fin n → Euclid q × Euclid r) :
    exactPrefixVariance w
      (fun i => postprefixCoefficients u amp groups T p
        ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)/Real.sqrt d)
      (capturedBlockLo (dyadicGroupSupport u amp groups T) p b)
      (capturedBlockHi (dyadicGroupSupport u amp groups T) p b) Y =
    ∑ j ∈ Ico p groups.length,
      (∑ i ∈ dyadicGroupSupport u amp groups T j,(u i)^2)*
        ‖operatorFrobenius (exactCompletedPrefix w
          (capturedBlockLo (dyadicGroupSupport u amp groups T) p b)
          (capturedBlockHi (dyadicGroupSupport u amp groups T) p b) Y
          (supportCut (dyadicGroupSupport u amp groups T) j))‖^2/(d:ℝ) := by
  unfold exactPrefixVariance
  apply real_postprefix_weighted_group_sum ratio u amp ha groups T d p hreg hflat
    (fun t => ‖operatorFrobenius (exactCompletedPrefix w
      (capturedBlockLo (dyadicGroupSupport u amp groups T) p b)
      (capturedBlockHi (dyadicGroupSupport u amp groups T) p b) Y t)‖^2)
  intro j hpj hj t hlo hhi
  rw [exactCapturedPrefix_constant_on_group _ p b j t hpj hlo hhi w Y]

/-- The same constancy gives the exact group cross sum: each summand pairs
Z_<j with the synthesis of the actual normalized retained group on original rows. -/
theorem real_exactPrefixCross_eq_group_sum {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (w : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) :
    let G := dyadicGroupSupport u amp groups T
    let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
    let Y := permuteRows e X
    exactPrefixCross w
      (fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d)
      (capturedBlockLo G p b) (capturedBlockHi G p b) Y =
    ∑ j ∈ Ico p groups.length,
      ⟪operatorFrobenius (exactCompletedPrefix w (capturedBlockLo G p b)
          (capturedBlockHi G p b) Y (supportCut G j)),
        operatorFrobenius (bilinearSynthesis (fun i => if i∈G j then u i/Real.sqrt d else 0) X)⟫_ℝ := by
  let G := dyadicGroupSupport u amp groups T
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  let Y := permuteRows e X
  let Z := fun t => exactCompletedPrefix w (capturedBlockLo G p b) (capturedBlockHi G p b) Y t
  have heq : (∑ i : Fin n,postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d*
      ⟪Z i.val (Y i).1,(Y i).2⟫_ℝ) =
      ∑ i : Fin n,postprefixCoefficients u amp groups T p i/Real.sqrt d*
        ⟪Z (e i).val (Y (e i)).1,(Y (e i)).2⟫_ℝ := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun i : Fin n => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d*
        ⟪Z i.val (Y i).1,(Y i).2⟫_ℝ)).symm
  have hdis : Set.PairwiseDisjoint (↑(Ico p groups.length) : Set ℕ) G := by
    intro j hj k hk hjk
    exact real_actual_group_supports_pairwise ratio u amp ha groups T hreg hflat groups.length le_rfl
      (mem_range.mpr (mem_Ico.mp hj).2) (mem_range.mpr (mem_Ico.mp hk).2) hjk
  change (∑ i : Fin n,postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d*
    ⟪Z i.val (Y i).1,(Y i).2⟫_ℝ)=_
  rw [heq]
  simp only [postprefixCoefficients]
  simp_rw [ite_div,zero_div,ite_mul,zero_mul]
  rw [Finset.sum_ite_mem_eq,postprefixSupport_eq_biUnion,Finset.sum_biUnion hdis]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := mem_Ico.mp hj
  calc
    _ = ∑ i ∈ G j,(u i/Real.sqrt d)*⟪Z (supportCut G j) (X i).1,(X i).2⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i hi
      have he := (real_actualDyadicSupportPermutation_group ratio u amp ha groups T hreg hflat
        j hj'.2 i).mp hi
      have hz : Z (e i).val=Z (supportCut G j) :=
        exactCapturedPrefix_constant_on_group G p b j (e i).val hj'.1 he.1 he.2 w Y
      rw [hz]
      simp only [Y,permuteRows,Equiv.symm_apply_apply]
    _ = _ := by
      symm
      rw [real_inner_comm,inner_bilinearSynthesis]
      simp only [ite_mul,zero_mul]
      rw [Finset.sum_ite_mem_eq]

/-- The literal actual random compensator paired with realActualExactCapturedCross. -/
def realActualExactCapturedVariance {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid q × Euclid r) : ℝ :=
  exactPrefixVariance (real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat)
    (fun i => postprefixCoefficients u amp groups T p
      ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)/Real.sqrt d)
    (capturedBlockLo (dyadicGroupSupport u amp groups T) p b)
    (capturedBlockHi (dyadicGroupSupport u amp groups T) p b)
    (permuteRows (real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat) X)

/-- Source v_k display and exact row-to-group bridge on the original row sample.
The two cutoffs p,b remain literal, and every postprefix group is included. -/
theorem real_actual_exact_variance_eq_group_sum {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid q × Euclid r) :
    let G := dyadicGroupSupport u amp groups T
    let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
    let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
    let Y := permuteRows e X
    realActualExactCapturedVariance ratio u amp ha groups T d p b hreg hflat X =
      ∑ j ∈ Ico p groups.length,(∑ i ∈ G j,(u i)^2)*
        ‖operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
          (capturedBlockHi G p b) Y (supportCut G j))‖^2/(d:ℝ) := by
  exact real_exactPrefixVariance_eq_group_sum ratio u amp ha groups T d p b hreg hflat _ _

/-- Direct deterministic bound for the actual row compensator with the source's
rank-sensitive group constant, all real record ratios >1 and no assumed variance envelope. -/
theorem real_exactPrefixVariance_le {n r q : ℕ}
    (ratio : ℝ) (hratio : 1<ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (hd : 0<(d:ℝ)) (w : Fin n → ℝ) (Y : Fin n → Euclid q × Euclid r) :
    exactPrefixVariance w
      (fun i => postprefixCoefficients u amp groups T p
        ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)/Real.sqrt d)
      (capturedBlockLo (dyadicGroupSupport u amp groups T) p b)
      (capturedBlockHi (dyadicGroupSupport u amp groups T) p b) Y ≤
      (16*T*ratio^2/(3*(ratio-1)*d))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  rw [real_exactPrefixVariance_eq_group_sum ratio u amp ha groups T d p b hreg hflat w Y]
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg
    (show Ico p groups.length ⊆ range groups.length from fun j hj => mem_range.mpr (mem_Ico.mp hj).2)
    (by intros; positivity))
  exact paper_exact_group_predictable_variance_le ratio hratio u w amp ha groups T hreg hflat hchain
    (capturedBlockLo _ p b) (capturedBlockHi _ p b) (capturedBlock_ordered _ p b)
    (capturedBlock_separated _ p b) Y d hd

theorem real_actual_exact_variance_le {n r q : ℕ}
    (ratio : ℝ) (hratio : 1<ratio) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor ratio
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (hd : 0<(d:ℝ)) (X : Fin n → Euclid q × Euclid r) :
    realActualExactCapturedVariance ratio u amp ha groups T d p b hreg hflat X ≤
      (16*T*ratio^2/(3*(ratio-1)*d))*(coefficientMass (retainedGroupVector u amp groups T))^2 := by
  exact real_exactPrefixVariance_le ratio hratio u amp ha groups T d p b hreg hflat hchain hd _ _

/-- With no postprefix groups the actual variance is exactly zero. -/
theorem real_actual_exact_variance_empty {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid q × Euclid r)
    (hp : groups.length≤p) :
    realActualExactCapturedVariance ratio u amp ha groups T d p b hreg hflat X=0 := by
  rw [real_actual_exact_variance_eq_group_sum]
  simp [Finset.Ico_eq_empty_of_le hp]

/-- Zero coefficients produce zero variance, without dividing by mass or radius. -/
theorem real_actual_exact_variance_zero {n r q : ℕ}
    (ratio amp : ℝ) (ha : 0≤amp) (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio (0 : Fin n → ℝ) amp T g)
    (hflat : groups.flatten.Nodup) (X : Fin n → Euclid q × Euclid r) :
    realActualExactCapturedVariance ratio 0 amp ha groups T d p b hreg hflat X=0 := by
  simp [realActualExactCapturedVariance,exactPrefixVariance,postprefixCoefficients]

/-- The paper's literal groupwise compensated expectation on the original iid
Gaussian sample law. Both the exact captured cross and its exact group compensator
use the same normalized actual coefficients, ordered rows, and full captured cutoff. -/
theorem real_actual_group_compensator {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (B : ℝ) (hB : 0<B)
    (hcoef : ∀ i : Fin n,|postprefixCoefficients u amp groups T p
      ((real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat).symm i)/Real.sqrt d|≤B)
    (lam : ℝ) (hlam : 0≤lam) (hlamB : lam≤1/(Real.sqrt 2*B)) :
    let G := dyadicGroupSupport u amp groups T
    let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
    let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
    let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
    let Xg := fun X : Fin n → Euclid q × Euclid r =>
      ∑ j ∈ Ico p groups.length,
        ⟪operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
            (capturedBlockHi G p b) (permuteRows e X) (supportCut G j)),
          operatorFrobenius (bilinearSynthesis (fun i => if i∈G j then u i/Real.sqrt d else 0) X)⟫_ℝ
    let Vg := fun X : Fin n → Euclid q × Euclid r =>
      ∑ j ∈ Ico p groups.length,(∑ i ∈ G j,(u i)^2)*
        ‖operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
          (capturedBlockHi G p b) (permuteRows e X) (supportCut G j))‖^2/(d:ℝ)
    Integrable (fun X : Fin n → Euclid q × Euclid r =>
      Real.exp (-lam*Xg X-lam^2*Vg X))
        (gaussianBilinearSampleLaw (Fin n) q r) ∧
    (∫ X : Fin n → Euclid q × Euclid r,
      Real.exp (-lam*Xg X-lam^2*Vg X)
        ∂gaussianBilinearSampleLaw (Fin n) q r)≤1 := by
  let G := dyadicGroupSupport u amp groups T
  let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
  let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
  let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
  let Xg := fun X : Fin n → Euclid q × Euclid r =>
    ∑ j ∈ Ico p groups.length,
      ⟪operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
          (capturedBlockHi G p b) (permuteRows e X) (supportCut G j)),
        operatorFrobenius (bilinearSynthesis (fun i => if i∈G j then u i/Real.sqrt d else 0) X)⟫_ℝ
  let Vg := fun X : Fin n → Euclid q × Euclid r =>
    ∑ j ∈ Ico p groups.length,(∑ i ∈ G j,(u i)^2)*
      ‖operatorFrobenius (exactCompletedPrefix U (capturedBlockLo G p b)
        (capturedBlockHi G p b) (permuteRows e X) (supportCut G j))‖^2/(d:ℝ)
  have hh := paper_captured_exact_compensator_permuted (r:=r) (q:=q) e G p b U v
    B hB hcoef lam hlam hlamB
  have hv (X : Fin n → Euclid q × Euclid r) :
      capturedExactVariance G p b U v (permuteRows e X)=Vg X :=
    real_exactPrefixVariance_eq_group_sum ratio u amp ha groups T d p b hreg hflat U (permuteRows e X)
  have hx (X : Fin n → Euclid q × Euclid r) :
      capturedExactCross G p b U v (permuteRows e X)=Xg X :=
    real_exactPrefixCross_eq_group_sum ratio u amp ha groups T d p b hreg hflat U X
  have hf : (fun X : Fin n → Euclid q × Euclid r =>
      Real.exp (-lam*capturedExactCross G p b U v (permuteRows e X)-
        lam^2*capturedExactVariance G p b U v (permuteRows e X))) =
      (fun X => Real.exp (-lam*Xg X-lam^2*Vg X)) := by
    funext X
    rw [hv,hx]
  rw [hf] at hh
  exact hh

/-- Empty future groups give expectation exactly one for every lambda; no
positive-radius premise or division by B is required in this case. -/
theorem real_actual_group_compensator_empty {n r q : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T d p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u amp T g)
    (hflat : groups.flatten.Nodup) (hp : groups.length≤p) (lam : ℝ) :
    let G := dyadicGroupSupport u amp groups T
    let e := real_actualDyadicSupportPermutation ratio u amp ha groups T hreg hflat
    let U := real_orderedRetainedCoefficients ratio u amp ha groups T d hreg hflat
    let v := fun i => postprefixCoefficients u amp groups T p (e.symm i)/Real.sqrt d
    (∫ X : Fin n → Euclid q × Euclid r,
      Real.exp (-lam*capturedExactCross G p b U v (permuteRows e X)-
        lam^2*realActualExactCapturedVariance ratio u amp ha groups T d p b hreg hflat X)
        ∂gaussianBilinearSampleLaw (Fin n) q r)=1 := by
  simp [capturedExactCross,exactPrefixCross,realActualExactCapturedVariance,exactPrefixVariance,
    postprefixCoefficients,postprefixSupport,Finset.Ico_eq_empty_of_le hp]

#print axioms real_postprefix_weighted_group_sum
#print axioms real_exactPrefixVariance_eq_group_sum
#print axioms real_exactPrefixCross_eq_group_sum
#print axioms realActualExactCapturedVariance
#print axioms real_actual_exact_variance_eq_group_sum
#print axioms real_exactPrefixVariance_le
#print axioms real_actual_exact_variance_le
#print axioms real_actual_exact_variance_empty
#print axioms real_actual_exact_variance_zero
#print axioms real_actual_group_compensator
#print axioms real_actual_group_compensator_empty
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoid.PaperCanonicalPolar.captured_endpoint_le_iff_at_group_start
#print axioms GaussianEllipsoid.PaperCanonicalPolar.exactCapturedPrefix_constant_on_group
