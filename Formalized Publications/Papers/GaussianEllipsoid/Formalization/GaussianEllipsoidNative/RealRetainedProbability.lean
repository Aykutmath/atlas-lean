import PaperAtomEvent
import RealRetainedCore
import PaperActualRhoConditional
import PaperGeneralQLateProbability
import PaperRetainedPositive
import PaperFixedVectorLogPrefactor
import PaperOriginalLogDepth


noncomputable section
set_option maxHeartbeats 1200000
open Finset MeasureTheory GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoid
open GaussianEllipsoid.ProjectedClusters
open scoped BigOperators
namespace GaussianEllipsoidCandidate

def realOrderedGroupFailure {n d : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (groups : List (List ℕ)) (T r : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u ‖u‖ T g) (hflat : groups.flatten.Nodup) :
    Set (Fin n → Euclid (d/2) × Euclid (d/2)) :=
  {X | spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock
    (real_orderedRetainedCoefficients ratio u ‖u‖ (norm_nonneg u) groups T d hreg hflat)
    (permuteRows (real_actualDyadicSupportPermutation ratio u ‖u‖ (norm_nonneg u) groups T hreg hflat) X)
    (supportCut (dyadicGroupSupport u ‖u‖ groups T) r)
    (supportCut (dyadicGroupSupport u ‖u‖ groups T) (r+1)))) <
      generalProj (1/4) (8*ratio)*Real.sqrt d*dyadicGroupMass u ‖u‖ groups T r}

theorem realOrderedGroupFailure_measurable {n d : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (groups : List (List ℕ)) (T r : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u ‖u‖ T g) (hflat : groups.flatten.Nodup) :
    MeasurableSet (realOrderedGroupFailure (d:=d) ratio u groups T r hreg hflat) :=
  (measurableSet_lt (measurable_nuclear_projectedPrefixBlock _ _ _) measurable_const).preimage
    (permuteRows_preserving _ (d/2) (d/2)).measurable

/-- The full-array conditional failure event is precisely the ordered canonical
projected-block event, not just an inequality between their probabilities. -/
theorem realOrderedGroupFailure_preimage {n d : ℕ}
    (ratio : ℝ) (u : Fin n → ℝ) (groups : List (List ℕ)) (T r : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u ‖u‖ T g) (hflat : groups.flatten.Nodup)
    (hr : r < groups.length) :
    tensorToCanonicalRows n (d/2) ⁻¹' realOrderedGroupFailure (d:=d) ratio u groups T r hreg hflat =
      actualRhoGroupFailure ratio u groups T d r := by
  ext z
  have he := real_projected_ordered_tensor_identity ratio u ‖u‖ (norm_nonneg u) groups T d r hreg hflat hr
    (rhoSupportEmbedding (rhoHeadSupport u groups T r))
    (rhoSupportEmbedding_range (rhoHeadSupport u groups T r)) z
  change spectralNuclearNorm _ < _ ↔ spectralNuclearNorm _ < _
  rw [he]
  rfl

theorem real_ordered_group_failure_probability {n d : ℕ}
    (ratio rho : ℝ) (hratio : 1 < ratio) (hrho : 0 < rho)
    (hrcap : rho < min (1/8) (generalUp (1/4) (8*ratio)/(32*ratio^2))) (hd : 8 ≤ d)
    (u : Fin n → ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u ‖u‖ T g) (hflat : groups.flatten.Nodup)
    (b : ℕ) (hb : SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b)
    (r : ℕ) (hrb : r < b)
    (hlow : generalLow (8*ratio)*Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r) :
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      (realOrderedGroupFailure (d:=d) ratio u groups T r hreg hflat) ≤
      Real.exp (-generalProj (1/4) (8*ratio)*(d:ℝ)*dyadicGroupEffectiveSupport u ‖u‖ groups T r) := by
  rw [← (tensorToCanonicalRows_preserving n (d/2)).measureReal_preimage
    (realOrderedGroupFailure_measurable (d:=d) ratio u groups T r hreg hflat).nullMeasurableSet,
    realOrderedGroupFailure_preimage (d:=d) ratio u groups T r hreg hflat (hrb.trans_le hb.1)]
  exact actual_rho_group_probability ratio rho hratio hrho hrcap hd u groups T hreg hflat b hb r hrb hlow

theorem real_captured_projection_union_probability {n d : ℕ}
    (ratio rho : ℝ) (hratio : 1 < ratio) (hrho : 0 < rho)
    (hrcap : rho < min (1/8) (generalUp (1/4) (8*ratio)/(32*ratio^2))) (hd : 8 ≤ d)
    (u : Fin n → ℝ) (groups : List (List ℕ)) (T p b : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup ratio u ‖u‖ T g) (hflat : groups.flatten.Nodup)
    (hb : SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b)
    (cR : ℝ) (hcR : 0 < cR) (hlog : 0 < Real.log (d:ℝ))
    (hlow : ∀ r,p ≤ r → r < b → generalLow (8*ratio)*Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r)
    (hR : ∀ r,p ≤ r → r < b → cR*(d:ℝ)/Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r) :
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      (real_actualCapturedProjectionBad ratio u ‖u‖ (norm_nonneg u) groups T d p b hreg hflat
        (generalProj (1/4) (8*ratio))) ≤
      (groups.length:ℝ)*Real.exp (-(generalProj (1/4) (8*ratio)*cR)*(d:ℝ)^2/Real.log (d:ℝ)) := by
  have hratio0 : 0 < ratio := by linarith
  have hc : 0 < generalProj (1/4) (8*ratio) :=
    (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*ratio)).2.2
  let E := fun r => realOrderedGroupFailure (d:=d) ratio u groups T r hreg hflat
  have hprob : ∀ r∈Ico p b,(gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real (E r) ≤
      Real.exp (-(generalProj (1/4) (8*ratio)*cR)*(d:ℝ)^2/Real.log (d:ℝ)) := by
    intro r hr
    have hp := real_ordered_group_failure_probability ratio rho hratio hrho hrcap hd u groups T hreg hflat b hb
      r (mem_Ico.mp hr).2 (hlow r (mem_Ico.mp hr).1 (mem_Ico.mp hr).2)
    apply hp.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hR r (mem_Ico.mp hr).1 (mem_Ico.mp hr).2)
      (show 0 ≤ generalProj (1/4) (8*ratio)*(d:ℝ) by positivity)
    calc
      _ = -(generalProj (1/4) (8*ratio)*(d:ℝ)*dyadicGroupEffectiveSupport u ‖u‖ groups T r) := by ring
      _ ≤ -(generalProj (1/4) (8*ratio)*(d:ℝ)*(cR*(d:ℝ)/Real.log (d:ℝ))) := neg_le_neg hh
      _ = _ := by ring
  have he : real_actualCapturedProjectionBad ratio u ‖u‖ (norm_nonneg u) groups T d p b hreg hflat
      (generalProj (1/4) (8*ratio)) = ⋃ r∈Ico p b,E r := by ext X; simp [real_actualCapturedProjectionBad,E,realOrderedGroupFailure]
  rw [he]
  calc
    _ ≤ ∑ r∈Ico p b,(gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real (E r) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r∈Ico p b,Real.exp (-(generalProj (1/4) (8*ratio)*cR)*(d:ℝ)^2/Real.log (d:ℝ)) := sum_le_sum hprob
    _ = ((b-p:ℕ):ℝ)*Real.exp (-(generalProj (1/4) (8*ratio)*cR)*(d:ℝ)^2/Real.log (d:ℝ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast ((Nat.sub_le b p).trans hb.1)) (Real.exp_nonneg _)

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.realOrderedGroupFailure_preimage
#print axioms GaussianEllipsoidCandidate.real_captured_projection_union_probability

namespace GaussianEllipsoidCandidate
open GaussianEllipsoid.SparseSupport

def realPostprefixScale (q : ℝ) (T : ℕ) : ℝ := 16384*T*q^2/(q-1)
def realEffectiveScale (q : ℝ) (T : ℕ) : ℝ := 3*(q-1)/(262144*T*q^3)
def realDiagonalConstant (q : ℝ) : ℝ := min (1/4194304) (generalProj (1/4) (8*q))/4
def realLateRateAt (q rho : ℝ) (T : ℕ) : ℝ :=
  (1/1048576)*min (rho*(q-1)/((T:ℝ)*q^2)) 1

def realRetainedRateAt (q rho : ℝ) (T : ℕ) : ℝ :=
  min (realCrossRate q T (realPostprefixScale q T) (realDiagonalConstant q))
    (min (generalProj (1/4) (8*q)*realEffectiveScale q T) (realLateRateAt q rho T))

theorem realRetainedRateAt_pos (q : ℝ) (hq : 1 < q) (rho : ℝ) (hrho : 0 < rho) (T : ℕ) (hT : 0 < T) :
    0 < realRetainedRateAt q rho T := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q-1 := by linarith
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hp := (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*q)).2.2
  have hr : 0 < rho := hrho
  have hL : 0 < realPostprefixScale q T := by unfold realPostprefixScale; positivity
  have ha : 0 < realDiagonalConstant q := by unfold realDiagonalConstant; positivity
  have hcross := realCrossRate_pos q hq T hT _ _ hL ha
  unfold realRetainedRateAt realEffectiveScale realLateRateAt
  positivity

/-- Both source alternatives for arbitrary q,T, with literal retained vector,
full-half sparse event and no atom event. All constants are fixed before u. -/
theorem real_retained_fixed_alternatives {n d : ℕ}
    (q : ℝ) (hq : 1 < q) (rho : ℝ) (hρ : 0 < rho)
    (hρcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    (T : ℕ) (hT : 0 < T) (K : ℝ)
    (hd : 8 ≤ d) (hlog : 1 ≤ Real.log (d:ℝ))
    (hlate : 64 ≤ min (rho*(q-1)/((T:ℝ)*q^2)) 1*(d:ℝ))
    (u : Fin n → ℝ) (hu : u ≠ 0) (groups : List (List ℕ)) (p b : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u ‖u‖ T g) (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u ‖u‖ t).card:ℝ)))
    (hsupp : ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d)
    (hpb : p ≤ b)
    (hb : SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b)
    (hsp : supportCut (dyadicGroupSupport u ‖u‖ groups T) p ≤ sparseSupportSize d)
    (hS : ∀ r,p ≤ r → r < groups.length →
      (d:ℝ)/(realPostprefixScale q T*Real.log (d:ℝ)) ≤ dyadicGroupScale u ‖u‖ groups r)
    (hR : ∀ r,p ≤ r → r < b →
      realEffectiveScale q T*(d:ℝ)/Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r)
    (hlow : ∀ r,p ≤ r → r < b →
      generalLow (8*q)*Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r)
    (hM : 0 < coefficientMass (retainedGroupVector u ‖u‖ groups T)) :
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
        realRetainedConstantAt q rho T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T)} ∩
        paperSparseSingularGood d n (d/2)) ≤
      (groups.length+1:ℝ)*Real.exp (-realRetainedRateAt q rho T*(d:ℝ)^2/Real.log (d:ℝ)) := by
  let M := coefficientMass (retainedGroupVector u ‖u‖ groups T)
  let E := Real.exp (-realRetainedRateAt q rho T*(d:ℝ)^2/Real.log (d:ℝ))
  have hd0 : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog0 : 0 < Real.log (d:ℝ) := by linarith
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q-1 := by linarith
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hrho : 0 < rho ∧ rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)) := ⟨hρ,hρcap⟩
  have hp := (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*q)).2.2
  have hL : 0 < realPostprefixScale q T := by unfold realPostprefixScale; positivity
  have hcR : 0 < realEffectiveScale q T := by unfold realEffectiveScale; positivity
  have ha : 0 < realDiagonalConstant q := by unfold realDiagonalConstant; positivity
  have hrate := realRetainedRateAt_pos q hq rho hrho.1 T hT
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hcommon (c : ℝ) (hc : realRetainedRateAt q rho T ≤ c) :
      Real.exp (-c*(d:ℝ)^2/Real.log (d:ℝ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ (d:ℝ)^2/Real.log (d:ℝ) by positivity)
    calc
      _ = -(c*((d:ℝ)^2/Real.log (d:ℝ))) := by ring
      _ ≤ -(realRetainedRateAt q rho T*((d:ℝ)^2/Real.log (d:ℝ))) := neg_le_neg hh
      _ = _ := by ring
  by_cases hcapt : M/2 ≤ ∑ r∈range b,dyadicGroupMass u ‖u‖ groups T r
  · have hsub : ({X : Fin n → Euclid (d/2) × Euclid (d/2) |
        scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
          realRetainedConstantAt q rho T K*Real.sqrt d*M} ∩ paperSparseSingularGood d n (d/2)) ⊆
      real_actualCapturedProjectionBad q u ‖u‖ (norm_nonneg u) groups T d p b hreg hflat (generalProj (1/4) (8*q)) ∪
      {X | realActualExactCapturedCross q u ‖u‖ (norm_nonneg u) groups T d p b hreg hflat X ≤
        -(realDiagonalConstant q*M*Real.sqrt d)} := by
      rintro X ⟨hbad,hspX⟩
      by_cases hproj : X∈real_actualCapturedProjectionBad q u ‖u‖ (norm_nonneg u) groups T d p b hreg hflat (generalProj (1/4) (8*q))
      · exact Or.inl hproj
      · right
        by_contra hcross
        have hl := real_actual_captured_retained_lower q u ‖u‖ (norm_nonneg u) groups T p b hreg hflat hpb hb.1 hsp
          (generalProj (1/4) (8*q)) hp.le hcapt X hspX hproj (le_of_not_ge hcross)
        have hth := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (realRetainedConstantAt_le_captured q hq rho hρ ((lt_min_iff.mp hρcap).1) T hT K) (Real.sqrt_nonneg (d:ℝ))) hM.le
        exact (not_lt_of_ge hl) (hbad.trans_le hth)
    have hproj := real_captured_projection_union_probability q (rho) hq hrho.1 hrho.2 hd u groups T p b hreg hflat hb
      (realEffectiveScale q T) hcR hlog0 hlow hR
    have hc := real_actual_captured_cross_common_tail (h:=d/2) q hq u ‖u‖ (norm_nonneg u) groups T p b hT hreg hflat hchain
      (realPostprefixScale q T) (realDiagonalConstant q) hL ha hd0 hlog hS hM
    have hpE := hcommon (generalProj (1/4) (8*q)*realEffectiveScale q T)
      ((min_le_right _ _).trans (min_le_left _ _))
    have hcE := hcommon (realCrossRate q T (realPostprefixScale q T) (realDiagonalConstant q)) (min_le_left _ _)
    calc
      _ ≤ _ := measureReal_mono (μ:=gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)) hsub
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ (groups.length:ℝ)*Real.exp (-(generalProj (1/4) (8*q)*realEffectiveScale q T)*(d:ℝ)^2/Real.log (d:ℝ))+
          Real.exp (-realCrossRate q T (realPostprefixScale q T) (realDiagonalConstant q)*(d:ℝ)^2/Real.log (d:ℝ)) :=
        add_le_add hproj hc
      _ ≤ (groups.length:ℝ)*E+E := add_le_add (mul_le_mul_of_nonneg_left hpE (Nat.cast_nonneg _)) hcE
      _ = _ := by dsimp [E]; push_cast; ring
  · have hlatebranch := lt_of_not_ge hcapt
    have hcount := real_late_logarithmic_budget q hq u ‖u‖ (norm_pos_iff.mpr hu) groups T hT hreg hchain hflat
      (rho) K d hrho.1 hd0 hsupp b hb hlatebranch
    have hl := real_retained_late_smallball q hq u ‖u‖ (norm_pos_iff.mpr hu) groups T hT hreg hchain hflat
      (rho) K (realLateBudgetAt q rho T K) hrho.1 (by simpa [realLateBudgetAt] using hcount.1)
      hlate hsupp b hb (by simpa [realLateBudgetAt] using hcount.2) hM hlatebranch
    have hprob : (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        {X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
          (1/1048576:ℝ)/(8*q*Real.sqrt (max K 1)*realLateBudgetAt q rho T K)*Real.sqrt d*M} ≤
        Real.exp (-realLateRateAt q rho T*(d:ℝ)^2) := by
      rw [show {X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
          (1/1048576:ℝ)/(8*q*Real.sqrt (max K 1)*realLateBudgetAt q rho T K)*Real.sqrt d*M} =
        {X | spectralNuclearNorm (operatorFrobenius ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis
          (retainedGroupVector u ‖u‖ groups T) X)) <
          (1/1048576:ℝ)/(8*q*Real.sqrt (max K 1)*realLateBudgetAt q rho T K)*Real.sqrt d*M} from rfl,
        paper_strict_canonical_probability]
      simpa only [realLateRateAt,M,neg_mul] using hl
    have hsub : ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
        realRetainedConstantAt q rho T K*Real.sqrt d*M} ∩ paperSparseSingularGood d n (d/2)) ⊆
      {X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
        (1/1048576:ℝ)/(8*q*Real.sqrt (max K 1)*realLateBudgetAt q rho T K)*Real.sqrt d*M} := by
      intro X hX
      exact hX.1.trans_le (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (realRetainedConstantAt_le_late q hq rho hρ ((lt_min_iff.mp hρcap).1) T hT K) (Real.sqrt_nonneg _)) hM.le)
    have hr : realRetainedRateAt q rho T ≤ realLateRateAt q rho T := (min_le_right _ _).trans (min_le_right _ _)
    have hlE : Real.exp (-realLateRateAt q rho T*(d:ℝ)^2) ≤ E := by
      apply Real.exp_le_exp.mpr
      have hh := (div_le_self (show 0 ≤ realRetainedRateAt q rho T*(d:ℝ)^2 by positivity) hlog).trans
        (mul_le_mul_of_nonneg_right hr (sq_nonneg (d:ℝ)))
      simpa only [neg_div,neg_mul] using neg_le_neg hh
    calc
      _ ≤ _ := measureReal_mono (μ:=gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)) hsub
      _ ≤ Real.exp (-realLateRateAt q rho T*(d:ℝ)^2) := hprob
      _ ≤ E := hlE
      _ ≤ (groups.length+1:ℝ)*E := by nlinarith [mul_nonneg (Nat.cast_nonneg groups.length) hE]

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.real_retained_fixed_alternatives

namespace GaussianEllipsoidCandidate
open GaussianEllipsoid.SparseSupport Filter

/-- Fully specified actual retained construction, including the greedy record
certificate, finite bin cover, exact amplitude and positive retained mass. -/
def RealRetainedCertificate {n : ℕ} (q : ℝ) (T : ℕ) (u : Fin n → ℝ)
    (N : ℕ) (groups : List (List ℕ)) : Prop :=
  0 < N ∧
  (∀ i,u i ≠ 0 ↔ ∃ t∈range N,i∈dyadicBin u ‖u‖ t) ∧
  (∀ t,N ≤ t → dyadicBin u ‖u‖ t=∅) ∧
  groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
  GaussianEllipsoid.PaperRealRecord.RecordGrouping q
    (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups ∧
  (∀ g∈groups,RealRegularRetainedGroup q u ‖u‖ T g) ∧
  groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
    fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) ∧
  0 < coefficientMass (retainedGroupVector u ‖u‖ groups T) ∧
  coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤ 4*q*(1/2:ℝ)^T*coefficientMass u

/-- Literal arbitrary-q, arbitrary-positive-T retained-vector source probability.
The admissible rho is fixed before T,K; the retained numerator depends only on q.
The rate and starting dimension are chosen before n,u and the random sample;
n has no ambient bound. -/
theorem paper_general_q_rho_retained_probability (q : ℝ) (hq : 1 < q)
    (rho : ℝ) (hρ : 0 < rho)
    (hρcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    (T : ℕ) (hT : 0 < T) (K : ℝ) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      ∃ N : ℕ,∃ groups : List (List ℕ),RealRetainedCertificate q T u N groups ∧
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
          realRetainedConstantAt q rho T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T)} ∩
          paperSparseSingularGood d n (d/2)) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  have hrho : 0 < rho ∧ rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)) := ⟨hρ,hρcap⟩
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q-1 := by linarith
  have hTr : (0:ℝ) < T := Nat.cast_pos.mpr hT
  have hlow := (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*q)).1
  let R := realRetainedRateAt q rho T
  have hRpos : 0 < R := realRetainedRateAt_pos q hq rho hrho.1 T hT
  let C : ℝ := 1/R
  have hC : 0 < C := by dsimp [C]; positivity
  let c : ℝ := 1/(2*C)
  have hc : 0 < c := by dsimp [c]; positivity
  have hKplus : 0 < max K 1 := lt_of_lt_of_le (by norm_num) (le_max_right K 1)
  obtain ⟨dLate,hdLate⟩ := real_late_dimension_threshold q rho T hq hrho.1 hT
  have hlogone : ∀ᶠ d : ℕ in atTop,1 ≤ Real.log (d:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  have hlarge : ∀ᶠ d : ℕ in atTop,48*C^3*(max K 1+1) ≤ (d:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hevent := (eventually_paper_rho_numerics q rho (generalLow (8*q)) hq hrho.1 hlow T hT).and
    (hlogone.and (hlarge.and (eventually_ge_atTop dLate)))
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp hevent
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n u hu hsupp
  obtain ⟨hnum,hlog,hlargeD,hLateD⟩ := hd₀ d hd
  obtain ⟨hd8,hlog0,hfloor,hbudget,hRnum⟩ := hnum
  have hdpos : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz,coefficientMass] at hu
  obtain ⟨N,groups,hN,hzero,hcover,hempty,hflat0,hreg,hchain,herror,hgreedy⟩ :=
    real_paper_dyadic_decomposition q hq u T hT
  have hflat := actual_constructor_flatten_nodup u ‖u‖ groups N hflat0
  have hM := real_retained_mass_pos q u ‖u‖ (norm_nonneg u) N groups T hu0 hcover hflat0 hflat hreg
  obtain ⟨p,b,hpb,hp,hb,hpost,hcapt,hlateS⟩ :=
    paper_real_rho_cutoffs q hq u ‖u‖ groups T hT hreg hchain rho (generalUp (1/4) (8*q)) d
      hrho.1 (lt_min_iff.mp hrho.2).2 hdpos hlog0 hfloor hbudget
  have hsp : supportCut (dyadicGroupSupport u ‖u‖ groups T) p ≤ sparseSupportSize d := by
    have hh : (supportCut (dyadicGroupSupport u ‖u‖ groups T) p:ℝ) ≤ (sparseSupportSize d:ℝ) := by
      rw [actual_dyadic_supportCut_cast]
      exact hp.2.1
    exact_mod_cast hh
  have hscale := real_actual_sparse_postprefix_scale q hq u ‖u‖ groups T p hT hreg hchain d hdpos hlog0 hfloor hp
  have hReff : ∀ r,p ≤ r → r < b →
      realEffectiveScale q T*(d:ℝ)/Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r := by
    intro r hpr hrb
    convert (hpost r hpr (hrb.trans_le hb.1)).2 using 1 <;> dsimp [realEffectiveScale] <;> ring
  have hlow' : ∀ r,p ≤ r → r < b →
      generalLow (8*q)*Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r := by
    intro r hpr hrb
    exact hRnum.trans (hpost r hpr (hrb.trans_le hb.1)).2
  have hprob := real_retained_fixed_alternatives q hq rho hρ hρcap T hT K hd8 hlog (hdLate d hLateD) u hu0 groups p b
    hreg hflat hchain hsupp hpb hb hsp hscale hReff hlow' hM
  have hcount : (groups.length:ℝ) ≤ max K 1*(d:ℝ)^2 := by
    have hc' : (groups.length:ℝ) ≤ ((univ.filter fun i => u i ≠ 0).card:ℝ) :=
      Nat.cast_le.mpr (real_actual_group_count_le_support q u ‖u‖ (norm_nonneg u) groups T hreg hflat)
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hs := hc'.trans (hsupp.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) hdpos.le))
    exact hs.trans (mul_le_mul_of_nonneg_left (by nlinarith) hKplus.le)
  have hpref := paper_logarithmic_prefactor hKplus.le hC
    (show (1:ℝ) ≤ d by exact_mod_cast (show 1 ≤ d by omega)) hlog hcount hlargeD
  have heq : -(d:ℝ)^2/(C*Real.log (d:ℝ)) = -R*(d:ℝ)^2/Real.log (d:ℝ) := by
    dsimp [C]
    field_simp [hRpos.ne',hlog0.ne'] <;> ring
  rw [heq] at hpref
  refine ⟨N,groups,⟨hN,hcover,hempty,hflat0,hgreedy,hreg,hchain,hM,herror⟩,?_⟩
  have hh := hprob.trans hpref
  apply hh.trans_eq
  congr 2
  dsimp [c]
  ring

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_general_q_rho_retained_probability

namespace GaussianEllipsoidCandidate
open GaussianEllipsoid.SparseSupport PaperLogarithmicDepth

/-- The arbitrary-q retained display on the actual original Gaussian samples,
with the literal first/last floor halves and the same sparse event. -/
theorem paper_original_general_q_rho_retained_probability (q : ℝ) (hq : 1 < q)
    (rho : ℝ) (hρ : 0 < rho)
    (hρcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    (T : ℕ) (hT : 0 < T) (K : ℝ) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      ∃ N : ℕ,∃ groups : List (List ℕ),RealRetainedCertificate q T u N groups ∧
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
        {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ))
            (retainedGroupVector u ‖u‖ groups T))) <
          realRetainedConstantAt q rho T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T) ∧
          paperOriginalRows d n X∈paperSparseSingularGood d n (d/2)} ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  obtain ⟨c,hc,d₀,hd₀⟩ := paper_general_q_rho_retained_probability q hq rho hρ hρcap T hT K
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n u hu hsupp
  obtain ⟨N,groups,hcert,hprob⟩ := hd₀ d hd n u hu hsupp
  refine ⟨N,groups,hcert,?_⟩
  rw [paper_original_retained_event_probability]
  exact hprob

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_original_general_q_rho_retained_probability

namespace GaussianEllipsoidCandidate
/-- The individual-norm atom-event corollary of the truncation-loss display.
It remains valid when epsilon_T exceeds one. The literal product-event version
is exported separately below. -/
theorem paper_general_q_rho_truncation_lower {n d h : ℕ}
    (q : ℝ) (hq : 1 < q) (rho : ℝ) (hρ : 0 < rho)
    (hρcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    (T : ℕ) (hT : 0 < T) (K : ℝ)
    (u : Fin n → ℝ) (hu : coefficientMass u=1) (groups : List (List ℕ))
    (herr : coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
      4*q*(1/2:ℝ)^T*coefficientMass u)
    (X : Fin n → Euclid h × Euclid h) (hatom : X∈atomRowsGood d n h)
    (hret : realRetainedConstantAt q rho T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T) ≤
      scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X) :
    (realRetainedConstantAt q rho T K*(1-4*q*(1/2:ℝ)^T)-4*q*(1/2:ℝ)^T)*Real.sqrt d ≤
      scaledBilinearNuclear d u X := by
  let V := retainedGroupVector u ‖u‖ groups T
  let eps : ℝ := 4*q*(1/2:ℝ)^T
  have herr' : coefficientMass (u-V) ≤ eps := by simpa only [hu,mul_one] using herr
  have hM := retained_mass_ge_one_sub u ‖u‖ groups T eps hu herr'
  have hc := (realRetainedConstantAt_pos q hq rho hρ ((lt_min_iff.mp hρcap).1) T hT K).le
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hc) (Real.sqrt_nonneg (d:ℝ))
  have he := (scaledBilinearNuclear_le_mass hatom (u-V)).trans
    (mul_le_mul_of_nonneg_left herr' (Real.sqrt_nonneg (d:ℝ)))
  have ht := scaledBilinearNuclear_sub_le (d:=d) u V X
  change (realRetainedConstantAt q rho T K*(1-eps)-eps)*Real.sqrt d ≤ _
  nlinarith
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_general_q_rho_truncation_lower

namespace GaussianEllipsoidCandidate
open GaussianEllipsoid.SparseSupport PaperLogarithmicDepth

/-- Explicit admissible rho(q) specialization of the free-rho source theorem. -/
theorem paper_general_q_retained_probability (q : ℝ) (hq : 1 < q)
    (T : ℕ) (hT : 0 < T) (K : ℝ) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      ∃ N : ℕ,∃ groups : List (List ℕ),RealRetainedCertificate q T u N groups ∧
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
        ({X | scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X <
          realRetainedConstant q T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T)} ∩
          paperSparseSingularGood d n (d/2)) ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  have hr := realProofRho_admissible q hq
  exact paper_general_q_rho_retained_probability q hq (realProofRho q) hr.1 hr.2 T hT K

/-- Explicit admissible rho(q) specialization of the free-rho source theorem. -/
theorem paper_original_general_q_retained_probability (q : ℝ) (hq : 1 < q)
    (T : ℕ) (hT : 0 < T) (K : ℝ) :
    ∃ c : ℝ,0 < c ∧ ∃ d₀ : ℕ,∀ d : ℕ,d₀ ≤ d → ∀ n : ℕ,∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d →
      ∃ N : ℕ,∃ groups : List (List ℕ),RealRetainedCertificate q T u N groups ∧
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
        {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ))
            (retainedGroupVector u ‖u‖ groups T))) <
          realRetainedConstant q T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T) ∧
          paperOriginalRows d n X∈paperSparseSingularGood d n (d/2)} ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  have hr := realProofRho_admissible q hq
  exact paper_original_general_q_rho_retained_probability q hq (realProofRho q) hr.1 hr.2 T hT K

end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_general_q_retained_probability
#print axioms GaussianEllipsoidCandidate.paper_original_general_q_retained_probability

namespace GaussianEllipsoidCandidate
/-- Source C_A form of the omitted-vector triangle step. The atom-bound
hypothesis is exactly the pointwise property supplied by the atom event. -/
theorem paper_general_q_rho_truncation_lower_CA {n d h : ℕ}
    (q : ℝ) (hq : 1 < q) (rho : ℝ) (hrho : 0 < rho) (hrcap : rho < 1/8)
    (T : ℕ) (hT : 0 < T) (K CA : ℝ) (hCA : 0 ≤ CA)
    (u : Fin n → ℝ) (hu : coefficientMass u=1) (groups : List (List ℕ))
    (herr : coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
      4*q*(1/2:ℝ)^T*coefficientMass u)
    (X : Fin n → Euclid h × Euclid h)
    (hatom : ∀ w : Fin n → ℝ,scaledBilinearNuclear d w X ≤ CA*Real.sqrt d*coefficientMass w)
    (hret : realRetainedConstantAt q rho T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T) ≤
      scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X) :
    (realRetainedConstantAt q rho T K*(1-4*q*(1/2:ℝ)^T)-CA*(4*q*(1/2:ℝ)^T))*Real.sqrt d ≤
      scaledBilinearNuclear d u X := by
  let V := retainedGroupVector u ‖u‖ groups T
  let eps : ℝ := 4*q*(1/2:ℝ)^T
  have herr' : coefficientMass (u-V) ≤ eps := by simpa only [hu,mul_one] using herr
  have hM := retained_mass_ge_one_sub u ‖u‖ groups T eps hu herr'
  have hc := (realRetainedConstantAt_pos q hq rho hrho hrcap T hT K).le
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hc) (Real.sqrt_nonneg (d:ℝ))
  have he := (hatom (u-V)).trans (mul_le_mul_of_nonneg_left herr'
    (show 0 ≤ CA*Real.sqrt d by positivity))
  have ht := scaledBilinearNuclear_sub_le (d:=d) u V X
  change (realRetainedConstantAt q rho T K*(1-eps)-CA*eps)*Real.sqrt d ≤ _
  nlinarith
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_general_q_rho_truncation_lower_CA

namespace GaussianEllipsoidCandidate
/-- Literal source product atom event supplies the C_A residual inequality. -/
theorem paper_general_q_rho_product_atom_truncation {n d h : ℕ}
    (q : ℝ) (hq : 1 < q) (rho : ℝ) (hrho : 0 < rho) (hrcap : rho < 1/8)
    (T : ℕ) (hT : 0 < T) (K CA : ℝ) (hCA : 0 ≤ CA)
    (u : Fin n → ℝ) (hu : coefficientMass u=1) (groups : List (List ℕ))
    (herr : coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
      4*q*(1/2:ℝ)^T*coefficientMass u)
    (X : Fin n → Euclid h × Euclid h) (hatom : X∈GaussianTensorMoments.paperPairAtomEvent CA d n h)
    (hret : realRetainedConstantAt q rho T K*Real.sqrt d*coefficientMass (retainedGroupVector u ‖u‖ groups T) ≤
      scaledBilinearNuclear d (retainedGroupVector u ‖u‖ groups T) X) :
    (realRetainedConstantAt q rho T K*(1-4*q*(1/2:ℝ)^T)-CA*(4*q*(1/2:ℝ)^T))*Real.sqrt d ≤
      scaledBilinearNuclear d u X := by
  apply paper_general_q_rho_truncation_lower_CA q hq rho hrho hrcap T hT K CA hCA u hu groups herr X ?_ hret
  intro w
  exact GaussianTensorMoments.paperPairAtomEvent_all_coefficients hatom w
end GaussianEllipsoidCandidate
#print axioms GaussianEllipsoidCandidate.paper_general_q_rho_product_atom_truncation
