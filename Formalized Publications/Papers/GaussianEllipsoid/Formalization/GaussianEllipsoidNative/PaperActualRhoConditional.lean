import PaperRhoSource
import ActualCapturedCoefficients
import SparsePrefixSynthesis

noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Module Finset Filter
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoidCandidate
open scoped BigOperators ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- Canonical enumeration of the actual selected finite support. -/
def rhoSupportEmbedding {N : ℕ} (I : Finset (Fin N)) : Fin I.card ↪ Fin N :=
  I.equivFin.symm.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
lemma rhoSupportEmbedding_mem {N : ℕ} (I : Finset (Fin N)) (i : Fin I.card) :
    rhoSupportEmbedding I i ∈ I := (I.equivFin.symm i).property
lemma rhoSupportEmbedding_range {N : ℕ} (I : Finset (Fin N)) :
    Set.range (rhoSupportEmbedding I)=(I : Set (Fin N)) := by
  ext i
  constructor
  · rintro ⟨j,rfl⟩
    exact rhoSupportEmbedding_mem I j
  · intro hi
    refine ⟨I.equivFin ⟨i,hi⟩,?_⟩
    simp [rhoSupportEmbedding]

def rhoMaskedCoefficients {N : ℕ} (u : Fin N → ℝ) (I : Finset (Fin N)) : Euclid N :=
  (WithLp.equiv 2 _).symm (fun i => if i∈I then u i else 0)

/-- The Euclidean coefficient representation is exactly the actual retained
record vector, with no rescaling or extra supported coordinates. -/
lemma rhoMasked_eq_realRecordVector {N : ℕ} (u : Fin N → ℝ) (amp : ℝ)
    (t : ℕ) (tail : List ℕ) (T : ℕ) :
    (fun i => rhoMaskedCoefficients u (recordRetainedSupport u amp t tail T) i)=
      realRecordVector u amp t tail T := by
  classical
  funext i
  simp [rhoMaskedCoefficients,realRecordVector]

lemma rhoMasked_support {N : ℕ} (u : Fin N → ℝ) (I : Finset (Fin N)) :
    ∀ i ∉ Set.range (rhoSupportEmbedding I),rhoMaskedCoefficients u I i=0 := by
  intro i hi
  rw [rhoSupportEmbedding_range] at hi
  exact if_neg hi

lemma rhoMasked_mass {N : ℕ} (u : Fin N → ℝ) (I : Finset (Fin N)) :
    ∑ i,|rhoMaskedCoefficients u I i|=∑ i∈I,|u i| := by
  change (∑ i,|if i∈I then u i else 0|)=_
  simp only [apply_ite abs,abs_zero,← Finset.sum_filter]
  simp

lemma rhoMasked_energy {N : ℕ} (u : Fin N → ℝ) (I : Finset (Fin N)) :
    ∑ i,(rhoMaskedCoefficients u I i)^2=∑ i∈I,(u i)^2 := by
  change (∑ i,(if i∈I then u i else 0)^2)=_
  simp only [ite_pow,zero_pow (by decide : 2≠0),← Finset.sum_filter]
  simp

lemma real_actual_group_energy_mass_cap {N : ℕ} (q : ℝ) (u : Fin N → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    0 < dyadicGroupMass u amp groups T r ∧ 0 < dyadicGroupEnergy u amp groups T r ∧
    ∀ i∈dyadicGroupSupport u amp groups T r,
      |u i|≤8*q*dyadicGroupEnergy u amp groups T r/dyadicGroupMass u amp groups T r := by
  have hg : groups[r]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hr,Option.getD_some]
    exact List.getElem_mem hr
  obtain ⟨t,tail,heq,h⟩ := hreg _ hg
  dsimp only at h
  rcases h with ⟨_,_,_,_,_,_,_,_,hm,hQ,_,_,_,hcap,_⟩
  dsimp only [dyadicGroupMass,dyadicGroupEnergy,dyadicGroupSupport]
  rw [heq]
  dsimp only [List.headD_cons,List.tail_cons]
  exact ⟨hm,hQ,fun i hi => (hcap i hi).2.1⟩

def rhoHeadSupport {N : ℕ} (u : Fin N → ℝ) (groups : List (List ℕ)) (T r : ℕ) : Finset (Fin N) :=
  (range r).biUnion (dyadicGroupSupport u ‖u‖ groups T)

def rhoHeadLeft {N p d : ℕ} (eH : Fin p ↪ Fin N)
    (z : GaussianEntries N (d/2) × GaussianEntries N (d/2)) : Euclid (d/2) →L[ℝ] Euclid (d/2) :=
  ContinuousLinearMap.id ℝ (Euclid (d/2))-
    finiteSpanProjector (entriesToRows p (d/2) (selectSample eH z).1)
def rhoHeadRight {N p d : ℕ} (eH : Fin p ↪ Fin N)
    (z : GaussianEntries N (d/2) × GaussianEntries N (d/2)) : Euclid (d/2) →L[ℝ] Euclid (d/2) :=
  ContinuousLinearMap.id ℝ (Euclid (d/2))-
    finiteSpanProjector (entriesToRows p (d/2) (selectSample eH z).2)
def rhoHeadObservable {N p d : ℕ} (eH : Fin p ↪ Fin N) (v : Euclid N)
    (z : GaussianEntries N (d/2) × GaussianEntries N (d/2)) : ℝ :=
  spectralNuclearNorm (projectedBilinear (rhoHeadLeft eH z) (rhoHeadRight eH z) N d z v)

/-- Literal full-array failure event for the current actual retained vector. -/
def actualRhoGroupFailure {N : ℕ} (q : ℝ) (u : Fin N → ℝ)
    (groups : List (List ℕ)) (T d r : ℕ) :
    Set (GaussianEntries N (d/2) × GaussianEntries N (d/2)) :=
  let H := rhoHeadSupport u groups T r
  let J := dyadicGroupSupport u ‖u‖ groups T r
  let eH := rhoSupportEmbedding H
  {z | rhoHeadObservable eH (rhoMaskedCoefficients u J) z <
      generalProj (1/4) (8*q)*Real.sqrt d*dyadicGroupMass u ‖u‖ groups T r}

/-- The head is precisely the union of earlier retained supports. -/
def actualRhoGroupConditional {N : ℕ} (q : ℝ) (u : Fin N → ℝ)
    (groups : List (List ℕ)) (T d r : ℕ) : Prop :=
  (tensorGaussianLaw N (d/2))[(actualRhoGroupFailure q u groups T d r).indicator
    (1 : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → ℝ) |
      selectedSampleSigmaField (rhoSupportEmbedding (rhoHeadSupport u groups T r))]
      ≤ᵐ[tensorGaussianLaw N (d/2)]
    fun _ => Real.exp (-generalProj (1/4) (8*q)*(d:ℝ)*dyadicGroupEffectiveSupport u ‖u‖ groups T r)

def actualRhoGroupProbability {N : ℕ} (q : ℝ) (u : Fin N → ℝ)
    (groups : List (List ℕ)) (T d r : ℕ) : Prop :=
  (tensorGaussianLaw N (d/2)).real (actualRhoGroupFailure q u groups T d r) ≤
    Real.exp (-generalProj (1/4) (8*q)*(d:ℝ)*dyadicGroupEffectiveSupport u ‖u‖ groups T r)

lemma rhoHeadObservable_measurable {N p d : ℕ} (hd : 8≤d)
    (eH : Fin p ↪ Fin N) (v : Euclid N) : Measurable (rhoHeadObservable (d := d) eH v) := by
  have hP : Measurable (rhoHeadLeft (d := d) eH) := measurable_const.sub
    ((measurable_finiteSpanProjector p).comp
      ((measurable_entriesToRows p (d/2)).comp (measurable_fst.comp (measurable_selectSample eH))))
  have hQ : Measurable (rhoHeadRight (d := d) eH) := measurable_const.sub
    ((measurable_finiteSpanProjector p).comp
      ((measurable_entriesToRows p (d/2)).comp (measurable_snd.comp (measurable_selectSample eH))))
  have hB := (measurable_projectedBilinear (h := d/2) N d (by omega) v
    (rhoHeadLeft eH) (rhoHeadRight eH) hP hQ).comp (measurable_id.prodMk measurable_id)
  exact (continuous_spectralNuclear (d/2) (d/2)).measurable.comp hB

lemma actualRhoGroupFailure_measurable {N d : ℕ} (hd : 8≤d)
    (q : ℝ) (u : Fin N → ℝ) (groups : List (List ℕ)) (T r : ℕ) :
    MeasurableSet (actualRhoGroupFailure q u groups T d r) := by
  exact measurableSet_lt (rhoHeadObservable_measurable hd
    (rhoSupportEmbedding (rhoHeadSupport u groups T r))
    (rhoMaskedCoefficients u (dyadicGroupSupport u ‖u‖ groups T r))) measurable_const


lemma actualRhoGroupConditional_probability {N d : ℕ} (hd : 8≤d)
    (q : ℝ) (u : Fin N → ℝ) (groups : List (List ℕ)) (T r : ℕ)
    (hc : actualRhoGroupConditional q u groups T d r) : actualRhoGroupProbability q u groups T d r := by
  have hE := actualRhoGroupFailure_measurable hd q u groups T r
  have h := integral_mono_ae integrable_condExp (integrable_const
    (Real.exp (-generalProj (1/4) (8*q)*(d:ℝ)*dyadicGroupEffectiveSupport u ‖u‖ groups T r))) hc
  rw [integral_condExp (selectedSampleSigmaField_le _),integral_indicator_one hE] at h
  simpa only [actualRhoGroupProbability,integral_const,Measure.real,measure_univ,
    ENNReal.toReal_one,smul_eq_mul,one_mul] using h

/-- Actual support/statistics/event consumer. Its numerical cutoff premise is
about the actual R_r and is supplied by the eventual constructor below. -/
theorem actual_rho_group_conditional {N d : ℕ} (q rho : ℝ) (hq : 1 < q) (hrho : 0 < rho)
    (hrcap : rho  <  min (1/8) (generalUp (1/4) (8*q)/(32*q^2))) (hd : 8≤d)
    (u : Fin N → ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u ‖u‖ T g)
    (hflat : groups.flatten.Nodup) (b : ℕ)
    (hb : SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b)
    (r : ℕ) (hrb : r < b)
    (hlow : generalLow (8*q)*Real.log (d:ℝ)≤dyadicGroupEffectiveSupport u ‖u‖ groups T r) :
    actualRhoGroupConditional q u groups T d r := by
  let H := rhoHeadSupport u groups T r
  let J := dyadicGroupSupport u ‖u‖ groups T r
  let eH := rhoSupportEmbedding H
  let eJ := rhoSupportEmbedding J
  let V := rhoMaskedCoefficients u J
  have hr : r < groups.length := hrb.trans_le hb.1
  have hdis : ∀ i j,eH i≠eJ j := by
    intro i j he
    have hi := rhoSupportEmbedding_mem H i
    obtain ⟨k,hkr,hki⟩ := mem_biUnion.mp hi
    have hj := rhoSupportEmbedding_mem J j
    have hp := real_actual_group_supports_pairwise q u ‖u‖ (norm_nonneg u) groups T hreg hflat
      groups.length le_rfl (mem_range.mpr ((mem_range.mp hkr).trans hr)) (mem_range.mpr hr)
      (ne_of_lt (mem_range.mp hkr))
    apply Finset.disjoint_left.mp hp hki
    change eH i∈J
    rw [he]
    exact hj
  have hbudget : (H.card:ℝ)≤rho*d := by
    rw [show (H.card:ℝ)=∑ k∈range r,dyadicGroupSize u ‖u‖ groups T k from
      paper_real_group_prefix_card q u ‖u‖ (norm_nonneg u) groups T hreg hflat r hr.le]
    exact (sum_le_sum_of_subset_of_nonneg (range_mono hrb.le)
      (by intro k _ _; exact Nat.cast_nonneg _)).trans hb.2.1
  have hpos := real_actual_group_energy_mass_cap q u ‖u‖ groups T hreg r hr
  let E := dyadicGroupEnergy u ‖u‖ groups T r
  let m := dyadicGroupMass u ‖u‖ groups T r
  let R := dyadicGroupEffectiveSupport u ‖u‖ groups T r
  have hE : 0 < E := hpos.2.1
  have hm : 0 < m := hpos.1
  have hsupport : ∀ i∉Set.range eJ,V i=0 := rhoMasked_support u J
  have hsum : ∑ i,(euclideanCoordinateSubfamily eJ V i)^2=(Real.sqrt E)^2 := by
    rw [sum_sq_euclideanCoordinateSubfamily eJ V hsupport,rhoMasked_energy,Real.sq_sqrt hE.le]
    rfl
  have hmass : m=∑ i,|euclideanCoordinateSubfamily eJ V i| := by
    rw [sum_abs_euclideanCoordinateSubfamily eJ V hsupport,rhoMasked_mass]
    rfl
  have hRdef : R=m^2/(Real.sqrt E)^2 := by rw [Real.sq_sqrt hE.le]; rfl
  have hcap : ∀ i,|euclideanCoordinateSubfamily eJ V i|≤(8*q)*Real.sqrt E/Real.sqrt R := by
    intro i
    have hi := rhoSupportEmbedding_mem J i
    change |if eJ i∈J then u (eJ i) else 0|≤_
    rw [if_pos hi]
    calc
      _ ≤ 8*q*E/m := hpos.2.2 _ hi
      _ = (8*q)*(E/m) := by ring
      _ = (8*q)*(Real.sqrt E/Real.sqrt (m^2/E)) := by rw [real_effective_rank_sqrt_identity m E hm hE]
      _ = _ := by dsimp [R,m,E,dyadicGroupEffectiveSupport,dyadicGroupMass,dyadicGroupEnergy]; ring
  have hn := real_actual_group_numerical_bounds q u ‖u‖ groups T hreg r hr
  have hS : dyadicGroupScale u ‖u‖ groups r≤rho*d :=
    hn.2.1.trans ((single_le_sum (f := dyadicGroupSize u ‖u‖ groups T)
      (fun i _ => Nat.cast_nonneg _) (mem_range.mpr hrb)).trans hb.2.1)
  have hp := paper_rho_projected_group_conditional q rho hq hrho hrcap hd eH eJ hdis hbudget
    (euclideanCoordinateSubfamily eJ V) (Real.sqrt_pos.mpr hE) hsum hmass hRdef hlow hS hn.2.2.2.2 hcap
  have he (z : GaussianEntries N (d/2) × GaussianEntries N (d/2)) :
      projectedBilinear
        (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows H.card (d/2) (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows H.card (d/2) (selectSample eH z).2))
        J.card d (selectSample eJ z) (euclideanCoordinateSubfamily eJ V) =
      projectedBilinear
        (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows H.card (d/2) (selectSample eH z).1))
        (ContinuousLinearMap.id ℝ _-finiteSpanProjector (entriesToRows H.card (d/2) (selectSample eH z).2))
        N d z V := by
    unfold projectedBilinear
    rw [gaussianBilinearOperator_selectSample d eJ z V hsupport]
  simp_rw [he] at hp
  exact hp

/-- Unconditional actual-group tail, retaining the exact source c_proj and R_r. -/
theorem actual_rho_group_probability {N d : ℕ} (q rho : ℝ) (hq : 1 < q) (hrho : 0 < rho)
    (hrcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2))) (hd : 8≤d)
    (u : Fin N → ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g∈groups,RealRegularRetainedGroup q u ‖u‖ T g)
    (hflat : groups.flatten.Nodup) (b : ℕ)
    (hb : SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b)
    (r : ℕ) (hrb : r < b)
    (hlow : generalLow (8*q)*Real.log (d:ℝ)≤dyadicGroupEffectiveSupport u ‖u‖ groups T r) :
    actualRhoGroupProbability q u groups T d r :=
  actualRhoGroupConditional_probability hd q u groups T r
    (actual_rho_group_conditional q rho hq hrho hrcap hd u groups T hreg hflat b hb r hrb hlow)

/-- Fully composed source consumer: the dimension threshold is selected before
n and u, the actual greedy retained groups and both cutoffs are constructed,
and every captured nonsparse group's literal full-array failure event receives
the conditional estimate. No regularity, support restriction, rank, or Gaussian
law bridge is supplied as a premise. -/
theorem paper_eventual_actual_rho_conditional
    (q rho : ℝ) (hq : 1 < q) (hrho : 0 < rho)
    (hrcap : rho  <  min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    (T : ℕ) (hT : 0 < T) :
    ∃ d0 : ℕ,∀ d : ℕ,d0≤d → ∀ n : ℕ,∀ u : Fin n → ℝ,
    ∃ N : ℕ,∃ groups : List (List ℕ),∃ p b : ℕ,
      8≤d ∧ 0 < N ∧ (u=0 → groups=[] ∧ p=0 ∧ b=0) ∧
      groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups ∧
      (∀ g∈groups,RealRegularRetainedGroup q u ‖u‖ T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
        fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups T)≤4*q*(1/2:ℝ)^T*coefficientMass u ∧
      p≤b ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length
        (⌊(d:ℝ)/(8192*Real.log d)⌋₊:ℝ) p ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b ∧
      (∀ r,r≤b → (d:ℝ)/4+(rhoHeadSupport u groups T r).card≤(d/2:ℕ)) ∧
      (∀ r,p≤r → r < b →
        generalLow (8*q)*Real.log (d:ℝ)≤dyadicGroupEffectiveSupport u ‖u‖ groups T r ∧
        dyadicGroupEffectiveSupport u ‖u‖ groups T r < generalUp (1/4) (8*q)*d) ∧
      (∀ r,b≤r → r < groups.length →
        rho*(q-1)/((T:ℝ)*q^2)*(d:ℝ)≤dyadicGroupScale u ‖u‖ groups r) ∧
      (∀ K : ℝ,0 < K → ((univ.filter fun i => u i≠0).card:ℝ)≤K*d → b < groups.length →
        ((groups.length-b:ℕ):ℝ)≤1+Real.log ((q^2/(q-1))*K*T/rho)/Real.log q) ∧
      (∀ r,p≤r → r < b → actualRhoGroupConditional q u groups T d r ∧
        actualRhoGroupProbability q u groups T d r) := by
  have hq0 : 0 < q := by linarith
  have hC : 0 < generalLow (8*q) :=
    (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0 < 8*q)).1
  obtain ⟨d0,hd0⟩ := eventually_atTop.mp
    (eventually_paper_rho_numerics q rho (generalLow (8*q)) hq hrho hC T hT)
  refine ⟨d0,?_⟩
  intro d hd n u
  obtain ⟨hd8,hlog,hfloor,hbudget,hlow⟩ := hd0 d hd
  have hdpos : (0:ℝ) < d := by positivity
  obtain ⟨N,groups,p,b,hN,hzero,hflat,hgreedy,hreg,hchain,herror,hpb,hp,hb,hpost,hcapt,hlate⟩ :=
    exists_paper_real_rho_geometry q hq u T hT rho (generalUp (1/4) (8*q)) d hrho
      (lt_min_iff.mp hrcap).2 hdpos hlog hfloor hbudget
  have hflat' : groups.flatten.Nodup := actual_constructor_flatten_nodup u ‖u‖ groups N hflat
  refine ⟨N,groups,p,b,hd8,hN,hzero,hflat,hgreedy,hreg,hchain,herror,hpb,hp,hb,?_,?_,?_,?_,?_⟩
  · intro r hr
    exact paper_real_captured_rank_budget q u ‖u‖ (norm_nonneg u) groups T hreg hflat'
      rho (lt_min_iff.mp hrcap).1 d hd8 b hb r hr
  · intro r hpr hrb
    have hr : r < groups.length := hrb.trans_le hb.1
    exact ⟨hlow.trans (hpost r hpr hr).2,hcapt r hrb⟩
  · intro r hbr hr
    exact (hlate r hbr hr).le
  · intro K hK hsupp hbn
    have hu : u≠0 := by
      intro hz
      have hg := (hzero hz).1
      simpa only [hg,List.length_nil,Nat.not_lt_zero] using hbn
    exact paper_real_rho_late_count q hq u ‖u‖ (norm_pos_iff.mpr hu) groups T hT hreg hchain
      rho K d hrho hK hdpos hsupp b hb hbn
  · intro r hpr hrb
    have hc := actual_rho_group_conditional q rho hq hrho hrcap hd8 u groups T hreg hflat' b hb r hrb
      (hlow.trans (hpost r hpr (hrb.trans_le hb.1)).2)
    exact ⟨hc,actualRhoGroupConditional_probability hd8 q u groups T r hc⟩

#print axioms actual_rho_group_probability
#print axioms actual_rho_group_conditional
#print axioms paper_eventual_actual_rho_conditional
end GaussianEllipsoid.ProjectedClusters
