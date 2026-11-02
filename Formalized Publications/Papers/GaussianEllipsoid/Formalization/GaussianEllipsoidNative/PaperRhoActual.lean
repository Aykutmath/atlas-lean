import PaperRhoScalars
import RealDyadicPaper
import LateGroupCount

noncomputable section
open Finset Filter
namespace GaussianEllipsoidCandidate

/-- The exact source cumulative support through the current general-q group. -/
theorem real_actual_support_through_bound {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ))) (r : ℕ) (hr : r<groups.length) :
    (∑ i ∈ range (r+1),dyadicGroupSize u amp groups T i) ≤
      (T:ℝ)*q^2/(q-1)*dyadicGroupScale u amp groups r := by
  have hp := (real_actual_group_prefix_bounds q hq u amp groups T hreg hchain r hr).2
  have hk := (real_actual_group_numerical_bounds q u amp groups T hreg r hr).2.2.1
  rw [sum_range_succ]
  calc
    _ ≤ (T:ℝ)*q/(q-1)*dyadicGroupScale u amp groups r+
        q*T*dyadicGroupScale u amp groups r := add_le_add hp hk
    _ = _ := by
      have hqn : q-1≠0 := ne_of_gt (sub_pos.mpr hq)
      field_simp [hqn]
      <;> ring

/-- Maximal sparse and arbitrary-rho span cutoffs for the actual general-q
record list, including empty and all-captured cases. -/
theorem paper_real_rho_cutoffs {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (rho cup d : ℝ) (hrho : 0<rho) (hrcap : rho<cup/(32*q^2))
    (hd : 0<d) (hlog : 0<Real.log d)
    (hfloor : d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊:ℝ))
    (hbudget : (⌊d/(8192*Real.log d)⌋₊:ℝ) ≤ rho*d) :
    ∃ p b : ℕ,p≤b ∧
      SupportCutoff (dyadicGroupSize u amp groups T) groups.length
        (⌊d/(8192*Real.log d)⌋₊:ℝ) p ∧
      SupportCutoff (dyadicGroupSize u amp groups T) groups.length (rho*d) b ∧
      (∀ r,p≤r → r<groups.length →
        (q-1)*d/(16384*T*q^2*Real.log d) ≤ dyadicGroupScale u amp groups r ∧
        3*(q-1)*d/(262144*T*q^3*Real.log d) ≤ dyadicGroupEffectiveSupport u amp groups T r) ∧
      (∀ r,r<b → dyadicGroupEffectiveSupport u amp groups T r<cup*d) ∧
      (∀ r,b≤r → r<groups.length →
        rho*(q-1)/((T:ℝ)*q^2)*d < dyadicGroupScale u amp groups r) := by
  let k := dyadicGroupSize u amp groups T
  let S := dyadicGroupScale u amp groups
  have hq0 : 0<q := by linarith
  have hqm : 0<q-1 := by linarith
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  have hk0 : ∀ r,0≤k r := fun _ => Nat.cast_nonneg _
  obtain ⟨p,hp⟩ := exists_supportCutoff k groups.length (⌊d/(8192*Real.log d)⌋₊:ℝ) (by positivity)
  obtain ⟨b,hb⟩ := exists_supportCutoff k groups.length (rho*d) (by positivity)
  have hpb := supportCutoff_mono k groups.length _ _ p b hk0 hbudget hp hb
  refine ⟨p,b,hpb,hp,hb,?_,?_,?_⟩
  · intro r hpr hr
    have hnum := real_actual_group_numerical_bounds q u amp groups T hreg r hr
    have hthrough := real_actual_support_through_bound q hq u amp groups T hreg hchain r hr
    have hex := hp.2.2 r hpr hr
    have hlow : (q-1)*d/(16384*T*q^2*Real.log d) ≤ S r := by
      have hf := hfloor.trans (hex.le.trans hthrough)
      have hp := mul_le_mul_of_nonneg_right hf hqm.le
      have he : ((T:ℝ)*q^2/(q-1)*S r)*(q-1)=(T:ℝ)*q^2*S r := by field_simp <;> try ring
      rw [he] at hp
      apply (div_le_iff₀ (by positivity : 0<16384*(T:ℝ)*q^2*Real.log d)).mpr
      have hdiv := (div_le_iff₀ (by positivity : 0<16384*Real.log d)).mp
        (show (d*(q-1))/(16384*Real.log d) ≤ (T:ℝ)*q^2*S r by
          simpa only [div_mul_eq_mul_div] using hp)
      nlinarith
    refine ⟨hlow,?_⟩
    calc
      _ = (3/(16*q))*((q-1)*d/(16384*T*q^2*Real.log d)) := by field_simp <;> try ring
      _ ≤ (3/(16*q))*S r := mul_le_mul_of_nonneg_left hlow (by positivity)
      _ ≤ _ := hnum.2.2.2.1
  · intro r hrb
    have hr : r<groups.length := lt_of_lt_of_le hrb hb.1
    have hn := real_actual_group_numerical_bounds q u amp groups T hreg r hr
    have hk : k r≤rho*d :=
      (single_le_sum (fun i _ => hk0 i) (mem_range.mpr hrb)).trans hb.2.1
    exact rho_effective_support_cap q rho cup d (S r) _ hq hrho hrcap hd
      (hn.2.1.trans hk) hn.2.2.2.2
  · intro r hbr hr
    exact rho_first_late_scale q T rho d (S r) _ hq hT' hrho (hb.2.2 r hbr hr)
      (real_actual_support_through_bound q hq u amp groups T hreg hchain r hr)

/-- The source logarithmic late count for the actual list. When b=N there
are exactly zero late groups; the logarithmic display is only the nonempty branch. -/
theorem paper_real_rho_late_count {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ) (ha : 0<amp)
    (groups : List (List ℕ)) (T : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (rho K d : ℝ) (hrho : 0<rho) (hK : 0<K) (hd : 0<d)
    (hsupp : ((univ.filter fun i => u i≠0).card:ℝ) ≤ K*d)
    (b : ℕ) (hb : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (rho*d) b)
    (hbn : b<groups.length) :
    ((groups.length-b:ℕ):ℝ) ≤ 1+Real.log ((q^2/(q-1))*K*T/rho)/Real.log q := by
  have hT' : (0:ℝ)<T := by exact_mod_cast hT
  apply rho_late_count_log q T rho K d hq hT' hrho hK hd
    (dyadicGroupScale u amp groups) groups.length b hbn
    (real_actual_group_growth q u amp groups T hreg hchain)
  · exact rho_first_late_scale q T rho d _ _ hq hT' hrho (hb.2.2 b le_rfl hbn)
      (real_actual_support_through_bound q hq u amp groups T hreg hchain b hbn)
  · intro r hr
    exact (actual_group_scale_le_support u amp ha groups r).trans hsupp

/-- Exact cardinality of all earlier retained samples, valid for the real-q
constructor, is the support budget used for residual-rank loss. -/
theorem paper_real_group_prefix_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup) (n : ℕ) (hn : n≤groups.length) :
    (((range n).biUnion (dyadicGroupSupport u amp groups T)).card:ℝ)=
      ∑ r ∈ range n,dyadicGroupSize u amp groups T r := by
  classical
  rw [card_biUnion (real_actual_group_supports_pairwise q u amp ha groups T hreg hflat n hn)]
  simp only [Nat.cast_sum,dyadicGroupSize]

/-- The actual pre-group sample count plus d/4 fits inside h=floor(d/2)
for every captured group and every rho in the source interval. -/
theorem paper_real_captured_rank_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup) (rho : ℝ) (hrho : rho<1/8)
    (d : ℕ) (hd : 8≤d) (b : ℕ)
    (hb : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (rho*d) b)
    (r : ℕ) (hr : r≤b) :
    (d:ℝ)/4+(((range r).biUnion (dyadicGroupSupport u amp groups T)).card:ℝ) ≤ (d/2:ℕ) := by
  rw [paper_real_group_prefix_card q u amp ha groups T hreg hflat r (hr.trans hb.1)]
  have hs : (∑ i ∈ range r,dyadicGroupSize u amp groups T i) ≤ rho*d :=
    (sum_le_sum_of_subset_of_nonneg (range_mono hr)
      (by intro i _ _; exact Nat.cast_nonneg _)).trans hb.2.1
  have hm := rho_floor_half_margin rho hrho d hd
  linarith

/-- Source-facing construction: arbitrary u (including zero), its literal
sup-norm dyadic scale, the exact greedy record certificate, and both maximal
cutoffs are constructed; no abstract decomposition is assumed. -/
theorem exists_paper_real_rho_geometry {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (T : ℕ) (hT : 0<T)
    (rho cup d : ℝ) (hrho : 0<rho) (hrcap : rho<cup/(32*q^2))
    (hd : 0<d) (hlog : 0<Real.log d)
    (hfloor : d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊:ℝ))
    (hbudget : (⌊d/(8192*Real.log d)⌋₊:ℝ) ≤ rho*d) :
    ∃ N : ℕ,∃ groups : List (List ℕ),∃ p b : ℕ,
      0<N ∧ (u=0 → groups=[] ∧ p=0 ∧ b=0) ∧
      groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups ∧
      (∀ g ∈ groups,RealRegularRetainedGroup q u ‖u‖ T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
        fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
        4*q*(1/2:ℝ)^T*coefficientMass u ∧ p≤b ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length
        (⌊d/(8192*Real.log d)⌋₊:ℝ) p ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b ∧
      (∀ r,p≤r → r<groups.length →
        (q-1)*d/(16384*T*q^2*Real.log d) ≤ dyadicGroupScale u ‖u‖ groups r ∧
        3*(q-1)*d/(262144*T*q^3*Real.log d) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r) ∧
      (∀ r,r<b → dyadicGroupEffectiveSupport u ‖u‖ groups T r<cup*d) ∧
      (∀ r,b≤r → r<groups.length →
        rho*(q-1)/((T:ℝ)*q^2)*d < dyadicGroupScale u ‖u‖ groups r) := by
  obtain ⟨N,groups,hN,hzero,hcover,hempty,hflat,hreg,hchain,herror,hgreedy⟩ :=
    real_paper_dyadic_decomposition q hq u T hT
  obtain ⟨p,b,hpb,hp,hb,hpost,hcapt,hlate⟩ :=
    paper_real_rho_cutoffs q hq u ‖u‖ groups T hT hreg hchain rho cup d
      hrho hrcap hd hlog hfloor hbudget
  refine ⟨N,groups,p,b,hN,?_,hflat,hgreedy,hreg,hchain,herror,hpb,hp,hb,hpost,hcapt,hlate⟩
  intro hz
  have hg := hzero hz
  refine ⟨hg,?_,?_⟩
  · have hh := hp.1
    rw [hg] at hh
    simpa using hh
  · have hh := hb.1
    rw [hg] at hh
    simpa using hh

#print axioms paper_real_rho_cutoffs
#print axioms paper_real_rho_late_count
#print axioms paper_real_captured_rank_budget
#print axioms exists_paper_real_rho_geometry
end GaussianEllipsoidCandidate
