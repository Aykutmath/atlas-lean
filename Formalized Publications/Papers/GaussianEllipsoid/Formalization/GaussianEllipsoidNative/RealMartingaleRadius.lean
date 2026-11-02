import PaperRhoActual
import CutoffThresholds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable
open Finset Filter
namespace GaussianEllipsoidCandidate

/-- The literal retained coefficient vector of the indexed actual group. -/
def realDyadicGroupVector {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) : ι → ℝ :=
  fun i => if i ∈ dyadicGroupSupport u amp groups T r then u i else 0

theorem realDyadicGroupVector_eq_record {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) :
    realDyadicGroupVector u amp groups T r =
      realRecordVector u amp ((groups[r]?.getD []).headD 0)
        (groups[r]?.getD []).tail T := rfl

/-- Its l1 mass is exactly m_r, not an independent scalar parameter. -/
theorem realDyadicGroupVector_mass {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T r : ℕ) :
    coefficientMass (realDyadicGroupVector u amp groups T r) =
      dyadicGroupMass u amp groups T r := by
  simp [coefficientMass,realDyadicGroupVector,dyadicGroupMass,apply_ite abs]

/-- The support in the group statistics is its actual nonzero support. -/
theorem realDyadicGroupVector_support {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0<amp) (groups : List (List ℕ)) (T r : ℕ) :
    Function.support (realDyadicGroupVector u amp groups T r) =
      (dyadicGroupSupport u amp groups T r : Set ι) := by
  exact realRecordVector_support u amp ha _ _ T

/-- The sup norm here is the true Pi norm; regularity gives the sharp cap 2m/S. -/
theorem real_actual_group_sup_le_mass {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (r : ℕ) (hr : r<groups.length) :
    ‖realDyadicGroupVector u amp groups T r‖ ≤
      2*dyadicGroupMass u amp groups T r/dyadicGroupScale u amp groups r := by
  have hg : groups[r]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hr,Option.getD_some]
    exact List.getElem_mem hr
  obtain ⟨t,tail,heq,h⟩ := hreg _ hg
  dsimp only at h
  rcases h with ⟨hS,ha,hklo,hkhi,hmlo,hmhi,hQlo,hQhi,hm,hQ,hRlo,hRhi,henergy,hcap,htail⟩
  dsimp [realDyadicGroupVector,dyadicGroupMass,dyadicGroupSupport,dyadicGroupScale]
  rw [heq]
  dsimp only [List.headD_cons,List.tail_cons]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  simp only [realDyadicGroupVector,dyadicGroupSupport,heq,List.headD_cons,List.tail_cons]
  split_ifs with hi
  · simpa only [Real.norm_eq_abs] using (hcap i hi).2.2
  · simp only [norm_zero]
    positivity

/-- Each group mass is bounded by the actual retained l1 mass, using the exact
partition identity from the real-q construction. -/
theorem real_actual_group_mass_le_total {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup) (r : ℕ) (hr : r<groups.length) :
    dyadicGroupMass u amp groups T r ≤ coefficientMass (retainedGroupVector u amp groups T) := by
  rw [real_actual_group_mass_sum q u amp ha groups T hreg hflat]
  exact single_le_sum (fun j _ => by unfold dyadicGroupMass; positivity) (mem_range.mpr hr)

/-- B_mart is the maximum group sup norm divided by sqrt(d). The maximum of
an empty post-prefix list is zero, so zero vectors and all-sparse lists are covered. -/
def realPostprefixMGFRadius {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) (d : ℝ) : ℝ :=
  if h : (Ico p groups.length).Nonempty then
    (Ico p groups.length).sup' h (fun r => ‖realDyadicGroupVector u amp groups T r‖/Real.sqrt d)
  else 0

theorem realPostprefixMGFRadius_empty {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) (d : ℝ)
    (hp : groups.length≤p) : realPostprefixMGFRadius u amp groups T p d = 0 := by
  simp [realPostprefixMGFRadius,not_lt.mpr hp]

/-- For a nonempty post-prefix list this definition is the literal finite maximum. -/
theorem realPostprefixMGFRadius_eq_max {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T p : ℕ) (d : ℝ)
    (hp : p<groups.length) :
    realPostprefixMGFRadius u amp groups T p d =
      (Ico p groups.length).sup' (Finset.nonempty_Ico.mpr hp)
        (fun r => ‖realDyadicGroupVector u amp groups T r‖/Real.sqrt d) := by
  simp only [realPostprefixMGFRadius,dif_pos (Finset.nonempty_Ico.mpr hp)]

/-- Each literal post-prefix group has radius at most 2 L M log(d)/(d sqrt(d)). -/
theorem real_actual_group_mgf_radius_le {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup)
    (d L : ℝ) (hd : 0<d) (hlog : 0<Real.log d) (hL : 0<L)
    (hscale : ∀ r,p≤r → r<groups.length → d/(L*Real.log d)≤dyadicGroupScale u amp groups r)
    (r : ℕ) (hpr : p≤r) (hr : r<groups.length) :
    ‖realDyadicGroupVector u amp groups T r‖/Real.sqrt d ≤
      2*L*coefficientMass (retainedGroupVector u amp groups T)*Real.log d/(d*Real.sqrt d) := by
  let M := coefficientMass (retainedGroupVector u amp groups T)
  let S := dyadicGroupScale u amp groups r
  have hM : 0≤M := coefficientMass_nonneg _
  have hS : 0<S := (real_actual_group_numerical_bounds q u amp groups T hreg r hr).1
  have hm := real_actual_group_mass_le_total q u amp ha groups T hreg hflat r hr
  have hcap := real_actual_group_sup_le_mass q u amp groups T hreg r hr
  have hds : d ≤ S*(L*Real.log d) := (div_le_iff₀ (by positivity)).mp (hscale r hpr hr)
  have hbound : ‖realDyadicGroupVector u amp groups T r‖ ≤ 2*L*M*Real.log d/d := by
    calc
      _ ≤ 2*dyadicGroupMass u amp groups T r/S := hcap
      _ ≤ 2*M/S := div_le_div_of_nonneg_right (by linarith) hS.le
      _ ≤ 2*L*M*Real.log d/d := by
        apply (div_le_div_iff₀ hS hd).mpr
        have hmul := mul_le_mul_of_nonneg_left hds (show 0≤2*M by positivity)
        nlinarith
  calc
    _ ≤ (2*L*M*Real.log d/d)/Real.sqrt d :=
      div_le_div_of_nonneg_right hbound (Real.sqrt_nonneg d)
    _ = _ := by dsimp [M]; ring

/-- Literal maximum form of the source's B_mart estimate, without a positivity
assumption on M and with the empty maximum interpreted as zero. -/
theorem real_actual_postprefix_mgf_radius_le {ι : Type*} [Fintype ι]
    (q : ℝ) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T p : ℕ)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup)
    (d L : ℝ) (hd : 0<d) (hlog : 0<Real.log d) (hL : 0<L)
    (hscale : ∀ r,p≤r → r<groups.length → d/(L*Real.log d)≤dyadicGroupScale u amp groups r) :
    realPostprefixMGFRadius u amp groups T p d ≤
      2*L*coefficientMass (retainedGroupVector u amp groups T)*Real.log d/(d*Real.sqrt d) := by
  unfold realPostprefixMGFRadius
  split_ifs with h
  · apply Finset.sup'_le
    intro r hr
    exact real_actual_group_mgf_radius_le q u amp ha groups T p hreg hflat d L hd hlog hL
      hscale r (mem_Ico.mp hr).1 (mem_Ico.mp hr).2
  · have hM := coefficientMass_nonneg (retainedGroupVector u amp groups T)
    positivity

/-- The maximal source sparse cutoff forces the general-q scale lower bound. -/
theorem real_actual_sparse_postprefix_scale {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T p : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (d : ℝ) (hd : 0<d) (hlog : 0<Real.log d)
    (hfloor : d/(16384*Real.log d)≤(⌊d/(8192*Real.log d)⌋₊:ℝ))
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊d/(8192*Real.log d)⌋₊:ℝ) p)
    (r : ℕ) (hpr : p≤r) (hr : r<groups.length) :
    d/((16384*T*q^2/(q-1))*Real.log d)≤dyadicGroupScale u amp groups r := by
  have hq0 : 0<q := by linarith
  have hqm : 0<q-1 := by linarith
  have hTr : (0:ℝ)<T := Nat.cast_pos.mpr hT
  have hthrough := real_actual_support_through_bound q hq u amp groups T hreg hchain r hr
  have hf := hfloor.trans ((hp.2.2 r hpr hr).le.trans hthrough)
  have hprod := mul_le_mul_of_nonneg_right hf hqm.le
  have he : ((T:ℝ)*q^2/(q-1)*dyadicGroupScale u amp groups r)*(q-1)=
      (T:ℝ)*q^2*dyadicGroupScale u amp groups r := by field_simp <;> ring
  rw [he] at hprod
  apply (div_le_iff₀ (by positivity : 0<(16384*(T:ℝ)*q^2/(q-1))*Real.log d)).mpr
  have hh := (div_le_iff₀ (by positivity : 0<16384*Real.log d)).mp
    (show (d*(q-1))/(16384*Real.log d)≤(T:ℝ)*q^2*dyadicGroupScale u amp groups r by
      simpa only [div_mul_eq_mul_div] using hprod)
  calc
    d ≤ (dyadicGroupScale u amp groups r*(16384*T*q^2*Real.log d))/(q-1) :=
      (le_div_iff₀ hqm).mpr (by nlinarith [hh])
    _ = _ := by ring

/-- Source lines 2230-2234, with explicit C(q,T)=32768 T q²/(q-1). -/
theorem real_actual_sparse_mgf_radius_le {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T p : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (d : ℝ) (hd : 0<d) (hlog : 0<Real.log d)
    (hfloor : d/(16384*Real.log d)≤(⌊d/(8192*Real.log d)⌋₊:ℝ))
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊d/(8192*Real.log d)⌋₊:ℝ) p) :
    realPostprefixMGFRadius u amp groups T p d ≤
      (32768*T*q^2/(q-1))*coefficientMass (retainedGroupVector u amp groups T)*
        Real.log d/d^(3/2:ℝ) := by
  have hq0 : 0<q := by linarith
  have hqm : 0<q-1 := by linarith
  have hTr : (0:ℝ)<T := Nat.cast_pos.mpr hT
  have hh := real_actual_postprefix_mgf_radius_le q u amp ha groups T p hreg hflat
    d (16384*T*q^2/(q-1)) hd hlog (by positivity)
    (real_actual_sparse_postprefix_scale q hq u amp groups T p hT hreg hchain d hd hlog hfloor hp)
  have he : d*Real.sqrt d=d^(3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hd]
    simp
  rw [he] at hh
  convert hh using 1 <;> ring

/-- The chosen source constant is positive and depends only on q and T. -/
theorem real_mgf_radius_constant_pos (q : ℝ) (hq : 1<q) (T : ℕ) (hT : 0<T) :
    0 < 32768*(T:ℝ)*q^2/(q-1) := by
  have hq0 : 0<q := by linarith
  have hqm : 0<q-1 := by linarith
  have hTr : (0:ℝ)<T := Nat.cast_pos.mpr hT
  positivity

/-- The source's homogeneous M=1 version uses the very same retained vectors. -/
theorem real_actual_sparse_mgf_radius_normalized {ι : Type*} [Fintype ι]
    (q : ℝ) (hq : 1<q) (u : ι → ℝ) (amp : ℝ) (ha : 0≤amp)
    (groups : List (List ℕ)) (T p : ℕ) (hT : 0<T)
    (hreg : ∀ g ∈ groups,RealRegularRetainedGroup q u amp T g)
    (hflat : groups.flatten.Nodup)
    (hchain : groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
      fun t => ((dyadicBin u amp t).card:ℝ)))
    (d : ℝ) (hd : 0<d) (hlog : 0<Real.log d)
    (hfloor : d/(16384*Real.log d)≤(⌊d/(8192*Real.log d)⌋₊:ℝ))
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊d/(8192*Real.log d)⌋₊:ℝ) p)
    (hM : coefficientMass (retainedGroupVector u amp groups T)=1) :
    realPostprefixMGFRadius u amp groups T p d ≤
      (32768*T*q^2/(q-1))*Real.log d/d^(3/2:ℝ) := by
  simpa only [hM,mul_one] using real_actual_sparse_mgf_radius_le q hq u amp ha groups T p hT
    hreg hflat hchain d hd hlog hfloor hp

/-- The large-d threshold precedes n and u. All groups and the maximal sparse
cutoff are constructed from u, and M is their actual retained l1 mass. -/
theorem paper_eventual_real_mgf_radius
    (q : ℝ) (hq : 1<q) (T : ℕ) (hT : 0<T) :
    ∃ d0 : ℕ,∀ d : ℕ,d0≤d → ∀ n : ℕ,∀ u : Fin n → ℝ,
    ∃ N : ℕ,∃ groups : List (List ℕ),∃ p : ℕ,
      8≤d ∧ 0<Real.log (d:ℝ) ∧ 0<N ∧
      (u=0 → groups=[] ∧ p=0 ∧ realPostprefixMGFRadius u ‖u‖ groups T p d=0) ∧
      groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups ∧
      (∀ g ∈ groups,RealRegularRetainedGroup q u ‖u‖ T g) ∧
      groups.IsChain (GaussianEllipsoid.PaperRealRecord.RecordSuccessor q
        fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length
        (⌊(d:ℝ)/(8192*Real.log d)⌋₊:ℝ) p ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups T)≤4*q*(1/2:ℝ)^T*coefficientMass u ∧
      coefficientMass (retainedGroupVector u ‖u‖ groups T)=
        ∑ r ∈ range groups.length,coefficientMass (realDyadicGroupVector u ‖u‖ groups T r) ∧
      realPostprefixMGFRadius u ‖u‖ groups T p d ≤
        (32768*T*q^2/(q-1))*coefficientMass (retainedGroupVector u ‖u‖ groups T)*
          Real.log d/(d:ℝ)^(3/2:ℝ) := by
  have hevent := tendsto_natCast_atTop_atTop.eventually eventually_sparse_cutoff_bounds
  obtain ⟨d0,hd0⟩ := eventually_atTop.mp ((eventually_ge_atTop (8:ℕ)).and hevent)
  refine ⟨d0,?_⟩
  intro d hd n u
  obtain ⟨hd8,hlog,hfloor,hbudget⟩ := hd0 d hd
  have hdpos : (0:ℝ)<d := by positivity
  obtain ⟨N,groups,hN,hzero,hcover,hempty,hflat,hreg,hchain,herror,hgreedy⟩ :=
    real_paper_dyadic_decomposition q hq u T hT
  obtain ⟨p,hp⟩ := exists_supportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length
    (⌊(d:ℝ)/(8192*Real.log d)⌋₊:ℝ) (by positivity)
  have hnodup : groups.flatten.Nodup := actual_constructor_flatten_nodup u ‖u‖ groups N hflat
  refine ⟨N,groups,p,hd8,hlog,hN,?_,hflat,hgreedy,hreg,hchain,hp,herror,?_,?_⟩
  · intro hz
    have hg := hzero hz
    have hp0 : p=0 := by have hh := hp.1; simpa only [hg,List.length_nil,Nat.le_zero] using hh
    exact ⟨hg,hp0,realPostprefixMGFRadius_empty u ‖u‖ groups T p d (by simp [hg])⟩
  · simp_rw [realDyadicGroupVector_mass]
    exact real_actual_group_mass_sum q u ‖u‖ (norm_nonneg u) groups T hreg hnodup
  · exact real_actual_sparse_mgf_radius_le q hq u ‖u‖ (norm_nonneg u) groups T p hT
      hreg hnodup hchain d hdpos hlog hfloor hp

#print axioms realDyadicGroupVector
#print axioms realPostprefixMGFRadius
#print axioms realDyadicGroupVector_eq_record
#print axioms realDyadicGroupVector_mass
#print axioms realDyadicGroupVector_support
#print axioms real_actual_group_sup_le_mass
#print axioms real_actual_group_mass_le_total
#print axioms realPostprefixMGFRadius_empty
#print axioms real_actual_group_mgf_radius_le
#print axioms real_actual_postprefix_mgf_radius_le
#print axioms real_actual_sparse_postprefix_scale
#print axioms real_actual_sparse_mgf_radius_le
#print axioms realPostprefixMGFRadius_eq_max
#print axioms real_mgf_radius_constant_pos
#print axioms real_actual_sparse_mgf_radius_normalized
#print axioms paper_eventual_real_mgf_radius
end GaussianEllipsoidCandidate
