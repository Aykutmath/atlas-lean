import PaperRhoActual
import PaperRhoProjected
import ActualSupportGeometry

noncomputable section
open Finset Filter GaussianEllipsoid.ProjectedClusters
namespace GaussianEllipsoidCandidate

/-- Combined paper-facing rho construction. The starting dimension is chosen
from q,T,rho before n and u. It preserves h=floor(d/2), exact greedy records,
zero-vector case, maximal support cutoffs, rank budgets, regular-group support
thresholds and the literal nonempty-late logarithmic count. -/
theorem paper_eventual_real_rho_geometry
    (q rho : ℝ) (hq : 1<q) (hrho : 0<rho)
    (hrcap : rho < min (1/8) (generalUp (1/4) (8*q)/(32*q^2)))
    (T : ℕ) (hT : 0<T) :
    ∃ d0 : ℕ,∀ d : ℕ,d0≤d → ∀ n : ℕ,∀ u : Fin n → ℝ,
    ∃ N : ℕ,∃ groups : List (List ℕ),∃ p b : ℕ,
      8≤d ∧ 0<N ∧ (u=0 → groups=[] ∧ p=0 ∧ b=0) ∧
      groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
      GaussianEllipsoid.PaperRealRecord.RecordGrouping q
        (fun t => ((dyadicBin u ‖u‖ t).card:ℝ)) (dyadicRecordLevels u ‖u‖ N) groups ∧
      coefficientMass (u-retainedGroupVector u ‖u‖ groups T) ≤
        4*q*(1/2:ℝ)^T*coefficientMass u ∧ p≤b ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length
        (⌊(d:ℝ)/(8192*Real.log d)⌋₊:ℝ) p ∧
      SupportCutoff (dyadicGroupSize u ‖u‖ groups T) groups.length (rho*d) b ∧
      (∀ r,r≤b → (d:ℝ)/4+
        (((range r).biUnion (dyadicGroupSupport u ‖u‖ groups T)).card:ℝ) ≤ (d/2:ℕ)) ∧
      (∀ r,p≤r → r<b →
        generalLow (8*q)*Real.log (d:ℝ) ≤ dyadicGroupEffectiveSupport u ‖u‖ groups T r ∧
        dyadicGroupEffectiveSupport u ‖u‖ groups T r<generalUp (1/4) (8*q)*d) ∧
      (∀ r,b≤r → r<groups.length →
        rho*(q-1)/((T:ℝ)*q^2)*(d:ℝ)≤dyadicGroupScale u ‖u‖ groups r) ∧
      (∀ K : ℝ,0<K → ((univ.filter fun i => u i≠0).card:ℝ)≤K*d → b<groups.length →
        ((groups.length-b:ℕ):ℝ) ≤ 1+Real.log ((q^2/(q-1))*K*T/rho)/Real.log q) := by
  have hq0 : 0<q := by linarith
  have hC : 0<generalLow (8*q) :=
    (generalConstants_pos (c:=(1/4:ℝ)) (by norm_num) (by positivity : 0<8*q)).1
  obtain ⟨d0,hd0⟩ := (eventually_atTop.mp
    (eventually_paper_rho_numerics q rho (generalLow (8*q)) hq hrho hC T hT))
  refine ⟨d0,?_⟩
  intro d hd n u
  obtain ⟨hd8,hlog,hfloor,hbudget,hlow⟩ := hd0 d hd
  have hdpos : (0:ℝ)<d := by positivity
  obtain ⟨N,groups,p,b,hN,hzero,hflat,hgreedy,hreg,hchain,herror,hpb,hp,hb,hpost,hcapt,hlate⟩ :=
    exists_paper_real_rho_geometry q hq u T hT rho (generalUp (1/4) (8*q)) d hrho
      (lt_min_iff.mp hrcap).2 hdpos hlog hfloor hbudget
  have hflat' : groups.flatten.Nodup := actual_constructor_flatten_nodup u ‖u‖ groups N hflat
  refine ⟨N,groups,p,b,hd8,hN,hzero,hflat,hgreedy,herror,hpb,hp,hb,?_,?_,?_,?_⟩
  · intro r hr
    exact paper_real_captured_rank_budget q u ‖u‖ (norm_nonneg u) groups T hreg hflat'
      rho (lt_min_iff.mp hrcap).1 d hd8 b hb r hr
  · intro r hpr hrb
    have hr : r<groups.length := lt_of_lt_of_le hrb hb.1
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

#print axioms paper_eventual_real_rho_geometry
end GaussianEllipsoidCandidate
