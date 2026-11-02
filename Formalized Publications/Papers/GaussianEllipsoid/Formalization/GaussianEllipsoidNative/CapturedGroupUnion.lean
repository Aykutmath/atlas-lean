import ActualCapturedCluster

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module Finset
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- The actual sparse cutoff forces the numerical projected-cluster scale. -/
theorem actual_postprefix_effective_support_lower {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (d : ℝ) (p : ℕ)
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊d/(8192*Real.log d)⌋₊ : ℝ) p)
    (hfloor : d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊ : ℝ))
    (r : ℕ) (hpr : p ≤ r) (hr : r < groups.length) :
    3*d/(2097152*T*Real.log d) ≤ dyadicGroupEffectiveSupport u amp groups T r := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hlo := record_scale_after_cutoff (dyadicGroupScale u amp groups)
    (dyadicGroupSize u amp groups T) groups.length p T _ hT'
    (fun j hj => (actual_group_numerical_bounds u amp groups T hreg j hj).1.le)
    (actual_group_doubling u amp groups T hreg hchain)
    (fun j hj => (actual_group_numerical_bounds u amp groups T hreg j hj).2.2.1)
    hp r hpr hr
  have hbase : d/(65536*T*Real.log d) ≤ dyadicGroupScale u amp groups r := by
    have hdiv := div_le_div_of_nonneg_right hfloor (by positivity : 0 ≤ 4*(T:ℝ))
    have heq : d/(16384*Real.log d)/(4*(T:ℝ)) = d/(65536*T*Real.log d) := by ring
    rw [heq] at hdiv
    exact hdiv.trans hlo.le
  have hR := (actual_group_numerical_bounds u amp groups T hreg r hr).2.2.2.1
  calc
    3*d/(2097152*T*Real.log d) = (3/32)*(d/(65536*T*Real.log d)) := by ring
    _ ≤ (3/32)*dyadicGroupScale u amp groups r :=
      mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ ≤ _ := hR

/-- Every group in the actual captured cutoff has admissible effective support. -/
theorem actual_captured_effective_support_upper {n : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g) (d : ℝ) (q : ℕ)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length (d/256) q)
    (r : ℕ) (hrq : r < q) : dyadicGroupEffectiveSupport u amp groups T r ≤ d/4 := by
  have hr : r < groups.length := lt_of_lt_of_le hrq hq.1
  have hb := actual_group_numerical_bounds u amp groups T hreg r hr
  have hkr : dyadicGroupSize u amp groups T r ≤
      ∑ i ∈ range q, dyadicGroupSize u amp groups T i :=
    single_le_sum (fun i _ => by unfold dyadicGroupSize; positivity) (mem_range.mpr hrq)
  have hks := hkr.trans hq.2.1
  nlinarith [hb.2.1, hb.2.2.2.2]

/-- Bad projected-prefix event for one concrete retained dyadic group. -/
def capturedGroupBad {n h d : ℕ} (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup)
    (r : ℕ) : Set (Fin n → Euclid h × Euclid h) :=
  {X | spectralNuclearNorm (operatorFrobenius
    (projectedPrefixBlock (fun i => orderedRetainedCoefficients u amp ha groups T hreg hflat i /
      Real.sqrt d) X (supportCut (dyadicGroupSupport u amp groups T) r)
      (supportCut (dyadicGroupSupport u amp groups T) (r+1)))) <
      projectedConstant * Real.sqrt d * dyadicGroupMass u amp groups T r}

theorem measurableSet_capturedGroupBad {n h d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup)
    (r : ℕ) : MeasurableSet (capturedGroupBad (h:=h) (d:=d) u amp ha groups T hreg hflat r) :=
  measurableSet_lt (measurable_nuclear_projectedPrefixBlock _ _ _) measurable_const

/-- Exact finite union over the actual captured dyadic groups in the canonical
Gaussian law. All small-ball hypotheses come from their actual construction
and the two true support cutoffs. -/
theorem actual_captured_group_union_bound {n h d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (p q : ℕ)
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊(d:ℝ)/(8192*Real.log d)⌋₊ : ℝ) p)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (hd : 0 < d) (hambient : (d:ℝ)/3 ≤ h)
    (hfloor : (d:ℝ)/(16384*Real.log d) ≤ (⌊(d:ℝ)/(8192*Real.log d)⌋₊ : ℝ))
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*T*Real.log d)) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | ∃ r ∈ Ico p q, X ∈ capturedGroupBad (d:=d) u amp ha groups T hreg hflat r} ≤
      (groups.length : ℝ) * Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log d)) := by
  let B := capturedGroupBad (h:=h) (d:=d) u amp ha groups T hreg hflat
  let μ := gaussianBilinearSampleLaw (Fin n) h h
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hh : 0 < h := by exact_mod_cast (by linarith : (0:ℝ) < h)
  have hcutq : (supportCut (dyadicGroupSupport u amp groups T) q : ℝ) ≤ (d:ℝ)/256 := by
    rw [actual_dyadic_supportCut_cast]
    exact hq.2.1
  have hprob : ∀ r ∈ Ico p q, μ.real (B r) ≤
      Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log d)) := by
    intro r hr
    obtain ⟨hpr,hrq⟩ := mem_Ico.mp hr
    have hrg : r < groups.length := hrq.trans_le hq.1
    have hcutr : (supportCut (dyadicGroupSupport u amp groups T) r : ℝ) ≤
        supportCut (dyadicGroupSupport u amp groups T) q :=
      Nat.cast_le.mpr (supportCut_mono _ hrq.le)
    have hbudget : (d:ℝ)/4 + supportCut (dyadicGroupSupport u amp groups T) r ≤ h := by linarith
    have hRlow := actual_postprefix_effective_support_lower u amp groups T hT hreg hchain
      (d:ℝ) p hp hfloor r hpr hrg
    have hRup := actual_captured_effective_support_upper u amp groups T hreg (d:ℝ) q hq r hrq
    have hb := actual_captured_group_smallball u amp ha groups T hreg hflat r hrg hh hbudget
      (hnum.trans hRlow) (hRup.trans (by linarith))
    apply hb.trans
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hRlow (by positivity : 0 ≤ (d:ℝ)/65536)
    have he : (d:ℝ)/65536 * (3*(d:ℝ)/(2097152*T*Real.log d)) =
        3*(d:ℝ)^2/(137438953472*T*Real.log d) := by ring
    rw [he] at hm
    convert! neg_le_neg hm using 1 <;> ring
  have hset : {X | ∃ r ∈ Ico p q, X ∈ B r} = ⋃ r ∈ Ico p q, B r := by ext X; simp
  change μ.real {X | ∃ r ∈ Ico p q, X ∈ B r} ≤ _
  rw [hset]
  calc
    _ ≤ ∑ r ∈ Ico p q, μ.real (B r) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Ico p q, Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log d)) :=
      sum_le_sum hprob
    _ = ((q-p : ℕ):ℝ) * Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log d)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast ((Nat.sub_le q p).trans hq.1)) (Real.exp_nonneg _)

end GaussianEllipsoid.ProjectedClusters
