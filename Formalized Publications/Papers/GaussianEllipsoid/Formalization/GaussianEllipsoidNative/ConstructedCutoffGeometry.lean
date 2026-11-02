import ActualSupportGeometry
import RetainedTailConstants

namespace GaussianEllipsoidCandidate
open Finset Filter

/-- One eventual natural-dimension threshold supplies every sparse-prefix,
projected-even-block, and macroscopic-late-bin numerical requirement. -/
theorem eventually_natural_cutoff_thresholds (T : ℕ) (hT : 0 < T) :
    ∀ᶠ d : ℕ in atTop,
      (0:ℝ) < d ∧ 0 < Real.log (d:ℝ) ∧
      (d:ℝ)/(16384*Real.log (d:ℝ)) ≤ (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) ∧
      (⌊(d:ℝ)/(8192*Real.log (d:ℝ))⌋₊ : ℝ) ≤ (d:ℝ)/256 ∧
      4096 ≤ 3*(d:ℝ)/(2097152*T*Real.log (d:ℝ)) ∧
      65536*(T:ℝ) ≤ d := by
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hR := eventually_postprefix_effective_support T hT'
  have hall : ∀ᶠ d : ℝ in atTop,
      0 < d ∧ 0 < Real.log d ∧
      d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊ : ℝ) ∧
      (⌊d/(8192*Real.log d)⌋₊ : ℝ) ≤ d/256 ∧
      4096 ≤ 3*d/(2097152*T*Real.log d) ∧ 65536*(T:ℝ) ≤ d := by
    filter_upwards [eventually_sparse_cutoff_bounds, hR,
      eventually_gt_atTop (0:ℝ), eventually_ge_atTop (65536*(T:ℝ))]
      with d hs hr hd hlate
    exact ⟨hd, hs.1, hs.2.1, hs.2.2, hr, hlate⟩
  exact tendsto_natCast_atTop_atTop.eventually hall

/-- Complete unconditional construction of the actual retained groups and
both maximal support cutoffs, with all post-prefix effective supports and
captured/late thresholds. No abstract decomposition is an input. -/
theorem exists_constructed_cutoff_geometry {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (amp : ℝ) (ha : 0 < amp) (hcap : ∀ i, |u i| ≤ amp)
    (T : ℕ) (hT : 0 < T) (d : ℝ) (hd : 0 < d) (hlog : 0 < Real.log d)
    (hfloor : d/(16384*Real.log d) ≤ (⌊d/(8192*Real.log d)⌋₊ : ℝ))
    (hbudget : (⌊d/(8192*Real.log d)⌋₊ : ℝ) ≤ d/256) :
    ∃ (N : ℕ) (groups : List (List ℕ)) (p q : ℕ),
      0 < N ∧
      (∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u amp t) ∧
      (∀ t, N ≤ t → dyadicBin u amp t = ∅) ∧
      groups.flatten = dyadicRecordLevels u amp N ∧
      (∀ g ∈ groups, RegularRetainedGroup u amp T g) ∧
      groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card) ∧
      coefficientMass (u-retainedGroupVector u amp groups T) ≤
        8*(1/2:ℝ)^T*coefficientMass u ∧
      p ≤ q ∧
      SupportCutoff (dyadicGroupSize u amp groups T) groups.length
        (⌊d/(8192*Real.log d)⌋₊ : ℝ) p ∧
      SupportCutoff (dyadicGroupSize u amp groups T) groups.length (d/256) q ∧
      (∀ r, p ≤ r → r < groups.length →
        d/(65536*T*Real.log d) ≤ dyadicGroupScale u amp groups r ∧
        3*d/(2097152*T*Real.log d) ≤ dyadicGroupEffectiveSupport u amp groups T r) ∧
      (∀ r, r < q → dyadicGroupEffectiveSupport u amp groups T r ≤ d/4) ∧
      (∀ r, q ≤ r → r < groups.length → d/(1024*T) < dyadicGroupScale u amp groups r) := by
  obtain ⟨N, groups, hN, hcover, hempty, hflat, hreg, hchain, _, herr⟩ :=
    exists_global_dyadic_retention u amp ha hcap T hT
  obtain ⟨p, q, hpq, hp, hq, hpost, hcapt, hlate⟩ :=
    actual_sparse_span_cutoffs u amp groups T hT hreg hchain d hd hlog hfloor hbudget
  exact ⟨N, groups, p, q, hN, hcover, hempty, hflat, hreg, hchain, herr,
    hpq, hp, hq, hpost, hcapt, hlate⟩

end GaussianEllipsoidCandidate
