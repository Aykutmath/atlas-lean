import CapturedGroupUnion
import ActualCapturedDeterministic

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module Finset GaussianEllipsoid
open GaussianEllipsoid.ProjectedClusters
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoidCandidate

/-- The literal original-sample projected-failure event is measurable. -/
theorem measurableSet_actualCapturedProjectionBad {n h : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T d p q : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup) :
    MeasurableSet (actualCapturedProjectionBad (h:=h) u amp ha groups T d p q hreg hflat) := by
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let E : Set (Fin n → Euclid h × Euclid h) :=
    {X | ∃ r ∈ Ico p q, X ∈ capturedGroupBad (d:=d) u amp ha groups T hreg hflat r}
  have hm : MeasurableSet E := by
    have hs : E = ⋃ r ∈ Ico p q, capturedGroupBad (h:=h) (d:=d) u amp ha groups T hreg hflat r := by
      ext X
      simp [E]
    rw [hs]
    exact MeasurableSet.iUnion (fun r => MeasurableSet.iUnion
      (fun _ => measurableSet_capturedGroupBad u amp ha groups T hreg hflat r))
  change MeasurableSet (permuteRows e ⁻¹' E)
  exact hm.preimage (permuteRows_preserving e h h).measurable

/-- The exact captured projection failure event used by the pathwise witness
assembly has the required unconditional original-sample probability bound. -/
theorem actualCapturedProjectionBad_probability {n h d : ℕ}
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
      (actualCapturedProjectionBad u amp ha groups T d p q hreg hflat) ≤
      (groups.length : ℝ) * Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log d)) := by
  let e := actualDyadicSupportPermutation u amp ha groups T hreg hflat
  let E : Set (Fin n → Euclid h × Euclid h) :=
    {X | ∃ r ∈ Ico p q, X ∈ capturedGroupBad (d:=d) u amp ha groups T hreg hflat r}
  have hm : MeasurableSet E := by
    have hs : E = ⋃ r ∈ Ico p q, capturedGroupBad (h:=h) (d:=d) u amp ha groups T hreg hflat r := by
      ext X
      simp [E]
    rw [hs]
    exact MeasurableSet.iUnion (fun r => MeasurableSet.iUnion
      (fun _ => measurableSet_capturedGroupBad u amp ha groups T hreg hflat r))
  change (gaussianBilinearSampleLaw (Fin n) h h).real (permuteRows e ⁻¹' E) ≤ _
  rw [(permuteRows_preserving e h h).measureReal_preimage hm.nullMeasurableSet]
  exact actual_captured_group_union_bound u amp ha groups T hT hreg hchain hflat p q
    hp hq hd hambient hfloor hnum

/-- Consumer endpoint at the precise even-half dimension. -/
theorem actualCapturedProjectionBad_probability_even {n d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ) (hT : 0 < T)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (p q : ℕ)
    (hp : SupportCutoff (dyadicGroupSize u amp groups T) groups.length
      (⌊(d:ℝ)/(8192*Real.log d)⌋₊ : ℝ) p)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (hd : 24 ≤ d)
    (hfloor : (d:ℝ)/(16384*Real.log d) ≤ (⌊(d:ℝ)/(8192*Real.log d)⌋₊ : ℝ))
    (hnum : 4096 ≤ 3*(d:ℝ)/(2097152*T*Real.log d)) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      (actualCapturedProjectionBad u amp ha groups T d p q hreg hflat) ≤
      (groups.length : ℝ) * Real.exp (-3*(d:ℝ)^2/(137438953472*T*Real.log d)) := by
  apply actualCapturedProjectionBad_probability u amp ha groups T hT hreg hchain hflat p q
    hp hq (by omega) ?_ hfloor hnum
  have hn : d ≤ 3 * (2 * (d/4)) := by omega
  have hR : (d:ℝ) ≤ 3 * ((2*(d/4) : ℕ):ℝ) := by exact_mod_cast hn
  linarith

alias actualCapturedProjectionBad_probability_le := actualCapturedProjectionBad_probability

end GaussianEllipsoidCandidate
