import ActualCapturedCoefficients
import ActualDyadicPermutationStats

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module Finset
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- The actual ordered retained coefficient vector, before d^(-1/2) scaling. -/
def orderedRetainedCoefficients {n : ℕ} (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup) :
    Fin n → ℝ :=
  permuteRows (actualDyadicSupportPermutation u amp ha groups T hreg hflat)
    (retainedGroupVector u amp groups T)

/-- The projected-prefix probability of an actual dyadic group, with its
energy, mass, coefficient cap and support all derived from that group. -/
theorem actual_captured_group_smallball {n h d : ℕ}
    (u : Fin n → ℝ) (amp : ℝ) (ha : 0 ≤ amp) (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g) (hflat : groups.flatten.Nodup)
    (r : ℕ) (hr : r < groups.length) (hh : 0 < h)
    (hbudget : (d : ℝ)/4 + supportCut (dyadicGroupSupport u amp groups T) r ≤ h)
    (hR : 4096 ≤ dyadicGroupEffectiveSupport u amp groups T r)
    (hRd : dyadicGroupEffectiveSupport u amp groups T r ≤ d) :
    (gaussianBilinearSampleLaw (Fin n) h h).real
      {X | spectralNuclearNorm (operatorFrobenius
        (projectedPrefixBlock (fun i => orderedRetainedCoefficients u amp ha groups T hreg hflat i /
          Real.sqrt d) X (supportCut (dyadicGroupSupport u amp groups T) r)
          (supportCut (dyadicGroupSupport u amp groups T) (r+1)))) <
          projectedConstant * Real.sqrt d * dyadicGroupMass u amp groups T r} ≤
      Real.exp (-(d : ℝ)*dyadicGroupEffectiveSupport u amp groups T r/65536) := by
  let G := dyadicGroupSupport u amp groups T
  let V := orderedRetainedCoefficients u amp ha groups T hreg hflat
  have hdG := actual_group_supports_pairwise u amp ha groups T hreg hflat groups.length le_rfl
  have hKL := supportCut_mono G (Nat.le_succ r)
  have hL := supportCut_le_ambient G hdG (r+1) (by omega)
  have hstat := actualDyadicSupportPermutation_interval_stats u amp ha groups T hreg hflat r hr
  have hpos := actual_group_energy_mass_cap u amp groups T hreg r hr
  let Q := dyadicGroupEnergy u amp groups T r
  have hQ : 0 < Q := hpos.2.1
  have hmass : dyadicGroupMass u amp groups T r =
      ∑ i, |intervalCoefficients V (supportCut G r) (supportCut G (r+1)) i| := by
    simpa [intervalCoefficients, supportInterval, sum_filter, apply_ite abs, V,
      orderedRetainedCoefficients, G] using hstat.1.symm
  have henergy : (∑ i, (intervalCoefficients V (supportCut G r) (supportCut G (r+1)) i)^2) =
      (Real.sqrt Q)^2 := by
    rw [Real.sq_sqrt hQ.le]
    simpa [intervalCoefficients, supportInterval, sum_filter, V,
      orderedRetainedCoefficients, G, Q, dyadicGroupEnergy] using hstat.2
  have hRdef : dyadicGroupEffectiveSupport u amp groups T r =
      (dyadicGroupMass u amp groups T r)^2 / (Real.sqrt Q)^2 := by
    rw [Real.sq_sqrt hQ.le]
    rfl
  have hcap : ∀ i, |intervalCoefficients V (supportCut G r) (supportCut G (r+1)) i| ≤
      16 * Real.sqrt Q / Real.sqrt (dyadicGroupEffectiveSupport u amp groups T r) := by
    intro i
    change _ ≤ 16 * Real.sqrt Q / Real.sqrt ((dyadicGroupMass u amp groups T r)^2/Q)
    rw [← regular_cap_sqrt_form hpos.1 hQ]
    exact actualDyadicSupportPermutation_interval_cap u amp ha groups T hreg hflat r hr i
  exact canonical_projected_prefix_smallball hKL hL hh hbudget V
    (Real.sqrt_pos.mpr hQ) henergy hmass hRdef hR hRd hcap

end GaussianEllipsoid.ProjectedClusters
