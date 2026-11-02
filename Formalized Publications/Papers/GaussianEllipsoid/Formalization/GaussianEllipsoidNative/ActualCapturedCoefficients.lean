import CanonicalProjectedPrefix
import ActualDyadicSupportPermutation
import ConstructedCutoffGeometry

noncomputable section
open MeasureTheory Module Finset
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- Literal squared energy on an actual retained group. -/
def dyadicGroupEnergy {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T r : ℕ) : ℝ :=
  ∑ i ∈ dyadicGroupSupport u amp groups T r, (u i)^2

/-- Positivity and regularity come from the actual retained group construction. -/
theorem actual_group_energy_mass_cap {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (r : ℕ) (hr : r < groups.length) :
    0 < dyadicGroupMass u amp groups T r ∧
    0 < dyadicGroupEnergy u amp groups T r ∧
    ∀ i ∈ dyadicGroupSupport u amp groups T r,
      |u i| ≤ 16 * dyadicGroupEnergy u amp groups T r / dyadicGroupMass u amp groups T r := by
  have hg : groups[r]?.getD [] ∈ groups := by
    simp only [List.getElem?_eq_getElem hr, Option.getD_some]
    exact List.getElem_mem hr
  obtain ⟨t, tail, heq, h⟩ := hreg _ hg
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, hm, hQ, _, _, _, hcap, _⟩
  dsimp only [dyadicGroupMass, dyadicGroupEnergy, dyadicGroupSupport]
  rw [heq]
  dsimp only [List.headD_cons, List.tail_cons]
  exact ⟨hm, hQ, fun i hi => (hcap i hi).2.1⟩

theorem regular_cap_sqrt_form {m Q : ℝ} (hm : 0 < m) (hQ : 0 < Q) :
    16 * Q / m = 16 * Real.sqrt Q / Real.sqrt (m^2/Q) := by
  rw [Real.sqrt_div (sq_nonneg m), Real.sqrt_sq hm.le]
  have hs : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hQ)
  field_simp
  nlinarith [Real.sq_sqrt hQ.le]

end GaussianEllipsoid.ProjectedClusters
