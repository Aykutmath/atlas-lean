import GaussianSelectedColumns
import SelectedCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Finset
open GaussianTensorMoments GaussianEllipsoid.CappedSimplex

namespace GaussianMixedNormHelpers

/-- Unconditional even-dimensional capped Gaussian determinant moment.
All selected-column law, general-position, Bartlett independence, Gamma
integration, capped extremization, and singular-value conventions are proved.
The only hypotheses are the explicit dimension and coefficient constraints. -/
theorem gaussian_capped_even_extended_moment
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r s : ℕ) (hr : 0 < r) (hrs : r = 2 * s)
    {w : κ → ℝ} (hw : w ∈ slice ((2 * (r : ℝ))⁻¹) 1) :
    extendedMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) s w ≤
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := by
  have hw' : w ∈ slice (((2 * r : ℕ) : ℝ)⁻¹) 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hw
  obtain ⟨T, hT⟩ := exists_card_subset_of_reciprocal_cap (by omega : 0 < 2 * r) hw'
  have hcard : Fintype.card T = r + 2 * s := by
    rw [Fintype.card_coe, hT]
    omega
  let e : Fin (r + 2 * s) ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  have he : Function.Injective (fun j : Fin (r + 2 * s) => (e j : κ)) :=
    Subtype.val_injective.comp e.injective
  have hlaw := gaussianColumns_map_selectedRows r (r + 2 * s) (fun j => (e j : κ)) he
  calc
    extendedMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) s w ≤
        extendedMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) s
          (fun k => if k ∈ T then (2 * (r : ℝ))⁻¹ else 0) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        extendedMoment_le_fixed_uniform_subset (gaussianProductLaw (Fin r)) s (2 * r)
          (by omega) hw' T hT
    _ ≤ ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) :=
      selected_uniform_extended_moment_le_of_map r s hr _ T e hlaw

/-- The same unconditional bound stated directly on the coefficient vector and
actual Gaussian expectation, with no internal law or moment predicates. -/
theorem gaussian_capped_even_inverse_det_moment
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r s : ℕ) (hr : 0 < r) (hrs : r = 2 * s)
    (z : κ → ℝ) (hzsum : ∑ k, z k ^ 2 = 1)
    (hzcap : ∀ k, z k ^ 2 ≤ (2 * (r : ℝ))⁻¹) :
    (∫⁻ g : κ → Fin r → ℝ,
      (ENNReal.ofReal (weightedGram g (fun k => z k ^ 2)).det ^ s)⁻¹
        ∂Measure.pi (fun _ : κ => gaussianProductLaw (Fin r))) ≤
      ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := by
  exact gaussian_capped_even_extended_moment r s hr hrs
    ⟨(fun k => ⟨sq_nonneg _, hzcap k⟩), hzsum⟩

end GaussianMixedNormHelpers
