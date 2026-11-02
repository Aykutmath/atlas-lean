import AHHSphereEuclideanGeometry
import LipschitzSmoothApproximationSupport

/-! Smooth sharp-Lipschitz ambient approximants to the actual square-root
covariance observable on the product of spheres. This addresses the operator
norm's nonsmoothness without asserting any Gaussian or sphere entropy bound.
Radial normalization and its singularities are not handled by this module. -/
noncomputable section
open MeasureTheory GaussianMixedNormHelpers
open scoped ContDiff Topology
namespace AHHRadial

/-- The actual root observable admits a bounded ambient extension with the
same sharp Lipschitz constant. Bounds are retained by clipping the extension. -/
theorem exists_bounded_root_extension (n h : ℕ) (hn : 0 < n) :
    ∃ g : SphereAmbient n h → ℝ, LipschitzWith 1 g ∧
      (∀ z, 1 ≤ g z) ∧ (∀ z, g z ≤ Real.sqrt n) ∧
      ∀ d : Directions n h,
        g (directionsToEuclidean n h d).val = Real.sqrt (unitCovarianceNorm n h d) := by
  classical
  let S : Set (SphereAmbient n h) := {z | ∀ j, ‖z j‖ = 1}
  let f : SphereAmbient n h → ℝ := fun z =>
    if hz : z ∈ S then
      Real.sqrt (unitCovarianceNorm n h (euclideanToDirections n h ⟨z, hz⟩)) else 1
  have hfl : LipschitzOnWith 1 f S := by
    intro x hx y hy
    have hh := lipschitzWith_sqrt_unitCovarianceNorm_euclidean n h ⟨x, hx⟩ ⟨y, hy⟩
    simpa only [f, dif_pos hx, dif_pos hy, Subtype.edist_eq] using hh
  obtain ⟨G, hG, hGeq⟩ := hfl.extend_real
  have hn1 : 1 ≤ Real.sqrt (n : ℝ) := by
    have hh : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hh
  refine ⟨fun z => max 1 (min (G z) (Real.sqrt n)),
    (hG.min_const _).const_max _, fun z => le_max_left _ _, ?_, ?_⟩
  · intro z
    exact max_le hn1 (min_le_right _ _)
  · intro d
    have hd : (directionsToEuclidean n h d).val ∈ S :=
      (directionsToEuclidean n h d).property
    have he : G (directionsToEuclidean n h d).val =
        Real.sqrt (unitCovarianceNorm n h d) := by
      rw [← hGeq hd]
      simp only [f, dif_pos hd]
      change Real.sqrt (unitCovarianceNorm n h
        (euclideanToDirections n h (directionsToEuclidean n h d))) = _
      rw [euclideanToDirections_directionsToEuclidean]
    dsimp only
    rw [he, min_eq_left (Real.sqrt_le_sqrt (unitCovarianceNorm_le n h d))]
    apply max_eq_right
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt (one_le_unitCovarianceNorm n h hn d)

/-- Uniformly close smooth ambient approximants, still bounded below by one
and still exactly one-Lipschitz. No derivative-energy approximation premise is
assumed: the Lipschitz estimate follows from positive convolution. -/
theorem exists_smooth_root_approximation (n h : ℕ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SphereAmbient n h → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith 1 g ∧
      (∀ z, 1 ≤ g z) ∧ (∀ z, g z ≤ Real.sqrt n) ∧
      (∀ d : Directions n h,
        |g (directionsToEuclidean n h d).val -
          Real.sqrt (unitCovarianceNorm n h d)| ≤ ε) ∧
      ∀ z, ‖fderiv ℝ g z‖ ≤ 1 := by
  obtain ⟨G, hl, hlo, hhi, heq⟩ := exists_bounded_root_extension n h hn
  have hl' : LipschitzWith 1 (fun z => G z - 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using hl.dist_le_mul x y
  obtain ⟨g, hc, hg, hgl, hgu, hge⟩ :=
    LipschitzSmoothApproximationSupport.exists_smooth_bounded (μ := volume)
      hl' (fun z => sub_nonneg.mpr (hlo z))
      (fun z => sub_le_sub_right (hhi z) 1) hε
  have hglip : LipschitzWith 1 (fun z => g z + 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul x y
  refine ⟨fun z => g z + 1, hc.add contDiff_const, hglip,
    ?_, ?_, ?_, ?_⟩
  · intro z
    linarith [hgl z]
  · intro z
    linarith [hgu z]
  · intro d
    have hh := hge (directionsToEuclidean n h d).val
    rw [Real.dist_eq, heq] at hh
    convert hh using 1
    congr 1
    ring
  · intro z
    exact norm_fderiv_le_of_lipschitz ℝ hglip

#print axioms exists_bounded_root_extension
#print axioms exists_smooth_root_approximation
end AHHRadial
