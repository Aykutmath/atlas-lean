import Section_10_Zonoid.Cor101.ZonotopeExtrusion
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The extrusion formula in an arbitrary direction

This transports `Zonotope.volume_extrusion` through genuine orthogonal,
measure-preserving coordinates. The coordinate construction is adapted from
`OAI/Geometry/ProjectionBodies/ShadowSlices.lean` in the public OpenAI math
repository:
https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Geometry/ProjectionBodies/ShadowSlices.lean
It is generalized here to an arbitrary finite-dimensional inner product space
and to the non-centered segment `[0,c • u]`.
-/

open MeasureTheory Set Function
open scoped ENNReal RealInnerProductSpace Pointwise

noncomputable section

namespace Cor101
namespace Zonotope

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal complement of one vector. -/
abbrev perpendicular (u : E) := (ℝ ∙ u)ᗮ

lemma perpendicular_inner (u : E) (z : perpendicular u) : ⟪u, (z : E)⟫ = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.property

/-- Linear reconstruction from an orthogonal component and a scalar coordinate. -/
def axialCoordLinear (u : E) : WithLp 2 (perpendicular u × ℝ) →ₗ[ℝ] E where
  toFun z := (WithLp.ofLp z).1 + (WithLp.ofLp z).2 • u
  map_add' z w := by
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' a z := by
    simp only [WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul_of_tower,
      smul_eq_mul, smul_add, smul_smul, RingHom.id_apply]

lemma axialCoordLinear_inner (u : E) (hu : ‖u‖ = 1)
    (z w : WithLp 2 (perpendicular u × ℝ)) :
    ⟪axialCoordLinear u z, axialCoordLinear u w⟫ = ⟪z, w⟫ := by
  change ⟪((WithLp.ofLp z).1 : E) + (WithLp.ofLp z).2 • u,
    ((WithLp.ofLp w).1 : E) + (WithLp.ofLp w).2 • u⟫ = _
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, hu, one_pow, mul_one,
    perpendicular_inner, Submodule.mem_orthogonal_singleton_iff_inner_left.mp (WithLp.ofLp z).1.property]
  simp only [mul_zero, add_zero, zero_add, WithLp.prod_inner_apply, Submodule.coe_inner,
    Real.inner_apply]
  ring

lemma axialCoordLinear_surjective (u : E) (hu : ‖u‖ = 1) :
    Surjective (axialCoordLinear u) := by
  intro x
  have hz : x - ⟪u, x⟫ • u ∈ perpendicular u := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu,
      one_pow, mul_one, sub_self]
  refine ⟨WithLp.toLp 2 (⟨_, hz⟩, ⟪u, x⟫), ?_⟩
  change x - _ + _ = x
  exact sub_add_cancel _ _

/-- A unit axial direction supplies isometric orthogonal coordinates. -/
def axialCoords (u : E) (hu : ‖u‖ = 1) :
    WithLp 2 (perpendicular u × ℝ) ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective
    (LinearMap.isometryOfInner (axialCoordLinear u) (axialCoordLinear_inner u hu))
    (axialCoordLinear_surjective u hu)

lemma axialCoords_apply (u : E) (hu : ‖u‖ = 1) (z : perpendicular u) (t : ℝ) :
    axialCoords u hu (WithLp.toLp 2 (z, t)) = z + t • u := rfl

lemma axialCoords_projection (u : E) (hu : ‖u‖ = 1) (z : perpendicular u) (t : ℝ) :
    (perpendicular u).orthogonalProjectionOnto (axialCoords u hu (WithLp.toLp 2 (z, t))) = z := by
  rw [axialCoords_apply, map_add, map_smul,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
    smul_zero, add_zero]

/-- The continuous linear change from product coordinates into the ambient space. -/
def axialContinuousEquiv (u : E) (hu : ‖u‖ = 1) :
    (perpendicular u × ℝ) ≃L[ℝ] E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (perpendicular u) ℝ).symm.trans
    (axialCoords u hu).toContinuousLinearEquiv

lemma axialContinuousEquiv_apply (u : E) (hu : ‖u‖ = 1) (z : perpendicular u × ℝ) :
    axialContinuousEquiv u hu z = z.1 + z.2 • u := rfl

lemma axial_preimage_projection (u : E) (hu : ‖u‖ = 1) (K : Set E) :
    Prod.fst '' (axialContinuousEquiv u hu ⁻¹' K) =
      (perpendicular u).orthogonalProjectionOnto '' K := by
  ext z
  constructor
  · rintro ⟨⟨w, t⟩, hw, rfl⟩
    exact ⟨axialContinuousEquiv u hu (w, t), hw, axialCoords_projection u hu w t⟩
  · rintro ⟨x, hx, rfl⟩
    let q := (axialContinuousEquiv u hu).symm x
    have hq : axialContinuousEquiv u hu q = x := (axialContinuousEquiv u hu).apply_symm_apply x
    refine ⟨q, ?_, ?_⟩
    · change axialContinuousEquiv u hu q ∈ K
      rwa [hq]
    · rw [← hq]
      exact (axialCoords_projection u hu q.1 q.2).symm

lemma axial_preimage_add_segment (u : E) (hu : ‖u‖ = 1) (K : Set E) (c : ℝ) :
    axialContinuousEquiv u hu ⁻¹' (K + segment ℝ 0 (c • u)) =
      (axialContinuousEquiv u hu ⁻¹' K) +
        segment ℝ (0 : perpendicular u × ℝ) (0, c) := by
  let e := axialContinuousEquiv u hu
  have hseg : e '' segment ℝ (0 : perpendicular u × ℝ) (0, c) =
      segment ℝ 0 (c • u) := by
    simpa [e, axialContinuousEquiv_apply] using
      image_segment ℝ e.toLinearMap.toAffineMap (0 : perpendicular u × ℝ) (0, c)
  rw [← hseg]
  ext z
  constructor
  · rintro ⟨x, hx, _, ⟨a, ha, rfl⟩, he⟩
    refine ⟨e.symm x, by simpa [e] using hx, a, ha, ?_⟩
    apply e.injective
    simpa only [map_add, ContinuousLinearEquiv.apply_symm_apply] using he
  · rintro ⟨x, hx, a, ha, rfl⟩
    change e (x + a) ∈ K + e '' segment ℝ (0 : perpendicular u × ℝ) (0, c)
    rw [map_add]
    exact add_mem_add hx (mem_image_of_mem _ ha)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The same coordinates as a measure-preserving measurable equivalence. -/
def axialMeasurableEquiv (u : E) (hu : ‖u‖ = 1) :
    (perpendicular u × ℝ) ≃ᵐ E :=
  (MeasurableEquiv.toLp 2 _).trans (axialCoords u hu).toMeasurableEquiv

lemma axialMeasurableEquiv_measurePreserving (u : E) (hu : ‖u‖ = 1) :
    MeasurePreserving (axialMeasurableEquiv u hu) :=
  (WithLp.volume_preserving_toLp _ _).trans (axialCoords u hu).measurePreserving

/-- Adding a segment along a unit vector increases ordinary Euclidean volume
by the length times the ordinary volume of its orthogonal projection. -/
theorem volume_add_segment_of_unit (u : E) (hu : ‖u‖ = 1) {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) {c : ℝ} (hc : 0 ≤ c) :
    volume (K + segment ℝ 0 (c • u)) = volume K +
      ENNReal.ofReal c * volume ((perpendicular u).orthogonalProjectionOnto '' K) := by
  let e := axialContinuousEquiv u hu
  have hC : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hcv : Convex ℝ (e ⁻¹' K) := hconv.linear_preimage e.toLinearMap
  have h := volume_add_vertical_segment hC hcv hc
  rw [← axial_preimage_add_segment u hu K c, axial_preimage_projection] at h
  have hm := axialMeasurableEquiv_measurePreserving u hu
  have hm' (B : Set E) (hB : MeasurableSet B) : volume (e ⁻¹' B) = volume B :=
    hm.measure_preimage hB.nullMeasurableSet
  have hseg : IsCompact (segment ℝ (0 : E) (c • u)) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  rw [hm' _ (hK.add hseg).measurableSet,
    hm' _ hK.measurableSet] at h
  exact h

/-- Normalizing a nonzero generator gives an arbitrary-direction extrusion
formula without any full-dimensionality or nondegeneracy assumption on `K`. -/
theorem volume_add_segment (v : E) (hv : v ≠ 0) {K : Set E}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    volume (K + segment ℝ 0 v) = volume K +
      ENNReal.ofReal ‖v‖ *
        volume ((perpendicular (‖v‖⁻¹ • v)).orthogonalProjectionOnto '' K) := by
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul, hv]
  have hvnorm : ‖v‖ • (‖v‖⁻¹ • v) = v := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]
  simpa only [hvnorm] using volume_add_segment_of_unit (‖v‖⁻¹ • v) hu hK hconv (norm_nonneg v)

end Zonotope
end Cor101
