import GaussianCoordinateMarginal
import RadialInvariance
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open MeasureTheory ProbabilityTheory Module

namespace GaussianMixedNormHelpers
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The orthogonal direct-sum decomposition as an actual linear isometry. -/
def orthogonalSumIsometry (W : Submodule ℝ E) : WithLp 2 (W × Wᗮ) ≃ₗᵢ[ℝ] E where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (W × Wᗮ)).trans
    (W.prodEquivOfIsCompl Wᗮ W.isCompl_orthogonal)
  norm_map' z := by
    change ‖(z.fst : E) + (z.snd : E)‖ = ‖z‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simpa only [pow_two, Submodule.norm_coe] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (z.fst : E) (z.snd : E)
        (Submodule.inner_right_of_mem_orthogonal z.fst.property z.snd.property)

@[simp] theorem orthogonalSumIsometry_apply (W : Submodule ℝ E) (z : WithLp 2 (W × Wᗮ)) :
    orthogonalSumIsometry W z = (z.fst : E) + (z.snd : E) := rfl

@[simp] theorem projection_orthogonalSumIsometry (W : Submodule ℝ E)
    (z : WithLp 2 (W × Wᗮ)) :
    W.orthogonalProjection (orthogonalSumIsometry W z) = z.fst := by
  rw [orthogonalSumIsometry_apply, map_add,
    Submodule.orthogonalProjection_mem_subspace_eq_self,
    Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero z.snd.property,
    add_zero]

/-- Coordinates adapted to a fixed subspace and its orthogonal complement. No
choice of basis is made as a measurable function of varying subspaces. -/
def subspaceCoordinates (W : Submodule ℝ E) :
    E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W) ⊕ Fin (finrank ℝ Wᗮ)) :=
  (orthogonalSumIsometry W).symm.trans
    ((stdOrthonormalBasis ℝ W).prod (stdOrthonormalBasis ℝ Wᗮ)).repr

/-- Restricting adapted coordinates to the first block is exactly the
orthonormal-coordinate vector of the orthogonal projection. -/
theorem subspaceCoordinates_inl (W : Submodule ℝ E) (x : E) (i : Fin (finrank ℝ W)) :
    subspaceCoordinates W x (Sum.inl i) =
      (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x) i := by
  let z := (orthogonalSumIsometry W).symm x
  have hx : orthogonalSumIsometry W z = x := (orthogonalSumIsometry W).apply_symm_apply x
  rw [← hx]
  change ((stdOrthonormalBasis ℝ W).prod (stdOrthonormalBasis ℝ Wᗮ)).repr
    ((orthogonalSumIsometry W).symm (orthogonalSumIsometry W z)) (Sum.inl i) = _
  rw [LinearIsometryEquiv.symm_apply_apply, projection_orthogonalSumIsometry]
  simp [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.prod_apply,
    WithLp.prod_inner_apply]

/-- Full orthogonal invariance of the actual iid Euclidean Gaussian law,
proved by its Lebesgue density and Haar-preserving linear isometries. -/
theorem euclideanGaussianLaw_map_linearIsometryEquiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    Measure.map e (euclideanGaussianLaw ι) = euclideanGaussianLaw κ := by
  have hcard : Fintype.card ι = Fintype.card κ := by
    simpa only [finrank_euclideanSpace] using e.toLinearEquiv.finrank_eq
  have hconst : gaussianDensityConstant ι = gaussianDensityConstant κ := by
    simp only [gaussianDensityConstant, hcard]
  rw [euclideanGaussianLaw_eq_withDensity, euclideanGaussianLaw_eq_withDensity]
  simpa only [hconst] using GaussianProductDensity.radial_density_isometry e
    (fun t : ℝ => ENNReal.ofReal (gaussianDensityConstant ι * Real.exp (-(1 / 2 : ℝ) * t ^ 2)))
    (by fun_prop)

/-- Exact Gaussian law of orthonormal coordinates of a fixed-subspace projection. -/
theorem euclideanGaussianLaw_map_projection_coordinates
    {ι : Type*} [Fintype ι] (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Measure.map (fun x => (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x))
      (euclideanGaussianLaw ι) = euclideanGaussianLaw (Fin (finrank ℝ W)) := by
  let e := subspaceCoordinates W
  have heq : (fun x => (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x)) =
      euclideanCoordinateSubfamily (Sum.inl : Fin (finrank ℝ W) →
        Fin (finrank ℝ W) ⊕ Fin (finrank ℝ Wᗮ)) ∘ e := by
    funext x
    ext i
    simpa only [Function.comp_apply, euclideanCoordinateSubfamily_apply] using
      (subspaceCoordinates_inl W x i).symm
  rw [heq, ← Measure.map_map]
  · rw [euclideanGaussianLaw_map_linearIsometryEquiv]
    exact euclideanGaussianLaw_map_subfamily Sum.inl Sum.inl_injective
  · unfold euclideanCoordinateSubfamily
    exact (MeasurableEquiv.toLp 2 (_ → ℝ)).measurable.comp
      (measurable_pi_lambda _ (fun i =>
        (measurable_pi_apply (Sum.inl i)).comp (MeasurableEquiv.toLp 2 (_ → ℝ)).symm.measurable))
  · exact e.continuous.measurable

/-- The genuine fixed-subspace Gaussian projection law, represented in any
canonical finite orthonormal coordinates of the subspace. -/
theorem euclideanGaussianLaw_map_projection
    {ι : Type*} [Fintype ι] (W : Submodule ℝ (EuclideanSpace ℝ ι)) :
    Measure.map W.orthogonalProjection (euclideanGaussianLaw ι) =
      Measure.map (stdOrthonormalBasis ℝ W).repr.symm
        (euclideanGaussianLaw (Fin (finrank ℝ W))) := by
  letI : BorelSpace W := Subtype.borelSpace _
  have hm : Measurable (fun x => (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x)) :=
    (stdOrthonormalBasis ℝ W).repr.continuous.measurable.comp
      W.orthogonalProjection.continuous.measurable
  rw [← euclideanGaussianLaw_map_projection_coordinates W,
    Measure.map_map (stdOrthonormalBasis ℝ W).repr.symm.continuous.measurable hm]
  congr 1
  funext x
  exact ((stdOrthonormalBasis ℝ W).repr.symm_apply_apply _).symm

/-- Squared length of a fixed nonzero-dimensional orthogonal Gaussian projection
has the exact chi-square law. This is the substantive one-row Bartlett fibre law. -/
theorem euclideanGaussianLaw_map_projection_norm_sq
    {ι : Type*} [Fintype ι] (W : Submodule ℝ (EuclideanSpace ℝ ι))
    (hW : 0 < finrank ℝ W) :
    Measure.map (fun x => ‖W.orthogonalProjection x‖ ^ 2) (euclideanGaussianLaw ι) =
      gammaMeasure ((finrank ℝ W : ℝ) / 2) (1 / 2) := by
  letI : BorelSpace W := Subtype.borelSpace _
  letI : Nonempty (Fin (finrank ℝ W)) := Fin.pos_iff_nonempty.mp hW
  have heq : (fun x => ‖W.orthogonalProjection x‖ ^ 2) =
      (fun y : EuclideanSpace ℝ (Fin (finrank ℝ W)) => ‖y‖ ^ 2) ∘
        (fun x => (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x)) := by
    funext x
    simp only [Function.comp_apply, LinearIsometryEquiv.norm_map]
  have hm : Measurable (fun x => (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x)) :=
    (stdOrthonormalBasis ℝ W).repr.continuous.measurable.comp
      W.orthogonalProjection.continuous.measurable
  rw [heq, ← Measure.map_map (by fun_prop) hm,
    euclideanGaussianLaw_map_projection_coordinates]
  simpa only [Fintype.card_fin] using euclideanGaussianLaw_map_norm_sq (Fin (finrank ℝ W))

end GaussianMixedNormHelpers
