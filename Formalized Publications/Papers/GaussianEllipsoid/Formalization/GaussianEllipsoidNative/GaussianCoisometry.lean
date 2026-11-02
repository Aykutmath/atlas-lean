import OrthogonalGaussianProjection
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open MeasureTheory Module
open GaussianMixedNormHelpers
open scoped InnerProductSpace

namespace GaussianEllipsoid.SmallBall
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- A rectangular coisometry takes an actual standard Gaussian to a standard
Gaussian of the target dimension. The proof uses a genuine fixed-subspace
projection law and orthogonal invariance, not an assumed covariance principle. -/
theorem euclideanGaussianLaw_map_coisometry
    (Q : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι)
    (hQ : Q ∘L ContinuousLinearMap.adjoint Q = ContinuousLinearMap.id ℝ _) :
    (euclideanGaussianLaw κ).map Q = euclideanGaussianLaw ι := by
  let J := ContinuousLinearMap.adjoint Q
  have hQapply : ∀ y, Q (J y) = y := by
    intro y
    exact congrArg (fun f : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => f y) hQ
  have hinner : ∀ x y : EuclideanSpace ℝ ι, ⟪J x, J y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    change ⟪ContinuousLinearMap.adjoint Q x, J y⟫_ℝ = _
    rw [ContinuousLinearMap.adjoint_inner_left, hQapply]
  let jiso : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
    J.toLinearMap.isometryOfInner hinner
  let W : Submodule ℝ (EuclideanSpace ℝ κ) := LinearMap.range J.toLinearMap
  letI : BorelSpace W := Subtype.borelSpace _
  let eL : EuclideanSpace ℝ ι ≃ₗ[ℝ] W :=
    LinearEquiv.ofInjective J.toLinearMap jiso.injective
  let e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] W := eL.isometryOfInner (by
    intro x y
    change ⟪J x, J y⟫_ℝ = ⟪x, y⟫_ℝ
    exact hinner x y)
  have hproj : ∀ x : EuclideanSpace ℝ κ, W.orthogonalProjection x = e (Q x) := by
    intro x
    apply Subtype.ext
    change (W.orthogonalProjection x : EuclideanSpace ℝ κ) = J (Q x)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨Q x, rfl⟩
    · intro v hv
      obtain ⟨y, rfl⟩ := hv
      change ⟪x - ContinuousLinearMap.adjoint Q (Q x), ContinuousLinearMap.adjoint Q y⟫_ℝ = 0
      rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_right,
        ContinuousLinearMap.adjoint_inner_left, hQapply, sub_self]
  let eout : EuclideanSpace ℝ (Fin (finrank ℝ W)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
    (stdOrthonormalBasis ℝ W).repr.symm.trans e.symm
  let coords : EuclideanSpace ℝ κ → EuclideanSpace ℝ (Fin (finrank ℝ W)) :=
    fun x => (stdOrthonormalBasis ℝ W).repr (W.orthogonalProjection x)
  have hcoords : Measurable coords :=
    (stdOrthonormalBasis ℝ W).repr.continuous.measurable.comp
      W.orthogonalProjection.continuous.measurable
  have hfactor : (fun x => Q x) = eout ∘ coords := by
    funext x
    simp only [Function.comp_apply, eout, LinearIsometryEquiv.trans_apply, coords,
      LinearIsometryEquiv.symm_apply_apply, hproj]
  change Measure.map (fun x => Q x) (euclideanGaussianLaw κ) = _
  rw [hfactor, ← Measure.map_map eout.continuous.measurable hcoords]
  rw [euclideanGaussianLaw_map_projection_coordinates W]
  exact euclideanGaussianLaw_map_linearIsometryEquiv eout

end GaussianEllipsoid.SmallBall

#print axioms GaussianEllipsoid.SmallBall.euclideanGaussianLaw_map_coisometry
