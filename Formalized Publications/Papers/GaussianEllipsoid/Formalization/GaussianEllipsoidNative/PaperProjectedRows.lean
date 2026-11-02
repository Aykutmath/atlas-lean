import ProjectedGaussianLaw
import CoordinateBlockPinching
import UCRetainedFrames
import UCNormalizedRows

noncomputable section
open MeasureTheory Module GaussianTensorMoments GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperProjectedRows
open ProjectedClusters

/-- Literal coordinate restriction to a deterministically enumerated retained set. -/
def restrictRows {n m : ℕ} (e : Fin m ↪ Fin n) : Euclid n →L[ℝ] Euclid m :=
  (coordinateEmbedding e).adjoint

@[simp] theorem restrictRows_apply {n m : ℕ} (e : Fin m ↪ Fin n)
    (x : Euclid n) (j : Fin m) : restrictRows e x j = x (e j) :=
  coordinateEmbedding_adjoint_apply e x j

/-- This is precisely L_J={v_J:v∈L}, not an intersection in the ambient coordinates. -/
def retainedNuisance {n m : ℕ} (e : Fin m ↪ Fin n) (L : Submodule ℝ (Euclid n)) :
    Submodule ℝ (Euclid m) := L.map (restrictRows e).toLinearMap

theorem mem_retainedNuisance_iff {n m : ℕ} (e : Fin m ↪ Fin n)
    (L : Submodule ℝ (Euclid n)) (x : Euclid m) :
    x ∈ retainedNuisance e L ↔ ∃ v ∈ L, ∀ j, v (e j)=x j := by
  constructor
  · rintro ⟨v,hv,hvx⟩
    refine ⟨v,hv,?_⟩
    intro j
    have hh := congrArg (fun y : Euclid m => y j) hvx
    change restrictRows e v j=x j at hh
    simpa only [restrictRows_apply] using hh
  · rintro ⟨v,hv,hvx⟩
    refine ⟨v,hv,?_⟩
    ext j
    change restrictRows e v j=x j
    simpa only [restrictRows_apply] using hvx j

theorem retainedNuisance_finrank_le {n m : ℕ} (e : Fin m ↪ Fin n)
    (L : Submodule ℝ (Euclid n)) : finrank ℝ (retainedNuisance e L) ≤ finrank ℝ L :=
  Submodule.finrank_map_le _ _

/-- Orthonormal rows spanning the full retained nuisance complement have exactly the paper rank. -/
theorem projected_rank {n m r : ℕ} (e : Fin m ↪ Fin n) (L : Submodule ℝ (Euclid n))
    (U : Euclid r →ₗᵢ[ℝ] Euclid m)
    (hU : LinearMap.range U.toLinearMap=(retainedNuisance e L)ᗮ) :
    r=m-finrank ℝ (retainedNuisance e L) ∧ m-finrank ℝ L ≤ r := by
  have hdim := (retainedNuisance e L).finrank_add_finrank_orthogonal
  have hr : finrank ℝ ((retainedNuisance e L)ᗮ)=r := by
    rw [← hU]
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      (LinearMap.finrank_range_of_inj U.injective)
  have hm : finrank ℝ (Euclid m)=m := by simp [Euclid]
  rw [hr,hm] at hdim
  have hle := retainedNuisance_finrank_le e L
  omega

def rowProjection {n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) : Euclid n →L[ℝ] Euclid r :=
  U.toContinuousLinearMap.adjoint ∘L restrictRows e

theorem rowProjection_coisometry {n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) :
    rowProjection e U ∘L (rowProjection e U).adjoint=ContinuousLinearMap.id ℝ _ := by
  unfold rowProjection restrictRows
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_adjoint]
  calc
    _ = U.toContinuousLinearMap.adjoint ∘L
        ((coordinateEmbedding e).adjoint ∘L coordinateEmbedding e) ∘L U.toContinuousLinearMap := by
      simp only [ContinuousLinearMap.comp_assoc]
    _ = _ := by
      rw [coordinateEmbedding_adjoint_comp]
      simp only [ContinuousLinearMap.comp_id,ContinuousLinearMap.id_comp,LinearIsometry.adjoint_comp_self]
      rfl

/-- Exact iid array law, in any finite-dimensional isonormal test-coordinate space.
In particular this includes symmetric-matrix coordinates and the r=0 endpoint. -/
theorem projected_coordinates_preserving {n m r : ℕ} (q : ℕ) (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) :
    MeasurePreserving (transformEntries q (rowProjection e U))
      (gaussianProductLaw (Fin q × Fin n)) (gaussianProductLaw (Fin q × Fin r)) :=
  transformEntries_preserving q (rowProjection e U) (rowProjection_coisometry e U)

/-- Source row weights of U_J in the chosen retained-row ordering. -/
def rowWeight {m r : ℕ} (U : Euclid r →ₗᵢ[ℝ] Euclid m) (i : Fin r) (j : Fin m) : ℝ :=
  U (EuclideanSpace.single i (1:ℝ)) j

theorem rowProjection_apply {n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) (x : Euclid n) (i : Fin r) :
    rowProjection e U x i = ∑ j, rowWeight U i j*x (e j) := by
  have hh := ContinuousLinearMap.adjoint_inner_right U.toContinuousLinearMap
    (EuclideanSpace.single i (1:ℝ)) (restrictRows e x)
  simpa [rowProjection,rowWeight,PiLp.inner_apply,RCLike.inner_apply,
    EuclideanSpace.single_apply,mul_comm] using hh

/-- A source Gaussian row, realized by independent full matrix entries. Restricting
its tests to symmetric matrices is the canonical Frobenius-isonormal realization. -/
def gaussianRows (p n : ℕ) (x : GaussianEntries (p*p) n) (i : Fin n) (A : Square p) : ℝ :=
  UCNormalizedRows.gaussianRow A (fun a => x (a,i))

/-- Explicit representation bridge: row projection is literally the displayed sum U_J G_J
on every matrix test, and therefore on every symmetric matrix test. -/
theorem projected_gaussianRows_eq {n m r p : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) (x : GaussianEntries (p*p) n)
    (i : Fin r) (A : Square p) :
    gaussianRows p r (transformEntries (p*p) (rowProjection e U) x) i A =
      ∑ j, rowWeight U i j * gaussianRows p n x (e j) A := by
  unfold gaussianRows UCNormalizedRows.gaussianRow
  change (∑ a, A (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2 *
    (rowProjection e U (entriesToRows (p*p) n x a)) i) = _
  simp_rw [rowProjection_apply]
  simp only [entriesToRows,MeasurableEquiv.toLp_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Paper-facing projected-row law and exact retained rank, in the explicit isonormal
coordinate realization bridged above. No stochastic covariance or independence premise is added. -/
theorem paper_projected_rows {n m r p : ℕ} (e : Fin m ↪ Fin n)
    (L : Submodule ℝ (Euclid n)) (U : Euclid r →ₗᵢ[ℝ] Euclid m)
    (hU : LinearMap.range U.toLinearMap=(retainedNuisance e L)ᗮ) :
    r=m-finrank ℝ (retainedNuisance e L) ∧ m-finrank ℝ L ≤ r ∧
    MeasurePreserving (transformEntries (p*p) (rowProjection e U))
      (gaussianProductLaw (Fin (p*p) × Fin n)) (gaussianProductLaw (Fin (p*p) × Fin r)) :=
  ⟨(projected_rank e L U hU).1,(projected_rank e L U hU).2,projected_coordinates_preserving (p*p) e U⟩

#print axioms paper_projected_rows
#print axioms projected_gaussianRows_eq
end GaussianEllipsoid.PaperProjectedRows
