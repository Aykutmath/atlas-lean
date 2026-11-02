import PaperProjectedRows
import GaussianSelectedColumns
import UCUniformContinuity
import BMFullEntryWidth
import UCProjectedNorm
import UCNormalizedRows
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Basic

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Module GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.UCContinuityGeometry BMGeometry
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperIsonormal

local instance {p : ℕ} : InnerProductSpace ℝ (FrobeniusMatrix p p) :=
  PiLp.innerProductSpace (fun _ : Fin p => EuclideanSpace ℝ (Fin p))
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) :=
  Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) :=
  Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : SeminormedAddCommGroup (EuclideanSpace ℝ (Fin p × Fin p)) :=
  (inferInstance : NormedAddCommGroup (EuclideanSpace ℝ (Fin p × Fin p))).toSeminormedAddCommGroup



local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) :=
  Submodule.innerProductSpace (symmetricFrobenius p)

/-- Orthogonal projection of an actual standard Gaussian onto an isometric
finite-dimensional real Hilbert subspace is standard Gaussian on that subspace. -/
theorem stdGaussian_adjoint_isometry_general
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (U : F →ₗᵢ[ℝ] E) :
    (stdGaussian E).map U.toContinuousLinearMap.adjoint = stdGaussian F := by
  let L := U.toContinuousLinearMap.adjoint
  haveI : IsGaussian ((stdGaussian E).map L) := isGaussian_map L
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian,integral_id_stdGaussian,map_zero]
  · ext x y
    rw [covarianceBilin_map (IsGaussian.memLp_id _ 2 (by norm_num)),
      covarianceBilin_stdGaussian,covarianceBilin_stdGaussian]
    simp only [L,ContinuousLinearMap.adjoint_adjoint,innerSL_apply_apply]
    exact U.inner_map_map x y

section Projection
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
def isoAdjoint (U : F →ₗᵢ[ℝ] E) : E →L[ℝ] F := U.toContinuousLinearMap.adjoint
theorem isoAdjoint_inner (U : F →ₗᵢ[ℝ] E) (x : F) (y : E) :
    ⟪isoAdjoint U y,x⟫_ℝ = ⟪y,U x⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left U.toContinuousLinearMap x y
theorem isoAdjoint_inner_right (U : F →ₗᵢ[ℝ] E) (x : F) (y : E) :
    ⟪x,isoAdjoint U y⟫_ℝ = ⟪U x,y⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_right U.toContinuousLinearMap x y
end Projection

/-- Inclusion of symmetric matrices into all independent entry coordinates
is an isometry for the actual Frobenius norm. -/
def symmetricEntryIsometry (p : ℕ) : SymFrob p →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin p × Fin p) :=
  (frobeniusEquivEuclidean p p).toLinearIsometry.comp (symmetricFrobenius p).subtypeₗᵢ

def fullEntryEuclid (p : ℕ) (z : Fin (p*p) → ℝ) : EuclideanSpace ℝ (Fin p × Fin p) :=
  (MeasurableEquiv.toLp 2 ((Fin p × Fin p) → ℝ)) (fun a => z (finProdFinEquiv a))

theorem fullEntryEuclid_preserving (p : ℕ) :
    MeasurePreserving (fullEntryEuclid p) (gaussianProductLaw (Fin (p*p)))
      (stdGaussian (EuclideanSpace ℝ (Fin p × Fin p))) := by
  have hcoord : MeasurePreserving
      (fun z : Fin (p*p) → ℝ => fun a : Fin p × Fin p => z (finProdFinEquiv a))
      (gaussianProductLaw (Fin (p*p))) (gaussianProductLaw (Fin p × Fin p)) :=
    ⟨by fun_prop,gaussianProductLaw_map_subfamily _ finProdFinEquiv.injective⟩
  have hLp : MeasurePreserving (MeasurableEquiv.toLp 2 ((Fin p × Fin p) → ℝ))
      (gaussianProductLaw (Fin p × Fin p)) (stdGaussian (EuclideanSpace ℝ (Fin p × Fin p))) :=
    ⟨(MeasurableEquiv.toLp 2 ((Fin p × Fin p) → ℝ)).measurable,map_pi_eq_stdGaussian⟩
  exact hLp.comp hcoord

/-- Literal full-entry symmetrization: diagonal entries are unchanged and
an off-diagonal entry is the average of its two independent source entries. -/
def symmetrizedFullEntry (p : ℕ) (z : Fin (p*p) → ℝ) : SymFrob p :=
  ⟨symmetricFrobLM p ((frobeniusEquivEuclidean p p).symm (fullEntryEuclid p z)), by
    exact isotropicSymmetricOp_symmetric p (fullEntryEuclid p z)⟩

theorem symmetrizedFullEntry_eq_adjoint (p : ℕ) (z : Fin (p*p) → ℝ) :
    symmetrizedFullEntry p z =
      (isoAdjoint (symmetricEntryIsometry p)) (fullEntryEuclid p z) := by
  apply ext_inner_right ℝ
  intro A
  have hp := symmetrization_pairing
    ((frobeniusEquivEuclidean p p).symm (fullEntryEuclid p z))
    (frobeniusOperator A.val) A.property
  rw [operatorFrobenius_frobeniusOperator] at hp
  calc
    ⟪symmetrizedFullEntry p z,A⟫_ℝ =
      ⟪(frobeniusEquivEuclidean p p).symm (fullEntryEuclid p z),A.val⟫_ℝ := hp
    _ = ⟪fullEntryEuclid p z,symmetricEntryIsometry p A⟫_ℝ := by
      change ⟪(frobeniusEquivEuclidean p p).symm (fullEntryEuclid p z),A.val⟫_ℝ =
        ⟪fullEntryEuclid p z,(frobeniusEquivEuclidean p p) A.val⟫_ℝ
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        ((frobeniusEquivEuclidean p p).inner_map_map
          ((frobeniusEquivEuclidean p p).symm (fullEntryEuclid p z)) A.val).symm
    _ = _ := (isoAdjoint_inner (symmetricEntryIsometry p) A (fullEntryEuclid p z)).symm

/-- The actual independent full-entry construction has precisely stdGaussian
on SymFrob p; this is a proved law, not a Gaussian-equivalence premise. -/
theorem symmetrizedFullEntry_preserving (p : ℕ) :
    MeasurePreserving (symmetrizedFullEntry p) (gaussianProductLaw (Fin (p*p)))
      (stdGaussian (SymFrob p)) := by
  have hproj : MeasurePreserving (isoAdjoint (symmetricEntryIsometry p))
      (stdGaussian (EuclideanSpace ℝ (Fin p × Fin p))) (stdGaussian (SymFrob p)) :=
    ⟨(isoAdjoint (symmetricEntryIsometry p)).continuous.measurable,
      stdGaussian_adjoint_isometry_general (symmetricEntryIsometry p)⟩
  convert hproj.comp (fullEntryEuclid_preserving p) using 1
  funext z
  exact symmetrizedFullEntry_eq_adjoint p z
end GaussianEllipsoid.PaperIsonormal
#print axioms GaussianEllipsoid.PaperIsonormal.symmetrizedFullEntry_preserving


set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Module GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open GaussianEllipsoid.UCContinuityGeometry BMGeometry
open GaussianEllipsoid.PaperProjectedRows GaussianEllipsoid.ProjectedClusters
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperIsonormal
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : SeminormedAddCommGroup (EuclideanSpace ℝ (Fin p × Fin p)) :=
  (inferInstance : NormedAddCommGroup (EuclideanSpace ℝ (Fin p × Fin p))).toSeminormedAddCommGroup

theorem symmetrizedFullEntry_matrix (p : ℕ) (z : Fin (p*p) → ℝ) (i j : Fin p) :
    matrix (symmetrizedFullEntry p z) i j =
      (z (finProdFinEquiv (i,j))+z (finProdFinEquiv (j,i)))/2 := by
  change (symmetricFrobLM p ((frobeniusEquivEuclidean p p).symm (fullEntryEuclid p z))) j i = _
  rw [symmetricFrob_apply]
  rfl

/-- Exact equality between the project's full-entry Gaussian row test and
Frobenius inner product against the canonical standard symmetric Gaussian. -/
theorem symmetrizedFullEntry_inner (p : ℕ) (z : Fin (p*p) → ℝ) (A : SymFrob p) :
    ⟪A,symmetrizedFullEntry p z⟫_ℝ = UCNormalizedRows.gaussianRow (matrix A) z := by
  rw [symmetrizedFullEntry_eq_adjoint,isoAdjoint_inner_right]
  have h := Equiv.sum_comp (finProdFinEquiv : (Fin p × Fin p) ≃ Fin (p*p))
    (fun k => matrix A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2*z k)
  simpa [symmetricEntryIsometry,fullEntryEuclid,matrix,frobeniusEquivEuclidean,
    UCNormalizedRows.gaussianRow,frobeniusToMatrix,PiLp.inner_apply,RCLike.inner_apply,mul_comm] using h

def symmetricRows (p n : ℕ) (x : GaussianEntries (p*p) n) : Fin n → SymFrob p :=
  fun i => symmetrizedFullEntry p (fun a => x (a,i))

/-- Full joint iid standard-Gaussian law on the Frobenius symmetric space,
proved from the actual independent entry array. -/
theorem symmetricRows_preserving (p n : ℕ) :
    MeasurePreserving (symmetricRows p n)
      (gaussianProductLaw (Fin (p*p) × Fin n))
      (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob p))) := by
  have hswap : MeasurePreserving
      (fun x : GaussianEntries (p*p) n => fun q : Fin n × Fin (p*p) => x (q.2,q.1))
      (gaussianProductLaw (Fin (p*p) × Fin n)) (gaussianProductLaw (Fin n × Fin (p*p))) :=
    ⟨by fun_prop,gaussianProductLaw_map_subfamily Prod.swap Prod.swap_injective⟩
  have hc : MeasurePreserving
      (fun x : (Fin n × Fin (p*p)) → ℝ => fun i a => x (i,a))
      (gaussianProductLaw (Fin n × Fin (p*p)))
      (Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (p*p)))) :=
    ⟨by fun_prop,gaussianProductLaw_map_curry⟩
  exact (measurePreserving_pi _ _ (fun _ : Fin n => symmetrizedFullEntry_preserving p)).comp (hc.comp hswap)

/-- The projected symmetric matrix is the actual weighted row sum, not just
an equality for one chosen family of tests. -/
theorem symmetricRows_projected_eq {p n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) (x : GaussianEntries (p*p) n) (i : Fin r) :
    symmetricRows p r (transformEntries (p*p) (rowProjection e U) x) i =
      ∑ j, rowWeight U i j • symmetricRows p n x (e j) := by
  apply ext_inner_left ℝ
  intro A
  rw [inner_sum (𝕜 := ℝ) (E := SymFrob p)]
  simp only [real_inner_smul_right (F := SymFrob p)]
  simp only [symmetricRows,symmetrizedFullEntry_inner]
  exact projected_gaussianRows_eq e U x i (matrix A)

def projectSymmetricRows {p n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) (G : Fin n → SymFrob p) : Fin r → SymFrob p :=
  fun i => ∑ j, rowWeight U i j • G (e j)

theorem projectSymmetricRows_measurable {p n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) : Measurable (projectSymmetricRows (p:=p) e U) := by
  apply measurable_pi_iff.mpr
  intro i
  unfold projectSymmetricRows
  fun_prop

/-- Any iid standard isonormal symmetric rows have the projected iid standard
isonormal law; no Gaussian coordinate-realization premise remains. -/
theorem projected_stdGaussian_symmetric_rows {p n m r : ℕ} (e : Fin m ↪ Fin n)
    (U : Euclid r →ₗᵢ[ℝ] Euclid m) :
    (Measure.pi (fun _ : Fin n => stdGaussian (SymFrob p))).map (projectSymmetricRows e U) =
      Measure.pi (fun _ : Fin r => stdGaussian (SymFrob p)) := by
  have hsource := symmetricRows_preserving p n
  have hprojected := (symmetricRows_preserving p r).comp (projected_coordinates_preserving (p*p) e U)
  rw [← hsource.map_eq,Measure.map_map (projectSymmetricRows_measurable e U) hsource.measurable]
  have heq : projectSymmetricRows e U ∘ symmetricRows p n =
      symmetricRows p r ∘ transformEntries (p*p) (rowProjection e U) := by
    funext x i
    exact (symmetricRows_projected_eq e U x i).symm
  rw [heq]
  exact hprojected.map_eq
end GaussianEllipsoid.PaperIsonormal
#print axioms GaussianEllipsoid.PaperIsonormal.projected_stdGaussian_symmetric_rows
#print axioms GaussianEllipsoid.PaperIsonormal.symmetrizedFullEntry_matrix
#print axioms GaussianEllipsoid.PaperIsonormal.symmetrizedFullEntry_inner


set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Module GaussianEllipsoid GaussianMixedNormHelpers
open GaussianEllipsoid.UCContinuityGeometry GaussianEllipsoid.PaperProjectedRows
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperIsonormal
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : SeminormedAddCommGroup (EuclideanSpace ℝ (Fin p × Fin p)) :=
  (inferInstance : NormedAddCommGroup (EuclideanSpace ℝ (Fin p × Fin p))).toSeminormedAddCommGroup

/-- Centered isonormal Gaussian law in the Frobenius symmetric Hilbert space.
All covariance data refer to the genuine Frobenius inner product. -/
structure IsIsonormalSymLaw (p : ℕ) (ν : Measure (SymFrob p)) : Prop where
  gaussian : IsGaussian ν
  mean_zero : (∫ x, x ∂ν) = 0
  covariance_inner : covarianceBilin ν = innerSL ℝ (E := SymFrob p)

/-- The definition of a centered isonormal Gaussian law is equivalent to the
canonical stdGaussian law, by Gaussian mean/covariance uniqueness. -/
theorem isonormalSymLaw_iff_stdGaussian (p : ℕ) (ν : Measure (SymFrob p)) :
    IsIsonormalSymLaw p ν ↔ ν = stdGaussian (SymFrob p) := by
  constructor
  · intro h
    letI := h.gaussian
    apply IsGaussian.ext
    · simpa only [id_eq,integral_id_stdGaussian] using h.mean_zero
    · simpa only [covarianceBilin_stdGaussian] using h.covariance_inner
  · rintro rfl
    exact ⟨inferInstance,integral_id_stdGaussian,covarianceBilin_stdGaussian⟩

/-- No Gaussian-law premise is used for the canonical full-entry construction. -/
theorem canonical_full_entries_isonormal (p : ℕ) :
    IsIsonormalSymLaw p ((gaussianProductLaw (Fin (p*p))).map (symmetrizedFullEntry p)) :=
  (isonormalSymLaw_iff_stdGaussian _ _).mpr (symmetrizedFullEntry_preserving p).map_eq

theorem iid_isonormal_symmetric_rows_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ)
    (G : Fin n → Ω → SymFrob p) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw p (μ.map (G i))) :
    μ.map (fun ω => fun i => G i ω) = Measure.pi (fun _ : Fin n => stdGaussian (SymFrob p)) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hG i).aemeasurable)).mp hind
  rw [h]
  congr 1
  funext i
  exact (isonormalSymLaw_iff_stdGaussian _ _).mp (hiso i)

/-- The paper's projected-row lemma for arbitrary iid isonormal Gaussian rows,
not just one coordinate realization: exact retained nuisance image/rank and
full joint projected law, including r=0. -/
theorem paper_projected_rows_isonormal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p n m r : ℕ}
    (e : Fin m ↪ Fin n) (L : Submodule ℝ (Euclid n))
    (U : Euclid r →ₗᵢ[ℝ] Euclid m)
    (hU : LinearMap.range U.toLinearMap = (retainedNuisance e L)ᗮ)
    (G : Fin n → Ω → SymFrob p) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw p (μ.map (G i))) :
    r = m-finrank ℝ (retainedNuisance e L) ∧ m-finrank ℝ L ≤ r ∧
    μ.map (fun ω => fun i : Fin r => ∑ j, rowWeight U i j • G (e j) ω) =
      Measure.pi (fun _ : Fin r => stdGaussian (SymFrob p)) := by
  refine ⟨(projected_rank e L U hU).1,(projected_rank e L U hU).2,?_⟩
  have harray : Measurable (fun ω => fun i => G i ω) := measurable_pi_iff.mpr hG
  change μ.map (projectSymmetricRows e U ∘ (fun ω => fun i => G i ω)) = _
  rw [← Measure.map_map (projectSymmetricRows_measurable e U) harray,
    iid_isonormal_symmetric_rows_law μ p n G hG hind hiso,
    projected_stdGaussian_symmetric_rows]
end GaussianEllipsoid.PaperIsonormal
#print axioms GaussianEllipsoid.PaperIsonormal.canonical_full_entries_isonormal
#print axioms GaussianEllipsoid.PaperIsonormal.paper_projected_rows_isonormal
