import CanonicalSymGaussian
import PaperGaussianEscapeZero

set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers GaussianTensorMoments
open BMGeometry BMSaddle BMGordon UCEscape
open GaussianEllipsoid.UCContinuityGeometry
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperIsonormalEscape
open PaperIsonormal PaperGaussianEscape PaperPSDSphereWidth
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

def sampleOfSymmetricRows {r d : ℕ} (G : Fin r → SymFrob d) : BMSaddle.Sample r d :=
  (WithLp.equiv 2 _).symm (fun p => matrix (G p.1) p.2.1 p.2.2)

def rowEscape {r d : ℕ} (G : Fin r → SymFrob d) : ℝ :=
  projectedEscape (d := d) (fun _ : PUnit.{1} => LinearIsometry.id : PUnit.{1} → Euclid r →ₗᵢ[ℝ] Euclid r)
    (sampleOfSymmetricRows G)

lemma sampleOfSymmetricRows_continuous (r d : ℕ) :
    Continuous (sampleOfSymmetricRows (r := r) (d := d)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro p
  change Continuous (fun G : Fin r → SymFrob d => (G p.1).val p.2.2 p.2.1)
  fun_prop

lemma rowEscape_continuous {r d : ℕ} (hd : 0 < d) : Continuous (rowEscape (r := r) (d := d)) :=
  (projectedEscape_lipschitz hd _).continuous.comp (sampleOfSymmetricRows_continuous r d)

def psdSym {d : ℕ} (S : ↥(psdUnit d)) : SymFrob d := ⟨S.val,S.property.1.1⟩

lemma measurement_symmetricRows {r d : ℕ} (G : Fin r → SymFrob d) (S : ↥(psdUnit d))
    (i : Fin r) : measurement (sampleOfSymmetricRows G) S i=⟪G i,psdSym S⟫_ℝ := by
  change (∑ j,∑ k, matrix (G i) k j*S.val j k) = _
  change (∑ j,∑ k, (G i).val j k*S.val j k) = ∑ j,∑ k,S.val j k*(G i).val j k
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Literal infimum of the Euclidean norms of the isonormal row pairings. -/
lemma rowEscape_eq_inf {r d : ℕ} (G : Fin r → SymFrob d) :
    rowEscape G = sInf (Set.range (fun S : ↥(psdUnit d) =>
      ‖(WithLp.equiv 2 _).symm (fun i : Fin r => ⟪G i,psdSym S⟫_ℝ)‖)) := by
  unfold rowEscape projectedEscape
  have he (S : ↥(psdUnit d)) : measurement (sampleOfSymmetricRows G) S =
      (WithLp.equiv 2 _).symm (fun i : Fin r => ⟪G i,psdSym S⟫_ℝ) := by
    ext i
    exact measurement_symmetricRows G S i
  simp only [LinearIsometry.id_toContinuousLinearMap,ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply,he]
  congr 1
  ext y
  simp

/-- The paper's source-matrix infimum, with its exact PSD and Frobenius-unit domain. -/
def paperRowEscape {r d : ℕ} (G : Fin r → SymFrob d) : ℝ :=
  sInf ((fun A : Square d => ‖measurement (sampleOfSymmetricRows G) (sourceFrobenius A)‖) ''
    paperPSDSphere d)

lemma source_measurement_pairings {r d : ℕ} (G : Fin r → SymFrob d) (A : Square d) :
    measurement (sampleOfSymmetricRows G) (sourceFrobenius A) =
      (WithLp.equiv 2 _).symm (fun k : Fin r => ∑ i,∑ j,matrix (G k) i j*A i j) := by
  ext k
  change (∑ j,∑ i,matrix (G k) i j*A i j) = ∑ i,∑ j,matrix (G k) i j*A i j
  exact Finset.sum_comm

lemma rowEscape_eq_paperRowEscape {r d : ℕ} (G : Fin r → SymFrob d) :
    rowEscape G=paperRowEscape G := by
  have he : rowEscape G = sInf (Set.range (fun S : ↥(psdUnit d) =>
      ‖measurement (sampleOfSymmetricRows G) S‖)) := by
    unfold rowEscape projectedEscape
    simp only [LinearIsometry.id_toContinuousLinearMap,ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_apply]
    congr 1
    ext y
    simp
  rw [he]
  unfold paperRowEscape
  congr 1
  ext y
  constructor
  · rintro ⟨S,rfl⟩
    let A := opMatrix (frobeniusOperator S.val)
    have hA : A.PosSemidef := (opMatrix_posSemidef_iff _).mpr S.property.1
    have hn : frobeniusNorm A=1 := by
      rw [frobeniusNorm_opMatrix,operatorFrobenius_frobeniusOperator]
      simpa only [Metric.mem_sphere,dist_zero_right] using S.property.2
    refine ⟨A,⟨hA,hn⟩,?_⟩
    dsimp only [A]
    rw [sourceFrobenius_opMatrix,operatorFrobenius_frobeniusOperator]
  · rintro ⟨A,hA,rfl⟩
    exact ⟨⟨sourceFrobenius A,sourceFrobenius_mem_psdUnit A hA.1 hA.2⟩,rfl⟩

lemma canonical_rowEscape {r d : ℕ} (z : Raw r d) :
    rowEscape (fun i => symmetrizedFullEntry d (z i)) =
      projectedEscape (d := d) (fun _ : PUnit.{1} => LinearIsometry.id : PUnit.{1} → Euclid r →ₗᵢ[ℝ] Euclid r)
        (rawSample r d z) := by
  unfold rowEscape projectedEscape
  congr 1
  apply congrArg Set.range
  funext p
  congr 1
  congr 1
  ext i
  rw [measurement_symmetricRows,real_inner_comm,symmetrizedFullEntry_inner,gaussianRow_eq_measurement]
  rfl

/-- Exact Gaussian escape for arbitrary independent centered isonormal symmetric
rows, using their genuine Frobenius covariance law and the source's exact threshold. -/
theorem isonormal_escape {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d r : ℕ} (hd : 0 < d)
    (G : Fin r → Ω → SymFrob d) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw d (μ.map (G i)))
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | rowEscape (fun i => G i ω) <
      (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r))-paperGaussianSphereWidth d-t} ≤
      Real.exp (-t^2/2) := by
  let a := (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r))-paperGaussianSphereWidth d-t
  let E : Set (Fin r → SymFrob d) := {x | rowEscape x<a}
  have hE : MeasurableSet E := (isOpen_lt (rowEscape_continuous hd) continuous_const).measurableSet
  have hp : MeasurePreserving (fun ω => fun i => G i ω) μ
      (Measure.pi (fun _ : Fin r => stdGaussian (SymFrob d))) :=
    ⟨measurable_pi_iff.mpr hG,iid_isonormal_symmetric_rows_law μ d r G hG hind hiso⟩
  change μ.real ((fun ω => fun i => G i ω) ⁻¹' E) ≤ _
  rw [hp.measureReal_preimage hE.nullMeasurableSet]
  have hc := measurePreserving_pi (fun _ : Fin r => gaussianProductLaw (Fin (d*d)))
    (fun _ : Fin r => stdGaussian (SymFrob d)) (fun _ => symmetrizedFullEntry_preserving d)
  rw [← hc.measureReal_preimage hE.nullMeasurableSet]
  change (rawSourceLaw r d).real {z | rowEscape (fun i => symmetrizedFullEntry d (z i))<a} ≤ _
  simp_rw [canonical_rowEscape]
  let U : PUnit.{1} → Euclid r →ₗᵢ[ℝ] Euclid r := fun _ => LinearIsometry.id
  have hevent : MeasurableSet {X : BMSaddle.Sample r d | projectedEscape (d := d) U X<a} :=
    (isOpen_lt (projectedEscape_lipschitz hd U).continuous continuous_const).measurableSet
  have he := gaussianRows_event r d {X : BMSaddle.Sample r d | projectedEscape (d := d) U X<a} hevent
  change (rawSourceLaw r d).real {z | projectedEscape (d := d) U (rawSample r d z)<a} ≤ _
  calc
    _ = (sampleLaw r d).real {X : BMSaddle.Sample r d | projectedEscape (d := d) U X<a} := by
      simpa only [rawSourceLaw,Set.mem_setOf_eq] using! he
    _ ≤ _ := gaussian_escape_all_output_dimensions hd LinearIsometry.id t ht

/-- Literal source matrix domain and arbitrary independent isonormal rows. -/
theorem paper_gaussian_escape {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d r : ℕ} (hd : 0 < d)
    (G : Fin r → Ω → SymFrob d) (hG : ∀ i, Measurable (G i))
    (hind : iIndepFun G μ) (hiso : ∀ i, IsIsonormalSymLaw d (μ.map (G i)))
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | paperRowEscape (fun i => G i ω) <
      (∫ g : Euclid r, ‖g‖ ∂euclideanGaussianLaw (Fin r))-paperGaussianSphereWidth d-t} ≤
      Real.exp (-t^2/2) := by
  simpa only [rowEscape_eq_paperRowEscape] using isonormal_escape μ hd G hG hind hiso t ht

#print axioms paper_gaussian_escape
end GaussianEllipsoid.PaperIsonormalEscape
