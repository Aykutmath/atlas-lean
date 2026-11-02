import BMGordonExpectations
import CanonicalSymGaussian
import PaperPSDSphereWidth

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open BMGeometry UCEscape BMGordon
open GaussianEllipsoid.UCContinuityGeometry
open scoped InnerProductSpace
namespace GaussianEllipsoid.PaperIsonormalSphereWidth
open PaperIsonormal PaperPSDSphereWidth
local instance {p : ℕ} : NormedAddCommGroup (SymFrob p) := Submodule.normedAddCommGroup (symmetricFrobenius p)
local instance {p : ℕ} : NormedSpace ℝ (SymFrob p) := Submodule.normedSpace (symmetricFrobenius p)
local instance {p : ℕ} : SeminormedAddCommGroup (SymFrob p) :=
  (inferInstance : NormedAddCommGroup (SymFrob p)).toSeminormedAddCommGroup
local instance {p : ℕ} : InnerProductSpace ℝ (SymFrob p) := Submodule.innerProductSpace (symmetricFrobenius p)

def symmetricSphereSupport {d : ℕ} (G : SymFrob d) : ℝ :=
  sSup ((fun S : HMat d => ⟪G.val,S⟫_ℝ) '' psdUnit d)

lemma symmetricSphereSupport_eq_raw {d : ℕ} (G : SymFrob d) :
    symmetricSphereSupport G = sphereSupport d
      ((WithLp.equiv 2 _) ((frobeniusEquivEuclidean d d) G.val)) := by
  simp only [sphereSupport, fullEntryMatrix, Equiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply, symmetricSphereSupport]

lemma symmetricSphereSupport_continuous {d : ℕ} (hd : 0 < d) :
    Continuous (symmetricSphereSupport (d := d)) := by
  have he : symmetricSphereSupport (d := d) = fun G : SymFrob d => -psdMinimum d (-G.val) := by
    funext G
    rw [symmetricSphereSupport_eq_raw, sphereSupport_eq_neg_min hd]
    congr 1

  rw [he]
  exact ((psdMinimum_lipschitz hd).continuous.comp continuous_subtype_val.neg).neg

lemma symmetricSphereSupport_canonical (d : ℕ) (z : Fin (d*d) → ℝ) :
    symmetricSphereSupport (symmetrizedFullEntry d z) =
      sphereSupport d (fun a => z (finProdFinEquiv a)) := by
  unfold symmetricSphereSupport sphereSupport
  congr 1
  apply Set.image_congr
  intro S hS
  have hs := symmetrization_pairing
    (fullEntryMatrix (fun a => z (finProdFinEquiv a))) (frobeniusOperator S) hS.1.1
  simpa only [operatorFrobenius_frobeniusOperator, symmetrizedFullEntry, fullEntryMatrix, fullEntryEuclid] using! hs

/-- The support is exactly over the paper's symmetric PSD Frobenius-unit domain. -/
lemma symmetricSphereSupport_source {d : ℕ} (G : SymFrob d) :
    symmetricSphereSupport G =
      sSup ((fun A : Square d => ⟪G.val,sourceFrobenius A⟫_ℝ) '' paperPSDSphere d) := by
  unfold symmetricSphereSupport
  congr 1
  ext y
  constructor
  · rintro ⟨S,hS,rfl⟩
    let A := opMatrix (frobeniusOperator S)
    have hA : A.PosSemidef := (opMatrix_posSemidef_iff _).mpr hS.1
    have hn : frobeniusNorm A = 1 := by
      rw [frobeniusNorm_opMatrix,operatorFrobenius_frobeniusOperator]
      simpa only [Metric.mem_sphere,dist_zero_right] using hS.2
    refine ⟨A,⟨hA,hn⟩,?_⟩
    dsimp only [A]
    rw [sourceFrobenius_opMatrix,operatorFrobenius_frobeniusOperator]
  · rintro ⟨A,hA,rfl⟩
    exact ⟨sourceFrobenius A,sourceFrobenius_mem_psdUnit A hA.1 hA.2,rfl⟩

theorem symmetricSphereSupport_integrable {d : ℕ} (hd : 0 < d) :
    Integrable (symmetricSphereSupport (d := d)) (stdGaussian (SymFrob d)) := by
  have hc : MeasurePreserving
      (fun z : Fin (d*d) → ℝ => fun a : Fin d × Fin d => z (finProdFinEquiv a))
      (gaussianProductLaw (Fin (d*d))) (gaussianProductLaw (Fin d × Fin d)) :=
    ⟨by fun_prop, gaussianProductLaw_map_subfamily _ finProdFinEquiv.injective⟩
  have hi := (hc.integrable_comp (sphereSupport_integrable hd).aestronglyMeasurable).mpr
    (sphereSupport_integrable hd)
  apply ((symmetrizedFullEntry_preserving d).integrable_comp
    (symmetricSphereSupport_continuous hd).aestronglyMeasurable).mp
  simpa only [Function.comp_def, symmetricSphereSupport_canonical] using hi

/-- Equality of the true sphere width under the standard symmetric Gaussian law
and the paper's explicit independent-entry symmetric representation. -/
theorem paper_sphere_width_eq_stdGaussian {d : ℕ} (hd : 0 < d) :
    paperGaussianSphereWidth d =
      ∫ G : SymFrob d, symmetricSphereSupport G ∂stdGaussian (SymFrob d) := by
  have hp := symmetrizedFullEntry_preserving d
  have hs := integral_comp_preserving hp
    (symmetricSphereSupport_continuous hd).aestronglyMeasurable
  have hc : MeasurePreserving
      (fun z : Fin (d*d) → ℝ => fun a : Fin d × Fin d => z (finProdFinEquiv a))
      (gaussianProductLaw (Fin (d*d))) (gaussianProductLaw (Fin d × Fin d)) :=
    ⟨by fun_prop, gaussianProductLaw_map_subfamily _ finProdFinEquiv.injective⟩
  have hm : AEStronglyMeasurable (sphereSupport d) (gaussianProductLaw (Fin d × Fin d)) :=
    (sphereSupport_integrable hd).aestronglyMeasurable
  have he := integral_comp_preserving hc hm
  simp_rw [symmetricSphereSupport_canonical] at hs
  rw [he] at hs
  simpa only [paperGaussianSphereWidth, paper_sphere_support_eq] using hs

theorem paper_sphere_width_eq_isonormal {d : ℕ} (hd : 0 < d)
    (μ : Measure (SymFrob d)) (hμ : IsIsonormalSymLaw d μ) :
    paperGaussianSphereWidth d = ∫ G : SymFrob d, symmetricSphereSupport G ∂μ := by
  rw [(isonormalSymLaw_iff_stdGaussian d μ).mp hμ]
  exact paper_sphere_width_eq_stdGaussian hd

theorem paper_sphere_width_source_isonormal {d : ℕ} (hd : 0 < d)
    (μ : Measure (SymFrob d)) (hμ : IsIsonormalSymLaw d μ) :
    paperGaussianSphereWidth d =
      ∫ G : SymFrob d, sSup ((fun A : Square d => ⟪G.val,sourceFrobenius A⟫_ℝ) ''
        paperPSDSphere d) ∂μ := by
  simpa only [symmetricSphereSupport_source] using paper_sphere_width_eq_isonormal hd μ hμ

#print axioms paper_sphere_width_eq_stdGaussian
#print axioms symmetricSphereSupport_integrable
#print axioms paper_sphere_width_source_isonormal
#print axioms paper_sphere_width_eq_isonormal
end GaussianEllipsoid.PaperIsonormalSphereWidth
