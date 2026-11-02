import UCPSDMinimumMean
import UCProjectSpectralPeeling

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid GaussianTensorMoments GaussianMixedNormHelpers BMGeometry UCEscape
namespace GaussianEllipsoid.PaperPSDSphereWidth

def sphereSupport (d : ℕ) (x : (Fin d × Fin d) → ℝ) : ℝ :=
  sSup ((fun S => ⟪fullEntryMatrix x,S⟫_ℝ) '' psdUnit d)

lemma fullEntry_neg (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    fullEntryMatrix (-x) = -fullEntryMatrix x := by
  change (frobeniusEquivEuclidean d d).symm (-((WithLp.equiv 2 _).symm x)) = _
  exact map_neg _ _

lemma sphere_values_bddAbove (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    BddAbove ((fun S => ⟪fullEntryMatrix x,S⟫_ℝ) '' psdUnit d) := by
  refine ⟨‖fullEntryMatrix x‖, ?_⟩
  rintro y ⟨S,hS,rfl⟩
  have hn : ‖S‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hS.2
  simpa only [hn,mul_one] using real_inner_le_norm (fullEntryMatrix x) S

lemma sphereSupport_eq_neg_min {d : ℕ} (hd : 0 < d) (x : (Fin d × Fin d) → ℝ) :
    sphereSupport d x = -psdMinimumRaw d (-x) := by
  apply le_antisymm
  · apply csSup_le ((psdUnit_nonempty hd).image _)
    rintro y ⟨S,hS,rfl⟩
    have h := csInf_le (psd_values_bddBelow d (fullEntryMatrix (-x))) ⟨S,hS,rfl⟩
    change psdMinimumRaw d (-x) ≤ ⟪fullEntryMatrix (-x),S⟫_ℝ at h
    rw [fullEntry_neg,inner_neg_left] at h
    linarith
  · have h : -sphereSupport d x ≤ psdMinimumRaw d (-x) := by
      apply le_csInf ((psdUnit_nonempty hd).image _)
      rintro y ⟨S,hS,rfl⟩
      have hs : ⟪fullEntryMatrix x,S⟫_ℝ ≤ sphereSupport d x :=
        le_csSup (sphere_values_bddAbove d x) ⟨S,hS,rfl⟩
      dsimp only
      rw [fullEntry_neg,inner_neg_left]
      linarith
    linarith

theorem sphereSupport_integrable {d : ℕ} (hd : 0 < d) :
    Integrable (sphereSupport d) (gaussianProductLaw (Fin d × Fin d)) := by
  have h := psdMinimumRaw_integrable hd
  have hp := gaussianProductLaw_neg_preserving (Fin d × Fin d)
  have hn : Integrable (fun x => psdMinimumRaw d (-x)) (gaussianProductLaw (Fin d × Fin d)) :=
    (hp.integrable_comp h.aestronglyMeasurable).mpr h
  have he : sphereSupport d = fun x => -psdMinimumRaw d (-x) :=
    funext (sphereSupport_eq_neg_min hd)
  rw [he]
  exact hn.neg

/-- The true PSD-unit-sphere Gaussian width, not the PSD-ball support width. -/
def sphereWidth (d : ℕ) : ℝ := ∫ x, sphereSupport d x ∂gaussianProductLaw (Fin d × Fin d)

theorem sphereWidth_le_sqrt {d : ℕ} (hd : 0 < d) :
    sphereWidth d ≤ Real.sqrt ((d:ℝ)*(d+1)/4) := by
  have h : sphereWidth d ≤ psdWidth d := by
    apply integral_mono (sphereSupport_integrable hd) (gaussianPSDSupportRaw_integrable d)
    intro x
    apply csSup_le ((psdUnit_nonempty hd).image _)
    rintro y ⟨S,hS,rfl⟩
    exact fullEntry_pairing_le_psdSupport S hS x
  exact h.trans (psdWidth_le_sqrt d)

def paperPSDSphere (d : ℕ) : Set (Square d) :=
  {A | A.PosSemidef ∧ frobeniusNorm A=1}

def paperSymmetricPairing (d : ℕ) (x : (Fin d × Fin d) → ℝ) (A : Square d) : ℝ :=
  ⟪operatorFrobenius (isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)),sourceFrobenius A⟫_ℝ

lemma paperSymmetricPairing_eq {d : ℕ} (x : (Fin d × Fin d) → ℝ) (A : Square d)
    (hA : A.PosSemidef) :
    paperSymmetricPairing d x A = ⟪fullEntryMatrix x,sourceFrobenius A⟫_ℝ := by
  have hs := ((sourceFrobenius_psd A).mpr hA).1
  have h := symmetrization_pairing (fullEntryMatrix x) (frobeniusOperator (sourceFrobenius A)) hs
  simpa only [paperSymmetricPairing,isotropicSymmetricOp_frobenius,
    operatorFrobenius_frobeniusOperator] using h

def paperGaussianSphereWidth (d : ℕ) : ℝ :=
  ∫ x, sSup ((paperSymmetricPairing d x) '' paperPSDSphere d)
    ∂gaussianProductLaw (Fin d × Fin d)

lemma paper_sphere_support_eq (d : ℕ) (x : (Fin d × Fin d) → ℝ) :
    sSup ((paperSymmetricPairing d x) '' paperPSDSphere d) = sphereSupport d x := by
  congr 1
  ext y
  constructor
  · rintro ⟨A,hA,rfl⟩
    refine ⟨sourceFrobenius A,sourceFrobenius_mem_psdUnit A hA.1 hA.2,?_⟩
    exact (paperSymmetricPairing_eq x A hA.1).symm
  · rintro ⟨S,hS,rfl⟩
    let A := opMatrix (frobeniusOperator S)
    have hA : A.PosSemidef := (opMatrix_posSemidef_iff _).mpr hS.1
    have hnorm : frobeniusNorm A=1 := by
      rw [frobeniusNorm_opMatrix,operatorFrobenius_frobeniusOperator]
      simpa only [Metric.mem_sphere,dist_zero_right] using hS.2
    refine ⟨A,⟨hA,hnorm⟩,?_⟩
    rw [paperSymmetricPairing_eq x A hA]
    dsimp only [A]
    rw [sourceFrobenius_opMatrix,operatorFrobenius_frobeniusOperator]

/-- Exact paper Gaussian width inequality on symmetric PSD Frobenius-unit matrices. -/
theorem paper_gaussian_sphere_width_bound {d : ℕ} (hd : 0 < d) :
    paperGaussianSphereWidth d ≤ Real.sqrt ((d:ℝ)*(d+1)/4) := by
  simp_rw [paperGaussianSphereWidth,paper_sphere_support_eq]
  exact sphereWidth_le_sqrt hd

#print axioms paper_gaussian_sphere_width_bound
#print axioms sphereSupport_integrable
end GaussianEllipsoid.PaperPSDSphereWidth
