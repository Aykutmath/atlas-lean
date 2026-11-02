import ProjectedGaussianLaw
import CoordinateBlockPinching

noncomputable section
open MeasureTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.ProjectedClusters

/-- The rank-one map a bᵀ, in genuine Euclidean operator spaces. -/
def outerOperator {h k : ℕ} (a : Euclid h) (b : Euclid k) : Euclid k →L[ℝ] Euclid h :=
  (innerSL ℝ b).smulRight a

@[simp] theorem outerOperator_apply {h k : ℕ} (a : Euclid h) (b x : Euclid k) :
    outerOperator a b x = ⟪b, x⟫_ℝ • a := rfl

theorem gaussianBilinearOperator_eq_outer_sum (n h d : ℕ)
    (z : GaussianEntries n h × GaussianEntries n h) (u : Euclid n) :
    frobeniusOperator (gaussianBilinearOperator n h d z u) =
      (Real.sqrt (d : ℝ))⁻¹ • ∑ i, u i •
        outerOperator (entriesToRows n h z.1 i) (entriesToRows n h z.2 i) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.ext
  intro b
  ext a
  change frobeniusOperator (gaussianBilinearOperator n h d z u)
    (EuclideanSpace.basisFun (Fin h) ℝ b) a = _
  rw [frobeniusOperator_basis]
  change frobeniusToMatrix (gaussianBilinearOperator n h d z u) a b =
    (((Real.sqrt (d : ℝ))⁻¹ • ∑ i, u i •
      outerOperator (entriesToRows n h z.1 i) (entriesToRows n h z.2 i)) : Euclid h →L[ℝ] Euclid h)
      (EuclideanSpace.basisFun (Fin h) ℝ b) a
  rw [gaussianBilinearOperator_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    outerOperator_apply, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul, mul_one, PiLp.smul_apply, smul_eq_mul, euclid_sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change u i * (z.1 (i,a) * z.2 (i,b)) = u i * (z.2 (i,b) * z.1 (i,a))
  ring

theorem outerOperator_compression {h k h' k' : ℕ}
    (U : Euclid h →L[ℝ] Euclid h') (V : Euclid k →L[ℝ] Euclid k')
    (a : Euclid h) (b : Euclid k) :
    U ∘L outerOperator a b ∘L ContinuousLinearMap.adjoint V = outerOperator (U a) (V b) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, outerOperator_apply, map_smul]
  rw [← ContinuousLinearMap.adjoint_inner_right]

/-- Coordinate pushforward preserves the actual d-scaled bilinear observable,
with exactly the matrix compression dictated by the two linear maps. -/
theorem gaussianBilinearOperator_transformSample {h k : ℕ} (n d : ℕ)
    (U V : Euclid h →L[ℝ] Euclid k)
    (z : GaussianEntries n h × GaussianEntries n h) (u : Euclid n) :
    frobeniusOperator (gaussianBilinearOperator n k d (transformSample n U V z) u) =
      U ∘L frobeniusOperator (gaussianBilinearOperator n h d z u) ∘L
        ContinuousLinearMap.adjoint V := by
  rw [gaussianBilinearOperator_eq_outer_sum, gaussianBilinearOperator_eq_outer_sum]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, map_smul, map_sum, outerOperator_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : entriesToRows n k (transformSample n U V z).2 i = V (entriesToRows n h z.2 i) := rfl
  rw [hi, ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The spectral nuclear norm of the transformed sample is bounded by the
actual ambient observable under any pair of contractions. -/
theorem spectralNuclear_transformSample_le {h k : ℕ} (n d : ℕ)
    (U V : Euclid h →L[ℝ] Euclid k) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (z : GaussianEntries n h × GaussianEntries n h) (u : Euclid n) :
    spectralNuclearNorm (gaussianBilinearOperator n k d (transformSample n U V z) u) ≤
      spectralNuclearNorm (gaussianBilinearOperator n h d z u) := by
  have hh := spectralNuclear_compression_le U
    (frobeniusOperator (gaussianBilinearOperator n h d z u))
    (ContinuousLinearMap.adjoint V) hU (by simpa using hV)
  rw [← gaussianBilinearOperator_transformSample, operatorFrobenius_frobeniusOperator,
    operatorFrobenius_frobeniusOperator] at hh
  exact hh

end GaussianEllipsoid.ProjectedClusters
