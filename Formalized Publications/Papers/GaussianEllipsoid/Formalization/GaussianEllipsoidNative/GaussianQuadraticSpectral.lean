import GaussianRadialDensity
import RadialInvariance
import CenteredQuadraticGauge
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Trace

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers Module
open scoped BigOperators InnerProductSpace

namespace BMQuadraticSpectral

abbrev Euclid (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Actual normalized centered Gaussian quadratic observable. -/
def normalizedQuadratic {d : ℕ} (T : Euclid d →L[ℝ] Euclid d) (x : Euclid d) : ℝ :=
  (⟪x, T x⟫_ℝ - LinearMap.trace ℝ (Euclid d) T.toLinearMap) / Real.sqrt d

/-- Weights are actual spectral eigenvalues, normalized by the ambient dimension. -/
def eigenWeight {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) (i : Fin d) : ℝ :=
  hT.eigenvalues finrank_euclideanSpace_fin i / Real.sqrt d

/-- Actual iid Gaussian law is invariant under every Euclidean linear isometry. -/
theorem euclideanGaussianLaw_map_isometry {ι : Type*} [Fintype ι]
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (euclideanGaussianLaw ι).map e = euclideanGaussianLaw ι := by
  rw [euclideanGaussianLaw_eq_withDensity]
  exact GaussianProductDensity.radial_density_isometry e
    (fun r => ENNReal.ofReal (gaussianDensityConstant ι * Real.exp (-(1/2:ℝ)*r^2)))
    (by fun_prop)

/-- Passing from Euclidean realization to ordinary coordinate functions preserves the Gaussian law. -/
theorem coordinates_preserving {ι : Type*} [Fintype ι] :
    MeasurePreserving ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm)
      (euclideanGaussianLaw ι) (gaussianProductLaw ι) := by
  refine ⟨((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).measurable, ?_⟩
  unfold euclideanGaussianLaw
  rw [Measure.map_map ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).measurable
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable]
  have hh : ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm) ∘
      (MeasurableEquiv.toLp 2 (ι → ℝ)) = id := by
    funext x
    exact ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).apply_symm_apply x
  rw [hh, Measure.map_id]

/-- The spectral change of coordinates, as a measurable equivalence. -/
def spectralCoordinates {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) : Euclid d ≃ᵐ (Fin d → ℝ) :=
  (hT.eigenvectorBasis finrank_euclideanSpace_fin).repr.toHomeomorph.toMeasurableEquiv.trans
    ((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)).symm)

theorem spectralCoordinates_preserving {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) :
    MeasurePreserving (spectralCoordinates hT)
      (euclideanGaussianLaw (Fin d)) (gaussianProductLaw (Fin d)) := by
  exact coordinates_preserving.comp
    ⟨(hT.eigenvectorBasis finrank_euclideanSpace_fin).repr.continuous.measurable,
      euclideanGaussianLaw_map_isometry _⟩

/-- Trace equals the sum of the actual spectral eigenvalues. -/
theorem trace_eq_sum_eigenvalues {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) :
    LinearMap.trace ℝ (Euclid d) T.toLinearMap =
      ∑ i, hT.eigenvalues finrank_euclideanSpace_fin i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ
    (hT.eigenvectorBasis finrank_euclideanSpace_fin).toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hT.eigenvectorBasis_apply_self_apply]
  simp

/-- Pointwise diagonalization of the actual quadratic form by the spectral basis. -/
theorem inner_self_eq_sum_eigenvalues {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) (x : Euclid d) :
    ⟪x, T x⟫_ℝ = ∑ i, hT.eigenvalues finrank_euclideanSpace_fin i *
      ((spectralCoordinates hT x) i)^2 := by
  let b := hT.eigenvectorBasis finrank_euclideanSpace_fin
  rw [← b.repr.inner_map_map x (T x), EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  change b.repr (T.toLinearMap x) i * b.repr x i = _
  rw [hT.eigenvectorBasis_apply_self_apply]
  change (hT.eigenvalues finrank_euclideanSpace_fin i * b.repr x i) * b.repr x i =
    hT.eigenvalues finrank_euclideanSpace_fin i * (b.repr x i)^2
  ring

/-- Exact observable equality, including centering and normalization. -/
theorem normalizedQuadratic_eq_centeredDiagonal {d : ℕ}
    {T : Euclid d →L[ℝ] Euclid d} (hT : T.toLinearMap.IsSymmetric) (x : Euclid d) :
    normalizedQuadratic T x =
      GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight hT) (spectralCoordinates hT x) := by
  rw [normalizedQuadratic, inner_self_eq_sum_eigenvalues hT,
    trace_eq_sum_eigenvalues hT, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [eigenWeight]
  ring

/-- Every actual eigenvalue is controlled by the genuine Euclidean operator norm. -/
theorem abs_eigenvalue_le_norm {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) (i : Fin d) :
    |hT.eigenvalues finrank_euclideanSpace_fin i| ≤ ‖T‖ := by
  have h := T.le_opNorm (hT.eigenvectorBasis finrank_euclideanSpace_fin i)
  change ‖T.toLinearMap _‖ ≤ _ at h
  rw [hT.apply_eigenvectorBasis, norm_smul,
    (hT.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one,
    mul_one, mul_one, Real.norm_eq_abs] at h
  exact h

/-- The spectral weights have the required uniform maximum bound. -/
theorem eigenWeight_abs_le {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1) (i : Fin d) :
    |eigenWeight hT i| ≤ 1 / Real.sqrt d := by
  rw [eigenWeight, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right ((abs_eigenvalue_le_norm hT i).trans hN)
    (Real.sqrt_nonneg _)

/-- The squared spectral weights sum to at most one for every positive dimension. -/
theorem sum_eigenWeight_sq_le {d : ℕ} (hd : 0 < d)
    {T : Euclid d →L[ℝ] Euclid d} (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1) :
    (∑ i, (eigenWeight hT i)^2) ≤ 1 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  calc
    _ ≤ ∑ _i : Fin d, (1 / Real.sqrt d)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := pow_le_pow_left₀ (abs_nonneg (eigenWeight hT i))
        (eigenWeight_abs_le hT hN i) 2
      simpa only [sq_abs] using h
    _ = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, div_pow, one_pow, Real.sq_sqrt hd'.le]
      field_simp

/-- Continuity of the actual normalized quadratic observable. -/
theorem continuous_normalizedQuadratic {d : ℕ} (T : Euclid d →L[ℝ] Euclid d) :
    Continuous (normalizedQuadratic T) := by
  unfold normalizedQuadratic
  fun_prop

theorem continuous_centeredDiagonal {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    Continuous (GaussianEllipsoidCandidate.centeredDiagonal w) := by
  unfold GaussianEllipsoidCandidate.centeredDiagonal
  fun_prop

/-- Actual Gaussian spectral rotation law. Neither Gaussian rotation nor diagonalization is a premise. -/
theorem normalizedQuadratic_identDistrib {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) :
    IdentDistrib (normalizedQuadratic T) (GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight hT))
      (euclideanGaussianLaw (Fin d)) (gaussianProductLaw (Fin d)) := by
  refine ⟨(continuous_normalizedQuadratic T).measurable.aemeasurable,
    (continuous_centeredDiagonal (eigenWeight hT)).measurable.aemeasurable, ?_⟩
  rw [← (spectralCoordinates_preserving hT).map_eq,
    Measure.map_map (continuous_centeredDiagonal (eigenWeight hT)).measurable (spectralCoordinates hT).measurable]
  congr 1
  funext x
  exact normalizedQuadratic_eq_centeredDiagonal hT x

/-- Arbitrary integral transport, including nonintegrable functions under the Bochner convention. -/
theorem integral_normalizedQuadratic_eq {d : ℕ} {T : Euclid d →L[ℝ] Euclid d}
    (hT : T.toLinearMap.IsSymmetric) (f : ℝ → ℝ) :
    (∫ x, f (normalizedQuadratic T x) ∂euclideanGaussianLaw (Fin d)) =
      ∫ z, f (GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight hT) z)
        ∂gaussianProductLaw (Fin d) := by
  simp_rw [normalizedQuadratic_eq_centeredDiagonal hT]
  exact (spectralCoordinates_preserving hT).integral_comp
    (spectralCoordinates hT).measurableEmbedding (fun z => f (GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight hT) z))

end BMQuadraticSpectral
