import GaussianVarianceBound

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace
namespace BMGeometry

theorem gaussianPSDSupport_second_moment (d : ℕ) :
    (∫ x, (gaussianPSDSupport d x)^2 ∂euclideanGaussianLaw (Fin d × Fin d)) =
      (d:ℝ)*(d+1)/4 := by
  rw [euclideanGaussianLaw, integral_map
    (f := fun x => (gaussianPSDSupport d x)^2)
    (MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).measurable.aemeasurable
    (by simpa using! ((gaussianPSDSupport_continuous d).pow 2).aestronglyMeasurable)]
  exact gaussianPSDSupportRaw_second_moment d

/-- Dimension-free variance of the actual positive spectral Frobenius support. -/
theorem gaussianPSDSupport_variance_le (d : ℕ) :
    variance (gaussianPSDSupport d) (euclideanGaussianLaw (Fin d × Fin d)) ≤ Real.pi^2/8 :=
  GaussianVariance.lipschitz_gaussian_variance_le (gaussianPSDSupport_lipschitz d)

/-- Actual Gaussian PSD-cone support mean with an absolute additive square loss. -/
theorem gaussianPSDSupport_mean_lower (d : ℕ) :
    Real.sqrt ((d:ℝ)*(d+1)/4-Real.pi^2/8) ≤
      ∫ x, gaussianPSDSupport d x ∂euclideanGaussianLaw (Fin d × Fin d) := by
  apply GaussianVariance.mean_lower_of_second_moment (gaussianPSDSupport_lipschitz d)
    (fun x => norm_nonneg _) (gaussianPSDSupport_second_moment d)

/-- Raw iid matrix-entry formulation for integration with the BM assembly. -/
theorem gaussianPSDSupportRaw_mean_lower (d : ℕ) :
    Real.sqrt ((d:ℝ)*(d+1)/4-Real.pi^2/8) ≤
      ∫ x, gaussianPSDSupportRaw d x ∂gaussianProductLaw (Fin d × Fin d) := by
  have h := gaussianPSDSupport_mean_lower d
  rw [euclideanGaussianLaw, integral_map
    (MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).measurable.aemeasurable
    (gaussianPSDSupport_continuous d).aestronglyMeasurable] at h
  exact h

/-- Centered-square form directly on iid matrix-entry coordinates. -/
theorem gaussianPSDSupportRaw_centered_sq_le (d : ℕ) :
    (∫ x, (gaussianPSDSupportRaw d x -
      (∫ y, gaussianPSDSupportRaw d y ∂gaussianProductLaw (Fin d × Fin d)))^2
      ∂gaussianProductLaw (Fin d × Fin d)) ≤ Real.pi^2/8 := by
  have hv := gaussianPSDSupport_variance_le d
  rw [variance_eq_integral (gaussianPSDSupport_continuous d).measurable.aemeasurable] at hv
  have hmean : (∫ x, gaussianPSDSupport d x ∂euclideanGaussianLaw (Fin d × Fin d)) =
      ∫ x, gaussianPSDSupportRaw d x ∂gaussianProductLaw (Fin d × Fin d) := by
    rw [euclideanGaussianLaw, integral_map
      (MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).measurable.aemeasurable
      (gaussianPSDSupport_continuous d).aestronglyMeasurable]
    rfl
  rw [hmean] at hv
  rw [euclideanGaussianLaw, integral_map
    (f := fun x => (gaussianPSDSupport d x -
      (∫ y, gaussianPSDSupportRaw d y ∂gaussianProductLaw (Fin d × Fin d)))^2)
    (MeasurableEquiv.toLp 2 ((Fin d × Fin d) → ℝ)).measurable.aemeasurable
    (by simpa using! (((gaussianPSDSupport_continuous d).sub continuous_const).pow 2).aestronglyMeasurable)] at hv
  exact hv

#print axioms gaussianPSDSupport_variance_le
#print axioms gaussianPSDSupport_mean_lower
#print axioms gaussianPSDSupportRaw_mean_lower
#print axioms gaussianPSDSupportRaw_centered_sq_le
end BMGeometry
