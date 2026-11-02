import GaussianWeightedBilinearMGF

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers GaussianEllipsoid
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- Exact determinant of the Gram perturbation in its orthonormal eigenbasis. -/
theorem gram_perturbation_det {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (t : ℝ) :
    LinearMap.det (LinearMap.id - (t^2) • (T.adjoint ∘L T).toLinearMap) =
      ∏ i, (1 - t^2 * gramEigenvalue T i) := by
  let b := (rightSingularBasis T).toBasis
  rw [← LinearMap.det_toMatrix b, map_sub, map_smul, LinearMap.toMatrix_id]
  have he : LinearMap.toMatrix b b (T.adjoint ∘L T).toLinearMap =
      Matrix.diagonal (gramEigenvalue T) := by
    convert (gramSymmetric T).toMatrix_eigenvectorBasis finrank_euclideanSpace_fin using 1 <;> rfl
  rw [he]
  have hd : (1 : Matrix (Fin q) (Fin q) ℝ) - (t^2) • Matrix.diagonal (gramEigenvalue T) =
      Matrix.diagonal (fun i => 1 - t^2 * gramEigenvalue T i) := by
    ext i j
    by_cases h : i=j <;> simp [Matrix.diagonal, h]
  rw [hd, Matrix.det_diagonal]

/-- Exact bilinear MGF on its strict finiteness domain. The real parameter may
have either sign. The proof first establishes a finite nonnegative integral. -/
theorem gaussian_bilinear_mgf_exact_det {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (t : ℝ) (hcap : t^2*‖T‖^2 < 1) :
    mgf (fun p : Euclid q × Euclid r => ⟪T p.1,p.2⟫_ℝ)
      ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) t =
      (Real.sqrt (LinearMap.det (LinearMap.id - (t^2) •
        (T.adjoint ∘L T).toLinearMap)))⁻¹ := by
  have hc : ∀ i, (t^2/2)*gramEigenvalue T i < 1/2 := by
    intro i
    have hi := mul_le_mul_of_nonneg_left (gramEigenvalue_bounds T i).2 (sq_nonneg t)
    nlinarith
  have hi := gaussian_operator_normsq_integrable T (t^2/2) hc
  have he : (∫⁻ p : Euclid q × Euclid r,
      ENNReal.ofReal (Real.exp (t*⟪T p.1,p.2⟫_ℝ))
      ∂(euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) =
      ENNReal.ofReal (∏ i, (Real.sqrt (1-t^2*gramEigenvalue T i))⁻¹) := by
    rw [lintegral_prod _ (by fun_prop)]
    simp_rw [euclidean_gaussian_linear_lintegral]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _),
      gaussian_operator_normsq_integral T (t^2/2) hc]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    congr 3
    ring
  have hprod : 0 ≤ ∏ i, (Real.sqrt (1-t^2*gramEigenvalue T i))⁻¹ := by positivity
  unfold mgf
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _) (by fun_prop), he,
    ENNReal.toReal_ofReal hprod, gram_perturbation_det,
    Real.sqrt_prod _ (fun i _ => by linarith [hc i]), Finset.prod_inv_distrib]

/-- Finite independent weighted pairs give the full product determinant formula. -/
theorem gaussian_weighted_bilinear_mgf_exact_det {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ i, (t*w i)^2*‖T‖^2 < 1) :
    mgf (fun X : ι → Euclid q × Euclid r => ∑ i,w i*⟪T (X i).1,(X i).2⟫_ℝ)
      (gaussianBilinearSampleLaw ι q r) t =
      ∏ i, (Real.sqrt (LinearMap.det (LinearMap.id - ((t*w i)^2) •
        (T.adjoint ∘L T).toLinearMap)))⁻¹ := by
  unfold mgf
  rw [gaussian_weighted_bilinear_integral_factorization]
  apply Finset.prod_congr rfl
  intro i _
  exact gaussian_bilinear_mgf_exact_det T (t*w i) (hcap i)

end GaussianEllipsoidCandidate

#print axioms GaussianEllipsoidCandidate.gram_perturbation_det
#print axioms GaussianEllipsoidCandidate.gaussian_bilinear_mgf_exact_det
#print axioms GaussianEllipsoidCandidate.gaussian_weighted_bilinear_mgf_exact_det
