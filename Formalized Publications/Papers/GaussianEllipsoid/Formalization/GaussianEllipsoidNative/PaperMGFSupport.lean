import PaperBilinearMGFBridges

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers GaussianEllipsoid BMGeometry
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- The squared spectral condition in the internal kernel is exactly the source's
absolute-value strict convergence condition, for both signs of the MGF parameter. -/
theorem spectral_mgf_domain_iff {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (t : ℝ) :
    t^2*‖T‖^2<1 ↔ |t| *‖T‖<1 := by
  have h := sq_lt_sq₀ (by positivity : 0 ≤ |t| *‖T‖) (by norm_num : (0:ℝ) ≤ 1)
  simpa only [mul_pow,sq_abs,one_pow] using h

/-- The product over every index equals the manuscript's product over support;
zero coefficients contribute exactly one, including an empty support. -/
theorem matrix_mgf_product_eq_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℕ} (T : Euclid h →L[ℝ] Euclid h) (v : ι → ℝ) (t d : ℝ) :
    (∏ i,(Matrix.det (1-(t^2*(v i)^2/d) •
      (opMatrix T*(opMatrix T).transpose)))^(-1/2:ℝ)) =
    ∏ i ∈ Finset.univ.filter (fun i => v i ≠ 0),
      (Matrix.det (1-(t^2*(v i)^2/d) •
        (opMatrix T*(opMatrix T).transpose)))^(-1/2:ℝ) := by
  classical
  symm
  apply Finset.prod_subset (Finset.filter_subset _ _)
  intro i hi hn
  have hv : v i = 0 := by simpa using hn
  simp [hv]

/-- The corresponding weighted bilinear sum can use literal support without
changing the random variable or its normalization. -/
theorem weighted_sum_eq_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v g : ι → ℝ) :
    (∑ i,v i*g i)=∑ i ∈ Finset.univ.filter (fun i => v i ≠ 0),v i*g i := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hn
  have hv : v i=0 := by simpa using hn
  simp [hv]

#print axioms spectral_mgf_domain_iff
#print axioms weighted_sum_eq_support
#print axioms matrix_mgf_product_eq_support
end GaussianEllipsoidCandidate
