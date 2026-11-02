import PaperMGFPairing
import PaperMGFSupport
import UCOrthogonalCompression

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid GaussianEllipsoid.ProjectedClusters BMGeometry
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- Real conditional MGF bound for an arbitrary predictable contraction and
independent Gaussian block. The global integrability needed by real conditional
expectation is proved by the imported pointwise identity, not assumed. -/
theorem conditional_gaussian_bilinear_mgf_le
    {Ω ι : Type*} [Fintype ι] {r q : ℕ}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable[m] W)
    (hWnorm : ∀ ω,‖W ω‖ ≤ 1)
    (X : Ω → (ι → Euclid q × Euclid r)) (hX : Measurable X)
    (hLaw : μ.map X=gaussianBilinearSampleLaw ι q r)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ᵐ ω ∂μ,∀ i,(t*w i)^2*‖W ω‖^2 ≤ 1/2) :
    μ[fun ω => Real.exp (t*∑ i,w i*⟪W ω (X ω i).1,(X ω i).2⟫_ℝ) | m] ≤ᵐ[μ]
      fun ω => Real.exp (t^2*(∑ i,(w i)^2)*‖operatorFrobenius (W ω)‖^2) := by
  have he := conditional_gaussian_bilinear_mgf_pointwise m μ hm W hW hWnorm X hX hLaw hind w t hcap
  filter_upwards [he,hcap] with ω hω hc
  rw [hω,← gaussian_weighted_bilinear_mgf_exact_det (W ω) w t
    (fun i => lt_of_le_of_lt (hc i) (by norm_num))]
  exact gaussian_weighted_bilinear_mgf_le (W ω) w t hc

/-- The manuscript's sup-norm radius implies the exact coefficientwise spectral
half-radius. The norm of the finite real function v is its supremum norm;
no sign restriction is imposed on t. -/
theorem source_supnorm_mgf_radius {ι : Type*} [Fintype ι] {r q d : ℕ}
    (hd : 0 < d) (v : ι → ℝ) (T : Euclid q →L[ℝ] Euclid r) (t : ℝ)
    (hcap : |t| *‖v‖*‖T‖/Real.sqrt (d:ℝ) ≤ 1/Real.sqrt 2) (i : ι) :
    (t*(v i/Real.sqrt (d:ℝ)))^2*‖T‖^2 ≤ 1/2 := by
  have hv : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hmono : |t| *|v i| *‖T‖/Real.sqrt (d:ℝ) ≤ |t| *‖v‖*‖T‖/Real.sqrt (d:ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (abs_nonneg t)) (norm_nonneg T))
      (Real.sqrt_nonneg _)
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ |t| *|v i| *‖T‖/Real.sqrt (d:ℝ))
    (by positivity : 0 ≤ 1/Real.sqrt 2)).mpr (hmono.trans hcap)
  have he : (|t| *|v i| *‖T‖/Real.sqrt (d:ℝ))^2 =
      (t*(v i/Real.sqrt (d:ℝ)))^2*‖T‖^2 := by
    simp only [div_pow,mul_pow,sq_abs]
    ring
  rw [he] at hs
  norm_num [div_pow,Real.sq_sqrt] at hs
  exact hs

/-- The literal t² Q ||Z||_F² / d conditional bound on the actual selected Gaussian
sample space. Its half-radius includes the operator norm pointwise, rather than
replacing it by its uniform contraction upper bound. -/
theorem paper_actual_conditional_matrix_mgf_le {N p n h d : ℕ} (hd : 0 < d)
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j)
    (W : (GaussianEntries N h × GaussianEntries N h) → (Euclid h →L[ℝ] Euclid h))
    (hW : Measurable[selectedSampleSigmaField eA] W) (hWnorm : ∀ z,‖W z‖ ≤ 1)
    (v : Fin n → ℝ) (t : ℝ)
    (hcap : ∀ᵐ z ∂tensorGaussianLaw N h,
      |t| *‖v‖*‖W z‖/Real.sqrt (d:ℝ) ≤ 1/Real.sqrt 2) :
    (tensorGaussianLaw N h)[fun z => Real.exp
      (t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ) | selectedSampleSigmaField eA] ≤ᵐ[tensorGaussianLaw N h]
      fun z => Real.exp (t^2*(∑ i,(v i)^2)*‖operatorFrobenius (W z)‖^2/(d:ℝ)) := by
  have hWa : Measurable[selectedSampleSigmaField eA] (fun z => (W z).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.measurable.comp hW
  have hWna (z) : ‖(W z).adjoint‖ ≤ 1 := by simpa using hWnorm z
  have hca : ∀ᵐ z ∂tensorGaussianLaw N h,∀ i,
      (t*(v i/Real.sqrt (d:ℝ)))^2*‖(W z).adjoint‖^2 ≤ 1/2 := by
    filter_upwards [hcap] with z hz
    intro i
    simpa using source_supnorm_mgf_radius hd v (W z) t hz i
  have he := conditional_gaussian_bilinear_mgf_le (selectedSampleSigmaField eA)
    (tensorGaussianLaw N h) (selectedSampleSigmaField_le eA)
    (fun z => (W z).adjoint) hWa hWna
    (sourceDriverRows eS) (sourceDriverRows_preserving eS).measurable
    (sourceDriverRows_preserving eS).map_eq (sourceDriverRows_indep eA eS hdisj)
    (fun i => v i/Real.sqrt (d:ℝ)) t hca
  simp only [ContinuousLinearMap.adjoint_inner_left,UCEscape.frobenius_norm_adjoint] at he
  have hobs (z : GaussianEntries N h × GaussianEntries N h) :
      t*∑ i,(v i/Real.sqrt (d:ℝ))*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ =
      t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    ring
  have henergy : (∑ i,(v i/Real.sqrt (d:ℝ))^2)=(∑ i,(v i)^2)/(d:ℝ) := by
    simp_rw [div_pow,Real.sq_sqrt (show (0:ℝ) ≤ d by positivity)]
    rw [Finset.sum_div]
  have hexp (z : GaussianEntries N h × GaussianEntries N h) :
      t^2*((∑ i,(v i)^2)/(d:ℝ))*‖operatorFrobenius (W z)‖^2 =
      t^2*(∑ i,(v i)^2)*‖operatorFrobenius (W z)‖^2/(d:ℝ) := by ring
  simpa only [hobs,henergy,hexp] using he

/-- The determinant identity with literal support and exactly the source's
sup-norm half-radius, expressed as genuine real conditional expectation. -/
theorem paper_actual_conditional_support_mgf {N p n h d : ℕ} (hd : 0 < d)
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j)
    (W : (GaussianEntries N h × GaussianEntries N h) → (Euclid h →L[ℝ] Euclid h))
    (hW : Measurable[selectedSampleSigmaField eA] W) (hWnorm : ∀ z,‖W z‖ ≤ 1)
    (v : Fin n → ℝ) (t : ℝ)
    (hcap : ∀ᵐ z ∂tensorGaussianLaw N h,
      |t| *‖v‖*‖W z‖/Real.sqrt (d:ℝ) ≤ 1/Real.sqrt 2) :
    (tensorGaussianLaw N h)[fun z => Real.exp
      (t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ) | selectedSampleSigmaField eA] =ᵐ[tensorGaussianLaw N h]
      fun z => ∏ i ∈ Finset.univ.filter (fun i => v i ≠ 0),
        (Matrix.det (1-(t^2*(v i)^2/(d:ℝ)) •
          (opMatrix (W z)*(opMatrix (W z)).transpose)))^(-1/2:ℝ) := by
  have hca : ∀ᵐ z ∂tensorGaussianLaw N h,∀ i,
      (t*(v i/Real.sqrt (d:ℝ)))^2*‖W z‖^2 ≤ 1/2 := by
    filter_upwards [hcap] with z hz
    exact source_supnorm_mgf_radius hd v (W z) t hz
  have he := paper_actual_conditional_matrix_mgf_real hd eA eS hdisj W hW hWnorm v t hca
  filter_upwards [he] with z hz
  exact hz.trans (matrix_mgf_product_eq_support (W z) v t (d:ℝ))

/-- The manuscript's actual Frobenius observable has the literal conditional
bound, with Q equal to the squared coefficient energy and both signs of t. -/
theorem paper_actual_frobenius_conditional_mgf_le {N p n h d : ℕ} (hd : 0 < d)
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j)
    (W : (GaussianEntries N h × GaussianEntries N h) → (Euclid h →L[ℝ] Euclid h))
    (hW : Measurable[selectedSampleSigmaField eA] W) (hWnorm : ∀ z,‖W z‖ ≤ 1)
    (v : Fin n → ℝ) (t : ℝ)
    (hcap : ∀ᵐ z ∂tensorGaussianLaw N h,
      |t| *‖v‖*‖W z‖/Real.sqrt (d:ℝ) ≤ 1/Real.sqrt 2) :
    (tensorGaussianLaw N h)[fun z => Real.exp
      (t*⟪operatorFrobenius (W z),gaussianBilinearOperator n h d (selectSample eS z)
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) v)⟫_ℝ) | selectedSampleSigmaField eA] ≤ᵐ[tensorGaussianLaw N h]
      fun z => Real.exp (t^2*(∑ i,(v i)^2)*‖operatorFrobenius (W z)‖^2/(d:ℝ)) := by
  have hscale (x : ℝ) : t*((Real.sqrt (d:ℝ))⁻¹*x)=t/Real.sqrt (d:ℝ)*x := by ring
  simp_rw [source_bilinear_pairing_eq,hscale]
  exact paper_actual_conditional_matrix_mgf_le hd eA eS hdisj W hW hWnorm v t hcap

/-- Literal source Frobenius pairing, support determinant product, ZZᵀ, d⁻¹
coefficient, and real conditional expectation under the displayed source radius. -/
theorem paper_actual_frobenius_conditional_support_mgf {N p n h d : ℕ} (hd : 0 < d)
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j)
    (W : (GaussianEntries N h × GaussianEntries N h) → (Euclid h →L[ℝ] Euclid h))
    (hW : Measurable[selectedSampleSigmaField eA] W) (hWnorm : ∀ z,‖W z‖ ≤ 1)
    (v : Fin n → ℝ) (t : ℝ)
    (hcap : ∀ᵐ z ∂tensorGaussianLaw N h,
      |t| *‖v‖*‖W z‖/Real.sqrt (d:ℝ) ≤ 1/Real.sqrt 2) :
    (tensorGaussianLaw N h)[fun z => Real.exp
      (t*⟪operatorFrobenius (W z),gaussianBilinearOperator n h d (selectSample eS z)
        ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ)) v)⟫_ℝ) | selectedSampleSigmaField eA] =ᵐ[tensorGaussianLaw N h]
      fun z => ∏ i ∈ Finset.univ.filter (fun i => v i ≠ 0),
        (Matrix.det (1-(t^2*(v i)^2/(d:ℝ)) •
          (opMatrix (W z)*(opMatrix (W z)).transpose)))^(-1/2:ℝ) := by
  have hscale (x : ℝ) : t*((Real.sqrt (d:ℝ))⁻¹*x)=t/Real.sqrt (d:ℝ)*x := by ring
  simp_rw [source_bilinear_pairing_eq,hscale]
  exact paper_actual_conditional_support_mgf hd eA eS hdisj W hW hWnorm v t hcap

#print axioms paper_actual_frobenius_conditional_mgf_le
#print axioms paper_actual_frobenius_conditional_support_mgf
#print axioms conditional_gaussian_bilinear_mgf_le
#print axioms source_supnorm_mgf_radius
#print axioms paper_actual_conditional_matrix_mgf_le
#print axioms paper_actual_conditional_support_mgf
end GaussianEllipsoidCandidate
