import PaperBilinearMGFBridges
import GaussianSelectedSigmaField
import GaussianExtractedRowsLaw

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoid GaussianEllipsoid.ProjectedClusters BMGeometry
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- The manuscript's (a,b) row order, extracted from literal independent scalar Gaussian arrays. -/
def sourceDriverRows {N n h : ℕ} (e : Fin n ↪ Fin N)
    (z : GaussianEntries N h × GaussianEntries N h) : Fin n → Euclid h × Euclid h :=
  tensorToCanonicalRows n h (Prod.swap (selectSample e z))

theorem sourceDriverRows_preserving {N n h : ℕ} (e : Fin n ↪ Fin N) :
    MeasurePreserving (sourceDriverRows (h:=h) e) (tensorGaussianLaw N h)
      (gaussianBilinearSampleLaw (Fin n) h h) := by
  have hs : MeasurePreserving Prod.swap (tensorGaussianLaw n h) (tensorGaussianLaw n h) :=
    ⟨measurable_swap,Measure.prod_swap⟩
  exact (tensorToCanonicalRows_preserving n h).comp (hs.comp (selectSample_preserving e))

theorem sourceDriverRows_coordinates {N n h : ℕ} (e : Fin n ↪ Fin N)
    (z : GaussianEntries N h × GaussianEntries N h) (i : Fin n) :
    sourceDriverRows e z i =
      (entriesToRows n h (selectEntries e z.1) i,
        entriesToRows n h (selectEntries e z.2) i) := rfl

theorem sourceDriverRows_indep {N p n h : ℕ}
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j) :
    Indep (selectedSampleSigmaField (h:=h) eA)
      (MeasurableSpace.comap (sourceDriverRows (h:=h) eS) inferInstance)
      (tensorGaussianLaw N h) := by
  have hi := (selectSample_indepFun (h:=h) eA eS hdisj).comp measurable_id
    ((tensorToCanonicalRows_preserving n h).measurable.comp measurable_swap)
  exact (IndepFun_iff_Indep _ _ _).mp hi

/-- Literal normalized determinant identity on the actual Gaussian sample space.
The past sigma-field, current samples, their independence, and their Gaussian law
are concrete. The only measurability premise is that the witness is predictable.
The strict finite-MGF domain is inherited from the preceding manuscript display. -/
theorem paper_actual_conditional_matrix_mgf {N p n h d : ℕ} (hd : 0 < d)
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j)
    (W : (GaussianEntries N h × GaussianEntries N h) → (Euclid h →L[ℝ] Euclid h))
    (hW : Measurable[selectedSampleSigmaField eA] W)
    (v : Fin n → ℝ) (t : ℝ)
    (hcap : ∀ᵐ z ∂tensorGaussianLaw N h,∀ i,
      (t*(v i/Real.sqrt (d:ℝ)))^2*‖W z‖^2<1) :
    (tensorGaussianLaw N h)⁻[fun z => ENNReal.ofReal (Real.exp
      (t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ)) | selectedSampleSigmaField eA] =ᵐ[tensorGaussianLaw N h]
      fun z => ENNReal.ofReal (∏ i,(Matrix.det (1-(t^2*(v i)^2/(d:ℝ)) •
        (opMatrix (W z)*(opMatrix (W z)).transpose)))^(-1/2:ℝ)) := by
  have he := paper_conditional_matrix_extended_mgf (selectedSampleSigmaField eA)
    (tensorGaussianLaw N h) (selectedSampleSigmaField_le eA) W hW
    (sourceDriverRows eS) (sourceDriverRows_preserving eS).measurable
    (sourceDriverRows_preserving eS).map_eq (sourceDriverRows_indep eA eS hdisj)
    (fun i => v i/Real.sqrt (d:ℝ)) t hcap
  have hcoeff (i : Fin n) : (t*(v i/Real.sqrt (d:ℝ)))^2=t^2*(v i)^2/(d:ℝ) := by
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity)]
    ring
  have hobs (z : GaussianEntries N h × GaussianEntries N h) :
      t*∑ i,(v i/Real.sqrt (d:ℝ))*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ =
      t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    ring
  simpa only [hcoeff,hobs] using he

/-- Pointwise spectral half-radius with a predictable contraction gives actual
real conditional expectation, including when coefficient magnitudes alone are
outside the coarser uniform radius. -/
theorem conditional_gaussian_bilinear_mgf_pointwise
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
    μ[fun ω => Real.exp (t*∑ i,w i*⟪W ω (X ω i).1,(X ω i).2⟫_ℝ) | m] =ᵐ[μ]
      fun ω => ∏ i,(Real.sqrt (LinearMap.det (LinearMap.id-((t*w i)^2) •
        ((W ω).adjoint ∘L W ω).toLinearMap)))⁻¹ := by
  let f : ((Euclid q →L[ℝ] Euclid r) × (ι → Euclid q × Euclid r)) → ℝ :=
    fun p => Real.exp (t*∑ i,w i*⟪p.1 (p.2 i).1,(p.2 i).2⟫_ℝ)
  have hf : Measurable f := ((measurable_predictable_bilinear_cluster
    (fun T : Euclid q →L[ℝ] Euclid r => T) measurable_id w).const_mul t).exp
  let c := ENNReal.ofReal (Real.exp (t^2*(∑ i,(w i)^2)*(q:ℝ)))
  have hsec : ∀ᵐ ω ∂μ,(∫⁻ y,ENNReal.ofReal (f (W ω,y)) ∂μ.map X) ≤ c := by
    filter_upwards [hcap] with ω hc
    rw [hLaw]
    apply (gaussian_weighted_bilinear_lintegral_le (W ω) w t hc).trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (contraction_frobenius_sq_le_dimension (W ω) (hWnorm ω)) (by positivity)
  have htotal := GaussianConditionalBound.lintegral_independent_kernel_le m μ hm W X hW hX hind
    (fun p => ENNReal.ofReal (f p)) hf.ennreal_ofReal c hsec
  have he := GaussianConditionalBound.condExp_independent_nonnegative_kernel m μ hm W X hW hX hind
    f hf (fun _ => Real.exp_nonneg _) (ne_of_lt (htotal.trans_lt ENNReal.ofReal_lt_top))
  filter_upwards [he,hcap] with ω hω hc
  rw [hLaw] at hω
  exact hω.trans (gaussian_weighted_bilinear_mgf_exact_det (W ω) w t
    (fun i => lt_of_le_of_lt (hc i) (by norm_num)))

/-- Real-valued conditional-expectation version on the manuscript's uniform
half-radius regime. Global exponential integrability follows from the actual
Gaussian law and contraction bound, rather than being assumed. -/
theorem paper_actual_conditional_matrix_mgf_real {N p n h d : ℕ} (hd : 0 < d)
    (eA : Fin p ↪ Fin N) (eS : Fin n ↪ Fin N) (hdisj : ∀ i j,eA i ≠ eS j)
    (W : (GaussianEntries N h × GaussianEntries N h) → (Euclid h →L[ℝ] Euclid h))
    (hW : Measurable[selectedSampleSigmaField eA] W) (hWnorm : ∀ z,‖W z‖ ≤ 1)
    (v : Fin n → ℝ) (t : ℝ)
    (hcap : ∀ᵐ z ∂tensorGaussianLaw N h,∀ i,
      (t*(v i/Real.sqrt (d:ℝ)))^2*‖W z‖^2 ≤ 1/2) :
    (tensorGaussianLaw N h)[fun z => Real.exp
      (t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ) | selectedSampleSigmaField eA] =ᵐ[tensorGaussianLaw N h]
      fun z => ∏ i,(Matrix.det (1-(t^2*(v i)^2/(d:ℝ)) •
        (opMatrix (W z)*(opMatrix (W z)).transpose)))^(-1/2:ℝ) := by
  have hWa : Measurable[selectedSampleSigmaField eA] (fun z => (W z).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.measurable.comp hW
  have hWna (z) : ‖(W z).adjoint‖ ≤ 1 := by simpa using hWnorm z
  have hca : ∀ᵐ z ∂tensorGaussianLaw N h,∀ i,
      (t*(v i/Real.sqrt (d:ℝ)))^2*‖(W z).adjoint‖^2 ≤ 1/2 := by simpa using hcap
  have he := conditional_gaussian_bilinear_mgf_pointwise (selectedSampleSigmaField eA)
    (tensorGaussianLaw N h) (selectedSampleSigmaField_le eA)
    (fun z => (W z).adjoint) hWa hWna
    (sourceDriverRows eS) (sourceDriverRows_preserving eS).measurable
    (sourceDriverRows_preserving eS).map_eq (sourceDriverRows_indep eA eS hdisj)
    (fun i => v i/Real.sqrt (d:ℝ)) t hca
  simp only [ContinuousLinearMap.adjoint_inner_left] at he
  have hcoeff (i : Fin n) : (t*(v i/Real.sqrt (d:ℝ)))^2=t^2*(v i)^2/(d:ℝ) := by
    rw [mul_pow,div_pow,Real.sq_sqrt (by positivity)]
    ring
  have hobs (z : GaussianEntries N h × GaussianEntries N h) :
      t*∑ i,(v i/Real.sqrt (d:ℝ))*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ =
      t/Real.sqrt (d:ℝ)*∑ i,v i*⟪(sourceDriverRows eS z i).1,
        W z (sourceDriverRows eS z i).2⟫_ℝ := by
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    ring
  simp only [hobs] at he
  filter_upwards [he,hcap] with z hz hcz
  apply hz.trans
  apply Finset.prod_congr rfl
  intro i _
  have hc : (t*(v i/Real.sqrt (d:ℝ)))^2*‖W z‖^2<1 := by
    exact lt_of_le_of_lt (hcz i) (by norm_num)
  simpa only [hcoeff] using adjoint_gram_inverse_sqrt_eq (W z) (t*(v i/Real.sqrt (d:ℝ))) hc

#print axioms paper_actual_conditional_matrix_mgf
#print axioms paper_actual_conditional_matrix_mgf_real
end GaussianEllipsoidCandidate
