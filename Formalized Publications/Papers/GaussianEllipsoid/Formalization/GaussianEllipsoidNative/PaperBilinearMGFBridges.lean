import PaperBilinearDeterminantMGF
import UCProjectSpectralPeeling
import IndependentConditionalBound
import PredictableGaussianBilinearMGF

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers GaussianEllipsoid BMGeometry
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- Matrix-coordinate bridge for I−t²ZZᵀ, preserving the order of the Gram factors. -/
theorem left_gram_determinant_matrix {h : ℕ} (T : Euclid h →L[ℝ] Euclid h) (t : ℝ) :
    LinearMap.det (LinearMap.id-(t^2) • (T ∘L T.adjoint).toLinearMap) =
      Matrix.det (1-(t^2) • (opMatrix T*(opMatrix T).transpose)) := by
  let b := (EuclideanSpace.basisFun (Fin h) ℝ).toBasis
  have ha : LinearMap.toMatrix b b T.adjoint.toLinearMap=(opMatrix T).transpose := by
    rw [← ContinuousLinearMap.adjoint_toLinearMap]
    simpa [b,opMatrix_eq_toMatrix] using
      LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin h) ℝ)
        (EuclideanSpace.basisFun (Fin h) ℝ) T.toLinearMap
  rw [← LinearMap.det_toMatrix b,map_sub,map_smul,LinearMap.toMatrix_id]
  have he : LinearMap.toMatrix b b (T ∘L T.adjoint).toLinearMap =
      opMatrix T*(opMatrix T).transpose := by
    change LinearMap.toMatrix b b (T.toLinearMap ∘ₗ T.adjoint.toLinearMap)=_
    rw [LinearMap.toMatrix_comp b b b,ha]
    rw [opMatrix_eq_toMatrix]
  rw [he]

theorem left_gram_determinant_pos {h : ℕ} (T : Euclid h →L[ℝ] Euclid h)
    (t : ℝ) (hcap : t^2*‖T‖^2 < 1) :
    0 < Matrix.det (1-(t^2) • (opMatrix T*(opMatrix T).transpose)) := by
  rw [← left_gram_determinant_matrix]
  have hdet := gram_perturbation_det T.adjoint t
  simp only [ContinuousLinearMap.adjoint_adjoint] at hdet
  rw [hdet]
  apply Finset.prod_pos
  intro i _
  have hb := mul_le_mul_of_nonneg_left (gramEigenvalue_bounds T.adjoint i).2 (sq_nonneg t)
  have hb' : t^2*gramEigenvalue T.adjoint i ≤ t^2*‖T‖^2 := by simpa using hb
  linarith

/-- Literal determinant MGF with the source's aᵀZb observable and ZZᵀ determinant.
The strict finite-MGF domain is explicit; both signs of t are allowed. -/
theorem paper_gaussian_bilinear_mgf {h : ℕ} (T : Euclid h →L[ℝ] Euclid h)
    (t : ℝ) (hcap : |t| *matrixOpNorm (opMatrix T)<1) :
    (∫ p : Euclid h × Euclid h, Real.exp (t*⟪p.1,T p.2⟫_ℝ)
      ∂(euclideanGaussianLaw (Fin h)).prod (euclideanGaussianLaw (Fin h))) =
      (Matrix.det (1-(t^2) • (opMatrix T*(opMatrix T).transpose)))^(-1/2:ℝ) := by
  rw [UCEscape.matrixOpNorm_opMatrix] at hcap
  have hc : t^2*‖T‖^2<1 := by
    have hs := (sq_lt_sq₀ (by positivity : 0 ≤ |t| *‖T‖) (by norm_num : (0:ℝ) ≤ 1)).mpr hcap
    simpa only [mul_pow,sq_abs,one_pow] using hs
  have h := gaussian_bilinear_mgf_exact_det T.adjoint t (by simpa using hc)
  simp only [mgf,ContinuousLinearMap.adjoint_inner_left,ContinuousLinearMap.adjoint_adjoint] at h
  rw [left_gram_determinant_matrix] at h
  rw [show (-1/2:ℝ)=-(1/2) by ring,Real.rpow_neg (left_gram_determinant_pos T t hc).le,
    ← Real.sqrt_eq_rpow]
  exact h

#print axioms paper_gaussian_bilinear_mgf
end GaussianEllipsoidCandidate


noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace GaussianConditionalBound
variable {Ω P D : Type*} [MeasurableSpace P] [MeasurableSpace D]

/-- Exact conditioning identity for a nonnegative measurable kernel and an
independent driver, on any probability space and sub-sigma-field. -/
theorem condLExp_independent_kernel
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (Z : Ω → P) (X : Ω → D) (hZ : Measurable[m] Z) (hX : Measurable X)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (f : P × D → ℝ≥0∞) (hf : Measurable f) :
    μ⁻[fun ω => f (Z ω,X ω) | m] =ᵐ[μ]
      fun ω => ∫⁻ y, f (Z ω,y) ∂μ.map X := by
  have hZm : Measurable Z := hZ.mono hm le_rfl
  have hsec : Measurable (fun p : P => ∫⁻ y,f (p,y) ∂μ.map X) := hf.lintegral_prod_right'
  apply (ae_eq_condLExp (hm := hm) μ (fun ω => f (Z ω,X ω)) (hsec.comp hZ) ?_).symm
  intro A hA
  calc
    _ = ∫⁻ p : P, ∫⁻ y, f (p,y) ∂μ.map X ∂(μ.restrict A).map Z := by
      simpa only [Function.comp_def] using (lintegral_map (μ := μ.restrict A) hsec hZm).symm
    _ = ∫⁻ p, f p ∂((μ.restrict A).map Z).prod (μ.map X) :=
      (lintegral_prod _ hf.aemeasurable).symm
    _ = _ := by
      rw [← restricted_joint_map_eq_product m μ hm Z X hZ hX hind hA,
        lintegral_map hf (hZm.prodMk hX)]

/-- Uniform section bounds give a finite unconditional integral, with actual
independence transport rather than an integrability premise. -/
theorem lintegral_independent_kernel_le
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (Z : Ω → P) (X : Ω → D) (hZ : Measurable[m] Z) (hX : Measurable X)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (f : P × D → ℝ≥0∞) (hf : Measurable f) (c : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂μ, (∫⁻ y,f (Z ω,y) ∂μ.map X) ≤ c) :
    (∫⁻ ω,f (Z ω,X ω) ∂μ) ≤ c := by
  have he := condLExp_independent_kernel m μ hm Z X hZ hX hind f hf
  rw [← lintegral_condLExp hm μ (fun ω => f (Z ω,X ω)),lintegral_congr_ae he]
  simpa using lintegral_mono_ae hbound

/-- Real conditional expectation bridge for a nonnegative kernel with finite
total expectation. Individual section integrability is not assumed. -/
theorem condExp_independent_nonnegative_kernel
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (Z : Ω → P) (X : Ω → D) (hZ : Measurable[m] Z) (hX : Measurable X)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (f : P × D → ℝ) (hf : Measurable f) (hf0 : ∀ p,0 ≤ f p)
    (hfinite : (∫⁻ ω,ENNReal.ofReal (f (Z ω,X ω)) ∂μ) ≠ ∞) :
    μ[fun ω => f (Z ω,X ω) | m] =ᵐ[μ]
      fun ω => ∫ y,f (Z ω,y) ∂μ.map X := by
  have hZm : Measurable Z := hZ.mono hm le_rfl
  have he := condLExp_independent_kernel m μ hm Z X hZ hX hind
    (fun p => ENNReal.ofReal (f p)) hf.ennreal_ofReal
  have ht := toReal_condLExp m (hf.ennreal_ofReal.comp (hZm.prodMk hX)).aemeasurable hfinite
  have hreal : (fun ω => (ENNReal.ofReal (f (Z ω,X ω))).toReal)=fun ω => f (Z ω,X ω) := by
    funext ω
    exact ENNReal.toReal_ofReal (hf0 _)
  dsimp only [Function.comp_def] at ht
  rw [hreal] at ht
  filter_upwards [he,ht] with ω heω htω
  rw [heω] at htω
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => hf0 (Z ω,y))
    ((hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)]
  exact htω.symm

#print axioms condExp_independent_nonnegative_kernel
end GaussianConditionalBound


noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers GaussianEllipsoid
open scoped BigOperators ENNReal InnerProductSpace
namespace GaussianEllipsoidCandidate

/-- Uniform Frobenius control follows from the actual Gram spectrum. -/
theorem contraction_frobenius_sq_le_dimension {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (hT : ‖T‖ ≤ 1) : ‖operatorFrobenius T‖^2 ≤ q := by
  rw [← sum_gramEigenvalue]
  have hn : ‖T‖^2 ≤ 1 := by nlinarith [norm_nonneg T]
  calc
    ∑ i,gramEigenvalue T i ≤ ∑ _i : Fin q,(1:ℝ) :=
      Finset.sum_le_sum fun i _ => (gramEigenvalue_bounds T i).2.trans hn
    _ = _ := by simp

/-- Genuine real conditional determinant-MGF identity for any measurable past
contraction and an independent current Gaussian block. Integrability is proved,
not added as a premise. The displayed 1/sqrt2 radius covers both signs of t. -/
theorem conditional_gaussian_bilinear_mgf_exact
    {Ω ι : Type*} [Fintype ι] {r q : ℕ}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable[m] W)
    (hWnorm : ∀ ω,‖W ω‖ ≤ 1)
    (X : Ω → (ι → Euclid q × Euclid r)) (hX : Measurable X)
    (hLaw : μ.map X=gaussianBilinearSampleLaw ι q r)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (w : ι → ℝ) (t : ℝ) (hcap : ∀ i,(t*w i)^2 ≤ 1/2) :
    μ[fun ω => Real.exp (t*∑ i,w i*⟪W ω (X ω i).1,(X ω i).2⟫_ℝ) | m] =ᵐ[μ]
      fun ω => ∏ i,(Real.sqrt (LinearMap.det (LinearMap.id-((t*w i)^2) •
        ((W ω).adjoint ∘L W ω).toLinearMap)))⁻¹ := by
  let f : ((Euclid q →L[ℝ] Euclid r) × (ι → Euclid q × Euclid r)) → ℝ :=
    fun p => Real.exp (t*∑ i,w i*⟪p.1 (p.2 i).1,(p.2 i).2⟫_ℝ)
  have hf : Measurable f := by
    exact ((measurable_predictable_bilinear_cluster (fun T : Euclid q →L[ℝ] Euclid r => T)
      measurable_id w).const_mul t).exp
  have hcap' (ω) (i) : (t*w i)^2*‖W ω‖^2 ≤ 1/2 := by
    have hn : ‖W ω‖^2 ≤ 1 := by nlinarith [hWnorm ω,norm_nonneg (W ω)]
    exact (mul_le_mul_of_nonneg_left hn (sq_nonneg (t*w i))).trans (by simpa using hcap i)
  let c := ENNReal.ofReal (Real.exp (t^2*(∑ i,(w i)^2)*(q:ℝ)))
  have hsec (ω) : (∫⁻ y,ENNReal.ofReal (f (W ω,y)) ∂μ.map X) ≤ c := by
    rw [hLaw]
    have hh := gaussian_weighted_bilinear_lintegral_le (W ω) w t (hcap' ω)
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (contraction_frobenius_sq_le_dimension (W ω) (hWnorm ω))
      (by positivity)
  have htotal := GaussianConditionalBound.lintegral_independent_kernel_le m μ hm W X hW hX hind
    (fun p => ENNReal.ofReal (f p)) hf.ennreal_ofReal c (Filter.Eventually.of_forall hsec)
  have hfinite : (∫⁻ ω,ENNReal.ofReal (f (W ω,X ω)) ∂μ) ≠ ∞ :=
    ne_of_lt (htotal.trans_lt ENNReal.ofReal_lt_top)
  have he := GaussianConditionalBound.condExp_independent_nonnegative_kernel m μ hm W X hW hX hind
    f hf (fun _ => Real.exp_nonneg _) hfinite
  filter_upwards [he] with ω hω
  rw [hLaw] at hω
  apply hω.trans
  exact gaussian_weighted_bilinear_mgf_exact_det (W ω) w t (fun i => lt_of_le_of_lt (hcap' ω i) (by norm_num))

/-- Positivity of the exact Gram determinant throughout the strict convergence domain. -/
theorem gram_determinant_pos {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (t : ℝ) (hcap : t^2*‖T‖^2<1) :
    0 < LinearMap.det (LinearMap.id-(t^2) • (T.adjoint ∘L T).toLinearMap) := by
  rw [gram_perturbation_det]
  apply Finset.prod_pos
  intro i _
  have h := mul_le_mul_of_nonneg_left (gramEigenvalue_bounds T i).2 (sq_nonneg t)
  linarith

theorem weighted_bilinear_lintegral_exact_det {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ i,(t*w i)^2*‖T‖^2<1) :
    (∫⁻ X : ι → Euclid q × Euclid r,
      ENNReal.ofReal (Real.exp (t*∑ i,w i*⟪T (X i).1,(X i).2⟫_ℝ))
        ∂gaussianBilinearSampleLaw ι q r) =
      ENNReal.ofReal (∏ i,(Real.sqrt (LinearMap.det (LinearMap.id-((t*w i)^2) •
        (T.adjoint ∘L T).toLinearMap)))⁻¹) := by
  have he := gaussian_weighted_bilinear_mgf_exact_det T w t hcap
  have hp : 0 < mgf (fun X : ι → Euclid q × Euclid r =>
      ∑ i,w i*⟪T (X i).1,(X i).2⟫_ℝ) (gaussianBilinearSampleLaw ι q r) t := by
    rw [he]
    exact Finset.prod_pos fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (gram_determinant_pos T (t*w i) (hcap i)))
  have hi := mgf_pos_iff.mp hp
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun X => Real.exp_nonneg _)]
  exact congrArg ENNReal.ofReal he

/-- Exact nonnegative conditional MGF on its full pointwise finite domain.
This remains valid even when the unconditional exponential is not integrable. -/
theorem conditional_bilinear_extended_mgf_exact
    {Ω ι : Type*} [Fintype ι] {r q : ℕ}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable[m] W)
    (X : Ω → (ι → Euclid q × Euclid r)) (hX : Measurable X)
    (hLaw : μ.map X=gaussianBilinearSampleLaw ι q r)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ᵐ ω ∂μ,∀ i,(t*w i)^2*‖W ω‖^2<1) :
    μ⁻[fun ω => ENNReal.ofReal (Real.exp (t*∑ i,w i*⟪W ω (X ω i).1,(X ω i).2⟫_ℝ)) | m] =ᵐ[μ]
      fun ω => ENNReal.ofReal (∏ i,(Real.sqrt (LinearMap.det (LinearMap.id-((t*w i)^2) •
        ((W ω).adjoint ∘L W ω).toLinearMap)))⁻¹) := by
  let f : ((Euclid q →L[ℝ] Euclid r) × (ι → Euclid q × Euclid r)) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal (Real.exp (t*∑ i,w i*⟪p.1 (p.2 i).1,(p.2 i).2⟫_ℝ))
  have hf : Measurable f :=
    (((measurable_predictable_bilinear_cluster (fun T : Euclid q →L[ℝ] Euclid r => T)
      measurable_id w).const_mul t).exp).ennreal_ofReal
  have he := GaussianConditionalBound.condLExp_independent_kernel m μ hm W X hW hX hind f hf
  filter_upwards [he,hcap] with ω hω hcω
  rw [hLaw] at hω
  exact hω.trans (weighted_bilinear_lintegral_exact_det (W ω) w t hcω)

/-- Exact conversion to the manuscript's ZZᵀ determinant and real negative half-power. -/
theorem adjoint_gram_inverse_sqrt_eq {h : ℕ} (T : Euclid h →L[ℝ] Euclid h)
    (t : ℝ) (hc : t^2*‖T‖^2<1) :
    (Real.sqrt (LinearMap.det (LinearMap.id-(t^2) •
      (T.adjoint.adjoint ∘L T.adjoint).toLinearMap)))⁻¹ =
      (Matrix.det (1-(t^2) • (opMatrix T*(opMatrix T).transpose)))^(-1/2:ℝ) := by
  rw [ContinuousLinearMap.adjoint_adjoint,left_gram_determinant_matrix,
    show (-1/2:ℝ)=-(1/2) by ring,Real.rpow_neg (left_gram_determinant_pos T t hc).le,
    ← Real.sqrt_eq_rpow]

/-- Literal matrix conditional determinant-MGF on the inherited finite-MGF domain. -/
theorem paper_conditional_matrix_extended_mgf
    {Ω ι : Type*} [Fintype ι] {h : ℕ}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (W : Ω → (Euclid h →L[ℝ] Euclid h)) (hW : Measurable[m] W)
    (X : Ω → (ι → Euclid h × Euclid h)) (hX : Measurable X)
    (hLaw : μ.map X=gaussianBilinearSampleLaw ι h h)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ᵐ ω ∂μ,∀ i,(t*w i)^2*‖W ω‖^2<1) :
    μ⁻[fun ω => ENNReal.ofReal (Real.exp (t*∑ i,w i*⟪(X ω i).1,W ω (X ω i).2⟫_ℝ)) | m] =ᵐ[μ]
      fun ω => ENNReal.ofReal (∏ i,(Matrix.det (1-((t*w i)^2) •
        (opMatrix (W ω)*(opMatrix (W ω)).transpose)))^(-1/2:ℝ)) := by
  have hWa : Measurable[m] (fun ω => (W ω).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.measurable.comp hW
  have hca : ∀ᵐ ω ∂μ,∀ i,(t*w i)^2*‖(W ω).adjoint‖^2<1 := by simpa using hcap
  have he := conditional_bilinear_extended_mgf_exact m μ hm (fun ω => (W ω).adjoint) hWa
    X hX hLaw hind w t hca
  simp only [ContinuousLinearMap.adjoint_inner_left] at he
  filter_upwards [he,hcap] with ω hω hcω
  apply hω.trans
  congr 1
  exact Finset.prod_congr rfl fun i _ => adjoint_gram_inverse_sqrt_eq (W ω) (t*w i) (hcω i)

#print axioms conditional_gaussian_bilinear_mgf_exact
#print axioms paper_conditional_matrix_extended_mgf
end GaussianEllipsoidCandidate
