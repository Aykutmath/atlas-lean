import PaperGeneralRegularCluster
import ProjectedHeadProduct
import IndependentConditionalBound

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- Joint measurability includes random coefficients and both random projections. -/
theorem measurable_random_projectedBilinear {Ω : Type*} [MeasurableSpace Ω]
    {n h : ℕ} (d : ℕ) (P Q : Ω → Euclid h →L[ℝ] Euclid h)
    (u : Ω → Euclid n) (hP : Measurable P) (hQ : Measurable Q) (hu : Measurable u) :
    Measurable (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      projectedBilinear (P p.1) (Q p.1) n d p.2 (u p.1)) := by
  let f : Ω × (GaussianEntries n h × GaussianEntries n h) → (Fin h × Fin h → ℝ) :=
    fun p ab => (Real.sqrt d)⁻¹ * ∑ i, u p.1 i * (p.2.1 (i,ab.1)*p.2.2 (i,ab.2))
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro ab
    unfold f
    fun_prop
  have he : (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      gaussianBilinearOperator n h d p.2 (u p.1)) =
      (frobeniusEquivEuclidean h h).symm ∘ (MeasurableEquiv.toLp 2 ((Fin h × Fin h) → ℝ)) ∘ f := by
    funext p
    apply (frobeniusEquivEuclidean h h).injective
    ext ab
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply,
      frobeniusEquivEuclidean_apply, PiLp.toLp_apply]
    exact gaussianBilinearOperator_apply n h d p.2 (u p.1) ab.1 ab.2
  have hB : Measurable (fun p : Ω × (GaussianEntries n h × GaussianEntries n h) =>
      frobeniusOperator (gaussianBilinearOperator n h d p.2 (u p.1))) := by
    apply (continuous_frobeniusOperator h h).measurable.comp
    rw [he]
    exact (frobeniusEquivEuclidean h h).symm.continuous.measurable.comp
      ((MeasurableEquiv.toLp 2 ((Fin h × Fin h) → ℝ)).measurable.comp hf)
  apply (continuous_operatorFrobenius h h).measurable.comp
  have hc : Continuous (fun p : (Euclid h →L[ℝ] Euclid h) × (Euclid h →L[ℝ] Euclid h) =>
      p.1 ∘L p.2) := by fun_prop
  exact hc.measurable.comp ((hP.comp measurable_fst).prodMk
    (hc.measurable.comp (hB.prodMk (hQ.comp measurable_fst))))

/-- Full conditional regular-cluster bound with random coefficients, mass,
effective support and residual spaces. No measurable basis selection is assumed. -/
theorem projected_regular_cluster_general_conditional
    {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) {n h d : ℕ} (hd2 : 2 ≤ d)
    (G : Ω → GaussianEntries n h × GaussianEntries n h) (hG : Measurable G)
    (hLaw : μ.map G = tensorGaussianLaw n h)
    (hind : Indep m (MeasurableSpace.comap G inferInstance) μ)
    (P Q : Ω → Euclid h →L[ℝ] Euclid h) (hP : Measurable[m] P) (hQ : Measurable[m] Q)
    (hproj : ∀ᵐ ω ∂μ, ∃ W Z : Submodule ℝ (Euclid h),
      P ω = W.subtypeL ∘L W.orthogonalProjection ∧ Q ω = Z.subtypeL ∘L Z.orthogonalProjection ∧
      c*(d:ℝ) ≤ finrank ℝ W ∧ c*(d:ℝ) ≤ finrank ℝ Z)
    (u : Ω → Euclid n) (σ mass R : Ω → ℝ)
    (hu : Measurable[m] u) (hσ : Measurable[m] σ) (hmass : Measurable[m] mass) (hR : Measurable[m] R)
    (hdata : ∀ᵐ ω ∂μ, 0 < σ ω ∧ (∑ i, (u ω i)^2 = (σ ω)^2) ∧
      mass ω = ∑ i, |u ω i| ∧ R ω = (mass ω)^2/(σ ω)^2 ∧
      generalLow C * Real.log (d:ℝ) ≤ R ω ∧ R ω ≤ generalUp c C*(d:ℝ) ∧
      ∀ i, |u ω i| ≤ C*σ ω/Real.sqrt (R ω)) :
    μ[({ω | spectralNuclearNorm (projectedBilinear (P ω) (Q ω) n d (G ω) (u ω)) <
      generalProj c C * Real.sqrt d * mass ω}).indicator (1 : Ω → ℝ) | m] ≤ᵐ[μ]
      fun ω => Real.exp (-generalProj c C * (d:ℝ) * R ω) := by
  let A := (Euclid h →L[ℝ] Euclid h) × (Euclid h →L[ℝ] Euclid h) × Euclid n × ℝ
  let Z : Ω → A := fun ω => (P ω,Q ω,u ω,mass ω)
  let S : Set (A × (GaussianEntries n h × GaussianEntries n h)) :=
    {p | spectralNuclearNorm (projectedBilinear p.1.1 p.1.2.1 n d p.2 p.1.2.2.1) <
      generalProj c C * Real.sqrt d * p.1.2.2.2}
  have hS : MeasurableSet S := by
    apply measurableSet_lt
    · exact (continuous_spectralNuclear h h).measurable.comp
        (measurable_random_projectedBilinear d (fun a : A => a.1) (fun a : A => a.2.1)
          (fun a : A => a.2.2.1) measurable_fst
          (measurable_fst.comp measurable_snd)
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    · exact (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).const_mul _
  have he := GaussianConditionalBound.condExp_event_eq m μ hm Z G
    (hP.prodMk (hQ.prodMk (hu.prodMk hmass))) hG hind S hS
  filter_upwards [he,hproj,hdata] with ω heω hp hd
  dsimp [Z,S] at heω
  rw [heω,hLaw]
  rcases hp with ⟨W,V,hPW,hQV,hW,hV⟩
  rcases hd with ⟨hσ0,hsum,hmass0,hRdef,hlow,hupp,hcap⟩
  apply ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
  change tensorGaussianLaw n h {z | spectralNuclearNorm
    (projectedBilinear (P ω) (Q ω) n d z (u ω)) < generalProj c C*Real.sqrt d*mass ω} ≤ _
  rw [hPW,hQV]
  exact projected_regular_cluster_general hc hC hd2 W V hW hV (u ω)
    hσ0 hsum hmass0 hRdef hlow hupp hcap

end GaussianEllipsoid.ProjectedClusters

#print axioms GaussianEllipsoid.ProjectedClusters.projected_regular_cluster_general_conditional
