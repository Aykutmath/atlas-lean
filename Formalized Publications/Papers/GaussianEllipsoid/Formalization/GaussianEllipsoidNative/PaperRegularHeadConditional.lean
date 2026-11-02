import PaperGeneralClusterConditional
import GaussianSelectedSigmaField

noncomputable section
open MeasureTheory ProbabilityTheory Module
open GaussianMixedNormHelpers GaussianTensorMoments
open scoped BigOperators ENNReal
namespace GaussianEllipsoid.ProjectedClusters

/-- Literal head-span specialization on one actual Gaussian sample array.
The conditioning field contains exactly the disjoint head samples; the current
Gaussian driver is the selected disjoint subfamily, not the entire array. -/
theorem projected_regular_head_general_conditional
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) {N p n h d : ℕ} (hd2 : 2 ≤ d)
    (eH : Fin p ↪ Fin N) (eJ : Fin n ↪ Fin N) (hdisj : ∀ i j, eH i ≠ eJ j)
    (hbudget : c*(d:ℝ)+(p:ℝ) ≤ h)
    (u : Euclid n) {σ mass R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hmass : mass = ∑ i, |u i|)
    (hRdef : R = mass^2/σ^2)
    (hlow : generalLow C * Real.log (d:ℝ) ≤ R)
    (hupp : R ≤ generalUp c C*(d:ℝ))
    (hcap : ∀ i, |u i| ≤ C*σ/Real.sqrt R) :
    (tensorGaussianLaw N h)[({z | spectralNuclearNorm (projectedBilinear
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1))
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2))
      n d (selectSample eJ z) u) < generalProj c C * Real.sqrt d * mass}).indicator
      (1 : (GaussianEntries N h × GaussianEntries N h) → ℝ) | selectedSampleSigmaField eH] ≤ᵐ[tensorGaussianLaw N h]
        fun _ => Real.exp (-generalProj c C * (d:ℝ) * R) := by
  let P := fun z : GaussianEntries N h × GaussianEntries N h =>
    ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).1)
  let Q := fun z : GaussianEntries N h × GaussianEntries N h =>
    ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p h (selectSample eH z).2)
  have hHead := measurable_selectSample_own_sigma (h := h) eH
  have hP : Measurable[selectedSampleSigmaField eH] P :=
    measurable_const.sub ((measurable_finiteSpanProjector p).comp
      ((measurable_entriesToRows p h).comp (measurable_fst.comp hHead)))
  have hQ : Measurable[selectedSampleSigmaField eH] Q :=
    measurable_const.sub ((measurable_finiteSpanProjector p).comp
      ((measurable_entriesToRows p h).comp (measurable_snd.comp hHead)))
  have hproj : ∀ᵐ z ∂tensorGaussianLaw N h, ∃ W Z : Submodule ℝ (Euclid h),
      P z = W.subtypeL ∘L W.orthogonalProjection ∧
      Q z = Z.subtypeL ∘L Z.orthogonalProjection ∧
      c*(d:ℝ) ≤ finrank ℝ W ∧ c*(d:ℝ) ≤ finrank ℝ Z := by
    apply Filter.Eventually.of_forall
    intro z
    refine ⟨headResidual (entriesToRows p h (selectSample eH z).1),
      headResidual (entriesToRows p h (selectSample eH z).2),
      (headResidual_projector _).symm, (headResidual_projector _).symm, ?_, ?_⟩
    · have hr : (h:ℝ) ≤ p + finrank ℝ (headResidual (entriesToRows p h (selectSample eH z).1)) := by
        exact_mod_cast headResidual_rank_loss (entriesToRows p h (selectSample eH z).1)
      linarith
    · have hr : (h:ℝ) ≤ p + finrank ℝ (headResidual (entriesToRows p h (selectSample eH z).2)) := by
        exact_mod_cast headResidual_rank_loss (entriesToRows p h (selectSample eH z).2)
      linarith
  exact projected_regular_cluster_general_conditional (selectedSampleSigmaField eH)
    (tensorGaussianLaw N h) (selectedSampleSigmaField_le eH) hc hC hd2
    (selectSample eJ) (measurable_selectSample eJ) (selectSample_preserving eJ).map_eq
    (selectedSampleSigmaField_indep eH eJ hdisj) P Q hP hQ hproj
    (fun _ => u) (fun _ => σ) (fun _ => mass) (fun _ => R)
    measurable_const measurable_const measurable_const measurable_const
    (Filter.Eventually.of_forall fun _ => ⟨hσ,husum,hmass,hRdef,hlow,hupp,hcap⟩)

/-- The manuscript's h=floor(d/2) specialization, with finite edge cases
explicit: d=0 has an empty strict failure event; d=1 violates the positive
rank budget. No additional lower-dimension hypothesis is inserted. -/
theorem projected_regular_head_half_dimension_conditional
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C) {N p n d : ℕ}
    (eH : Fin p ↪ Fin N) (eJ : Fin n ↪ Fin N) (hdisj : ∀ i j, eH i ≠ eJ j)
    (hbudget : c*(d:ℝ)+(p:ℝ) ≤ (d/2:ℕ))
    (u : Euclid n) {σ mass R : ℝ} (hσ : 0 < σ)
    (husum : ∑ i, (u i)^2 = σ^2) (hmass : mass = ∑ i, |u i|)
    (hRdef : R = mass^2/σ^2)
    (hlow : generalLow C * Real.log (d:ℝ) ≤ R)
    (hupp : R ≤ generalUp c C*(d:ℝ))
    (hcap : ∀ i, |u i| ≤ C*σ/Real.sqrt R) :
    (tensorGaussianLaw N (d/2))[({z | spectralNuclearNorm (projectedBilinear
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p (d/2) (selectSample eH z).1))
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p (d/2) (selectSample eH z).2))
      n d (selectSample eJ z) u) < generalProj c C * Real.sqrt d * mass}).indicator
      (1 : (GaussianEntries N (d/2) × GaussianEntries N (d/2)) → ℝ) | selectedSampleSigmaField eH] ≤ᵐ[tensorGaussianLaw N (d/2)]
        fun _ => Real.exp (-generalProj c C * (d:ℝ) * R) := by
  by_cases hd0 : d = 0
  · subst d
    have hempty : {z : GaussianEntries N (0/2) × GaussianEntries N (0/2) |
        spectralNuclearNorm (projectedBilinear
          (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p (0/2) (selectSample eH z).1))
          (ContinuousLinearMap.id ℝ _ - finiteSpanProjector (entriesToRows p (0/2) (selectSample eH z).2))
          n 0 (selectSample eJ z) u) < generalProj c C * Real.sqrt 0 * mass} = ∅ := by
      ext z
      simp only [Real.sqrt_zero, mul_zero, zero_mul, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt_of_ge (spectralNuclear_nonneg _)
    simp only [Nat.cast_zero]
    rw [hempty]
    simp
    exact Filter.Eventually.of_forall (fun _ => zero_le_one)
  · have hd2 : 2 ≤ d := by
      by_contra h
      have hd1 : d = 1 := by omega
      subst d
      norm_num at hbudget
      have hp : (0:ℝ) ≤ p := Nat.cast_nonneg p
      linarith
    exact projected_regular_head_general_conditional hc hC hd2 eH eJ hdisj hbudget
      u hσ husum hmass hRdef hlow hupp hcap

#print axioms projected_regular_head_general_conditional
#print axioms projected_regular_head_half_dimension_conditional
end GaussianEllipsoid.ProjectedClusters
