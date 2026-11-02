import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner

/-! Reconstructed source, 2026-10-03. This is new text, not recovered original bytes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace GaussianConditionalBound
variable {Ω P D : Type*} [MeasurableSpace P] [MeasurableSpace D]

/-- Independence continues to factor the joint law after restriction to an event
in the conditioning sigma-field; the first marginal retains this restriction. -/
theorem restricted_joint_map_eq_product
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (Z : Ω → P) (X : Ω → D) (hZ : Measurable[m] Z) (hX : Measurable X)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (μ.restrict A).map (fun ω => (Z ω, X ω)) =
      ((μ.restrict A).map Z).prod (μ.map X) := by
  have hZm : Measurable Z := hZ.mono hm le_rfl
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (hZm.prodMk hX) (hs.prod ht), Measure.prod_prod,
    Measure.map_apply hZm hs, Measure.map_apply hX ht,
    Measure.restrict_apply (hs.preimage hZm),
    Measure.restrict_apply ((hs.prod ht).preimage (hZm.prodMk hX))]
  have hpre : (fun ω => (Z ω, X ω)) ⁻¹' (s ×ˢ t) ∩ A =
      (Z ⁻¹' s ∩ A) ∩ X ⁻¹' t := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_prod]
    exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩
  rw [hpre]
  exact (Indep_iff _ _ _).mp hind _ _ ((hZ hs).inter hA)
    (measurable_iff_comap_le.mpr le_rfl ht)

/-- Exact conditional indicator kernel, with no pointwise section-bound premise. -/
theorem condExp_event_eq
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (Z : Ω → P) (X : Ω → D) (hZ : Measurable[m] Z) (hX : Measurable X)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (S : Set (P × D)) (hS : MeasurableSet S) :
    μ[({ω | (Z ω,X ω) ∈ S}).indicator (1 : Ω → ℝ) | m] =ᵐ[μ]
      fun ω => (μ.map X).real {y | (Z ω,y) ∈ S} := by
  have hZm : Measurable Z := hZ.mono hm le_rfl
  let f : P × D → ℝ≥0∞ := S.indicator 1
  have hf : Measurable f := measurable_const.indicator hS
  have hsec : Measurable (fun p : P => ∫⁻ y, f (p,y) ∂μ.map X) := hf.lintegral_prod_right'
  have he : μ⁻[fun ω => f (Z ω,X ω) | m] =ᵐ[μ]
      fun ω => ∫⁻ y, f (Z ω,y) ∂μ.map X := by
    apply (ae_eq_condLExp (hm := hm) μ _ (hsec.comp hZ) ?_).symm
    intro A hA
    calc
      _ = ∫⁻ p : P, ∫⁻ y, f (p,y) ∂μ.map X ∂(μ.restrict A).map Z := by
        simpa only [Function.comp_def] using
          (lintegral_map (μ := μ.restrict A) hsec hZm).symm
      _ = ∫⁻ p, f p ∂((μ.restrict A).map Z).prod (μ.map X) :=
        (lintegral_prod _ hf.aemeasurable).symm
      _ = _ := by
        rw [← restricted_joint_map_eq_product m μ hm Z X hZ hX hind hA,
          lintegral_map hf (hZm.prodMk hX)]
  have hfinite : (∫⁻ ω, f (Z ω,X ω) ∂μ) ≠ ∞ := by
    apply ne_of_lt
    calc
      _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_mono (fun ω => by
        by_cases h : (Z ω,X ω) ∈ S <;> simp [f,h])
      _ < ∞ := by simp
  have ht := toReal_condLExp m (hf.comp (hZm.prodMk hX)).aemeasurable hfinite
  have hreal : (fun ω => (f (Z ω,X ω)).toReal) =
      ({ω | (Z ω,X ω) ∈ S}).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases h : (Z ω,X ω) ∈ S <;> simp [f,h]
  dsimp only [Function.comp_def] at ht
  rw [hreal] at ht
  filter_upwards [he,ht] with ω heω htω
  rw [heω] at htω
  have hs : MeasurableSet (Prod.mk (Z ω) ⁻¹' S) := hS.preimage measurable_prodMk_left
  have hs' : MeasurableSet {y : D | (Z ω,y) ∈ S} := hs
  simpa [f, Measure.real, ← Set.indicator_comp_right, Set.preimage, lintegral_indicator hs'] using htω.symm

/-- An almost-everywhere uniform section bound gives the same actual conditional
probability bound for arbitrary measurable coefficients and centers. -/
theorem condExp_event_le
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (Z : Ω → P) (X : Ω → D) (hZ : Measurable[m] Z) (hX : Measurable X)
    (hind : Indep m (MeasurableSpace.comap X inferInstance) μ)
    (S : Set (P × D)) (hS : MeasurableSet S) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, (μ.map X) {y | (Z ω,y) ∈ S} ≤ ENNReal.ofReal c) :
    μ[({ω | (Z ω,X ω) ∈ S}).indicator (1 : Ω → ℝ) | m] ≤ᵐ[μ] fun _ => c := by
  filter_upwards [condExp_event_eq m μ hm Z X hZ hX hind S hS,hbound] with ω he hb
  rw [he]
  exact ENNReal.toReal_le_of_le_ofReal hc hb

end GaussianConditionalBound

#print axioms GaussianConditionalBound.restricted_joint_map_eq_product
#print axioms GaussianConditionalBound.condExp_event_eq
#print axioms GaussianConditionalBound.condExp_event_le
