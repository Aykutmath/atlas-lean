import SequentialProductLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension

noncomputable section
open MeasureTheory MeasureTheory.Measure Set

namespace GaussianMixedNormHelpers
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- General position of independent absolutely continuous rows. Every prefix
up to ambient dimension has full row rank almost surely. -/
theorem ae_linearIndependent_pi_of_absolutelyContinuous (μ ρ : Measure E)
    [SigmaFinite μ] [IsAddHaarMeasure ρ] (hμ : μ ≪ ρ)
    (n : ℕ) (hn : n ≤ Module.finrank ℝ E) :
    ∀ᵐ f ∂Measure.pi (fun _ : Fin n => μ), LinearIndependent ℝ f := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => linearIndependent_empty_type)
  | succ n ih =>
    have hprev := ih (by omega)
    have hsnoc := measurePreserving_finSnoc (fun _ : Fin (n + 1) => μ)
    have hm : MeasurableSet {f : Fin (n + 1) → E | LinearIndependent ℝ f} :=
      isOpen_setOf_linearIndependent.measurableSet
    rw [← hsnoc.map_eq]
    apply (ae_map_iff hsnoc.measurable.aemeasurable hm).mpr
    apply (ae_prod_iff_ae_ae (hm.preimage hsnoc.measurable)).mpr
    filter_upwards [hprev] with f hf
    have hproper : Submodule.span ℝ (Set.range f) ≠ ⊤ := by
      intro heq
      have hdim := finrank_le_of_span_eq_top heq
      simp only [Fintype.card_fin] at hdim
      omega
    have hnull : μ (Submodule.span ℝ (Set.range f) : Set E) = 0 :=
      hμ (addHaar_submodule ρ _ hproper)
    have havoid : ∀ᵐ x ∂μ, x ∉ Submodule.span ℝ (Set.range f) := by
      rw [ae_iff]
      simp only [not_not]
      change μ (Submodule.span ℝ (Set.range f) : Set E) = 0
      exact hnull
    filter_upwards [havoid] with x hx
    exact linearIndependent_fin_snoc.mpr ⟨hf, hx⟩

end GaussianMixedNormHelpers
