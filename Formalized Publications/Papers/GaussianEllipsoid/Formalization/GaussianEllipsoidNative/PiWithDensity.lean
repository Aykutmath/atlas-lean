import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
namespace GaussianProductDensity

/-- The finite product of measures with nonnegative integrable real densities
has the product density. This is an equality of the actual measures. -/
theorem pi_withDensity_ofReal {ι : Type*} [Fintype ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, E i → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ∀ i, E i => ∏ i, f i (x i))
      (Measure.pi (fun i => (μ i).restrict (s i))) := by
    exact Integrable.fintype_prod_dep (fun i => (hf i).restrict)
  have hi : (∫ x : ∀ i, E i, ∏ i, f i (x i)
      ∂Measure.pi (fun i => (μ i).restrict (s i))) =
        ∏ i, ∫ x in s i, f i x ∂μ i := by
    exact integral_fintype_prod_eq_prod f
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal hp (ae_of_all _ (fun x =>
    Finset.prod_nonneg (fun i _ => hn i (x i)))), hi]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict
    (ae_of_all _ (hn i))

#print axioms pi_withDensity_ofReal
end GaussianProductDensity
