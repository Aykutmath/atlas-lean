import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace GaussianProductDensity

/-- A measure-preserving map transports a pulled-back measurable density. -/
theorem map_withDensity_comp {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {μ : Measure E} {ν : Measure F} {e : E → F}
    (he : MeasurePreserving e μ ν) (f : F → ℝ≥0∞) (hf : Measurable f) :
    Measure.map e (μ.withDensity (fun x => f (e x))) = ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply he.measurable hs,
    withDensity_apply _ (he.measurable hs), withDensity_apply _ hs]
  exact he.setLIntegral_comp_preimage hs hf

/-- Orthogonal changes of coordinates preserve every measurable radial
Lebesgue density, in arbitrary finite-dimensional real Hilbert spaces. -/
theorem radial_density_isometry {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    Measure.map e ((volume : Measure E).withDensity (fun x => f ‖x‖)) =
      (volume : Measure F).withDensity (fun x => f ‖x‖) := by
  simpa only [e.norm_map] using
    map_withDensity_comp e.measurePreserving (fun x => f ‖x‖)
      (hf.comp measurable_norm)

#print axioms map_withDensity_comp
#print axioms radial_density_isometry
end GaussianProductDensity
