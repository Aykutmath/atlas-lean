import GaussianRadialMoments
import Mathlib.Probability.Independence.Basic

/-! Polar decomposition of the actual radial Gaussian measure.  Both factors
are explicit measures: normalized Haar surface measure and a radial density.
No independence or distributional hypothesis is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AHHRadial
open GaussianMixedNormHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := Metric.sphere (0 : E) 1
abbrev Radius := Set.Ioi (0 : ℝ)

/-- Normalized surface measure, with no project-specific surrogate distribution. -/
def sphereLaw (μ : Measure E) : Measure (UnitSphere E) :=
  (μ.toSphere Set.univ)⁻¹ • μ.toSphere

variable (μ : Measure E) [μ.IsAddHaarMeasure]

instance sphereLaw_probability : IsProbabilityMeasure (sphereLaw μ) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero μ))
    (measure_ne_top _ _)

def rawRadiusLaw (b : ℝ) : Measure Radius :=
  (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
    (fun r => ENNReal.ofReal ((radialGaussianMass μ b)⁻¹ * Real.exp (-b * (r : ℝ)^2)))

def radiusLaw (b : ℝ) : Measure Radius :=
  μ.toSphere Set.univ • rawRadiusLaw μ b

instance rawRadiusLaw_sfinite (b : ℝ) : SFinite (rawRadiusLaw μ b) := by
  unfold rawRadiusLaw
  infer_instance

instance radiusLaw_sfinite (b : ℝ) : SFinite (radiusLaw μ b) := by
  unfold radiusLaw
  infer_instance

/-- Reassemble the nonzero vector from its unit direction and positive radius. -/
def assemble (p : UnitSphere E × Radius) : E := (p.2 : ℝ) • (p.1 : E)

theorem measurable_assemble : Measurable (assemble (E := E)) := by
  unfold assemble
  fun_prop

@[simp] theorem norm_assemble (p : UnitSphere E × Radius) :
    ‖assemble p‖ = (p.2 : ℝ) := by
  rw [assemble, norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property,
    (mem_sphere_zero_iff_norm.mp p.1.property), mul_one]

/-- Density transport through a measure-preserving map. -/
theorem map_density {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {ρ : Measure β} {f : α → β}
    (hf : MeasurePreserving f ν ρ) {w : β → ℝ≥0∞} (hw : Measurable w) :
    (ν.withDensity (w ∘ f)).map f = ρ.withDensity w := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  exact hf.setLIntegral_comp_preimage hs hw

/-- Haar polar integration, including the null origin, as a measure identity. -/
theorem assemble_preserving_haar :
    MeasurePreserving (assemble (E := E))
      (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) μ := by
  have hc : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
      (μ.comap Subtype.val) μ := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton (0 : E)).compl]
    apply Measure.restrict_eq_self_of_ae_mem
    simp [ae_iff]
  have hp := (MeasurePreserving.symm (homeomorphUnitSphereProd E).toMeasurableEquiv
    (Measure.measurePreserving_homeomorphUnitSphereProd μ))
  exact hc.comp hp

/-- The exact unnormalized factorization furnished by polar coordinates. -/
theorem radialGaussianLaw_eq_map_raw (b : ℝ) :
    radialGaussianLaw μ b = (μ.toSphere.prod (rawRadiusLaw μ b)).map assemble := by
  rw [rawRadiusLaw, prod_withDensity_right (by fun_prop)]
  have he : (fun p : UnitSphere E × Radius => ENNReal.ofReal
      ((radialGaussianMass μ b)⁻¹ * Real.exp (-b * (p.2 : ℝ)^2))) =
      (fun x : E => ENNReal.ofReal
        ((radialGaussianMass μ b)⁻¹ * Real.exp (-b * ‖x‖^2))) ∘ assemble := by
    funext p
    simp only [Function.comp_apply, norm_assemble]
  rw [he, map_density (assemble_preserving_haar μ) (by fun_prop)]
  rfl

/-- Normalizing the surface factor puts its mass in the radius factor. -/
theorem polar_product_eq_raw (b : ℝ) :
    (sphereLaw μ).prod (radiusLaw μ b) = μ.toSphere.prod (rawRadiusLaw μ b) := by
  rw [sphereLaw, radiusLaw, Measure.prod_smul_right, Measure.prod_smul_left,
    smul_smul, ENNReal.mul_inv_cancel
      (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero μ)) (measure_ne_top _ _), one_smul]

/-- The actual radial Gaussian is precisely the product reconstruction of
normalized Haar direction and an independent positive radius. -/
theorem radialGaussianLaw_eq_map_polar (b : ℝ) :
    radialGaussianLaw μ b = ((sphereLaw μ).prod (radiusLaw μ b)).map assemble := by
  rw [polar_product_eq_raw, radialGaussianLaw_eq_map_raw]

theorem radiusLaw_probability {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (radiusLaw μ b) := by
  haveI := radialGaussianLaw_isProbabilityMeasure μ hb
  constructor
  have he := congrArg (fun ν : Measure E => ν Set.univ)
    (radialGaussianLaw_eq_map_polar μ b)
  rw [measure_univ, Measure.map_apply measurable_assemble MeasurableSet.univ,
    Set.preimage_univ] at he
  simpa only [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul] using he.symm

/-- Radius and unit direction really are independent under the explicit
Gaussian polar law. -/
theorem direction_radius_independent {b : ℝ} (hb : 0 < b) :
    IndepFun (fun p : UnitSphere E × Radius => p.1)
      (fun p => (p.2 : ℝ)^2) ((sphereLaw μ).prod (radiusLaw μ b)) := by
  letI := radiusLaw_probability μ hb
  exact indepFun_prod (X := fun u : UnitSphere E => u)
    (Y := fun r : Radius => (r : ℝ)^2) measurable_id (by fun_prop)

end AHHRadial
