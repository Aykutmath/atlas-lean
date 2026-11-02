import AHHRadialMean
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Exact transport of normalized radial Gaussian densities under scaling and
real linear isometries. -/
noncomputable section
open MeasureTheory Set GaussianMixedNormHelpers
open scoped ENNReal
namespace AHHRadial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Probability normalization determines the coefficient of a radial density. -/
theorem probability_density_eq_radial {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    [IsProbabilityMeasure (μ.withDensity (fun x : E => ENNReal.ofReal
      (C * Real.exp (-b * ‖x‖^2))))] :
    μ.withDensity (fun x : E => ENNReal.ofReal (C * Real.exp (-b * ‖x‖^2))) =
      radialGaussianLaw μ b := by
  have hmass := radialGaussianMass_pos μ hb
  have he : (∫ x : E, (1 : ℝ) ∂μ.withDensity
      (fun x : E => ENNReal.ofReal (C * Real.exp (-b * ‖x‖^2)))) = 1 := by
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at he
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg hC (Real.exp_nonneg _)),
    smul_eq_mul, mul_one] at he
  rw [integral_const_mul] at he
  have hc : C = (radialGaussianMass μ b)⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hmass.ne').mpr he
  rw [hc]
  rfl

/-- Exact rescaling of the actual radial Gaussian probability law. -/
theorem map_radialGaussian_smul {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    (radialGaussianLaw μ b).map (fun x => c • x) = radialGaussianLaw μ (b / c^2) := by
  let e : E ≃ᵐ E := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hc.ne').unit).toMeasurableEquiv
  have he : ∀ x : E, e x = c • x := fun _ => rfl
  have hei : ∀ x : E, e.symm x = c⁻¹ • x := by
    intro x
    apply e.injective
    rw [e.apply_symm_apply, he, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hp : MeasurePreserving e μ
      (ENNReal.ofReal (abs (c ^ Module.finrank ℝ E)⁻¹) • μ) := by
    refine ⟨e.measurable, ?_⟩
    exact Measure.map_addHaar_smul μ hc.ne'
  have hnorm (x : E) : -b * ‖e.symm x‖^2 = -(b/c^2) * ‖x‖^2 := by
    rw [hei, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), mul_pow]
    field_simp
  let C : ℝ := abs (c ^ Module.finrank ℝ E)⁻¹ * (radialGaussianMass μ b)⁻¹
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (radialGaussianMass_pos μ hb).le)
  have hmap : (radialGaussianLaw μ b).map (fun x => c • x) =
      μ.withDensity (fun x : E => ENNReal.ofReal (C * Real.exp (-(b/c^2) * ‖x‖^2))) := by
    change (μ.withDensity _).map e = _
    rw [map_withDensity_equiv e μ _ hp, withDensity_smul_measure,
      ← withDensity_smul _ (by fun_prop)]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, hnorm, ← ENNReal.ofReal_mul (abs_nonneg _), C]
    congr 1
    ring
  rw [hmap]
  letI := radialGaussianLaw_isProbabilityMeasure μ hb
  haveI : IsProbabilityMeasure (μ.withDensity (fun x : E =>
      ENNReal.ofReal (C * Real.exp (-(b/c^2) * ‖x‖^2)))) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  exact probability_density_eq_radial μ (div_pos hb (sq_pos_of_pos hc)) hC

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
  (ν : Measure F) [ν.IsAddHaarMeasure]

/-- Exact radial density transport under any volume-preserving real isometry. -/
theorem map_radialGaussian_isometry {b : ℝ} (hb : 0 < b) (e : E ≃ₗᵢ[ℝ] F)
    (he : MeasurePreserving e μ ν) :
    (radialGaussianLaw μ b).map e = radialGaussianLaw ν b := by
  have hmap : (radialGaussianLaw μ b).map e =
      ν.withDensity (fun y : F => ENNReal.ofReal
        ((radialGaussianMass μ b)⁻¹ * Real.exp (-b * ‖y‖^2))) := by
    unfold radialGaussianLaw
    exact (map_withDensity_equiv e.toHomeomorph.toMeasurableEquiv μ ν he _).trans (by
      congr 1
      funext y
      change ENNReal.ofReal ((radialGaussianMass μ b)⁻¹ * Real.exp (-b * ‖e.symm y‖^2)) = _
      rw [e.symm.norm_map])
  rw [hmap]
  letI := radialGaussianLaw_isProbabilityMeasure μ hb
  haveI : IsProbabilityMeasure (ν.withDensity (fun y : F => ENNReal.ofReal
      ((radialGaussianMass μ b)⁻¹ * Real.exp (-b * ‖y‖^2)))) := by
    rw [← hmap]
    exact Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  exact probability_density_eq_radial ν hb (inv_nonneg.mpr (radialGaussianMass_pos μ hb).le)

#print axioms map_radialGaussian_smul
#print axioms map_radialGaussian_isometry
end AHHRadial
