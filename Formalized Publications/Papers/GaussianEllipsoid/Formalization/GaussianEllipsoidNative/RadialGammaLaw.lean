import RadialGaussianIntegral
import Mathlib.Probability.Distributions.Gamma

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace GaussianMixedNormHelpers

/-- Exact change of variables from a radius to its square. -/
theorem radial_square_substitution (m : ℕ) (hm : 0 < m) (b : ℝ) (φ : ℝ → ℝ) :
    (∫ r : ℝ in Ioi 0, r ^ (m - 1) * (Real.exp (-b * r ^ 2) * φ (r ^ 2))) =
      (1 / 2 : ℝ) * ∫ t : ℝ in Ioi 0,
        t ^ ((m : ℝ) / 2 - 1) * (Real.exp (-b * t) * φ t) := by
  rw [← integral_comp_rpow_Ioi
    (fun r : ℝ => r ^ (m - 1) * (Real.exp (-b * r ^ 2) * φ (r ^ 2)))
    (show (1 / 2 : ℝ) ≠ 0 by norm_num), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  have hsq : (t ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  rw [hsq, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), smul_eq_mul,
    ← Real.rpow_natCast _ (m - 1), ← Real.rpow_mul ht.le,
    Nat.cast_sub (Nat.succ_le_of_lt hm), Nat.cast_one]
  rw [mul_assoc, ← mul_assoc (t ^ (1 / 2 - 1)), ← Real.rpow_add ht]
  congr 2
  ring

/-- Arbitrary test-function integral under the actual Gamma measure. -/
theorem integral_gammaMeasure_eq_kernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (φ : ℝ → ℝ) :
    (∫ t : ℝ, φ t ∂gammaMeasure a b) =
      (b ^ a / Real.Gamma a) * ∫ t : ℝ in Ioi 0,
        t ^ (a - 1) * (Real.exp (-b * t) * φ t) := by
  unfold gammaMeasure
  change (∫ t : ℝ, φ t ∂volume.withDensity
    (fun t => ENNReal.ofReal (gammaPDFReal a b t))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal a b).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hb _), smul_eq_mul]
  have hzero : ∀ t : ℝ, t ∉ Set.Ici 0 → gammaPDFReal a b t * φ t = 0 := by
    intro t ht
    simp only [Set.mem_Ici] at ht
    simp [gammaPDFReal, ht]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_Ici_eq_integral_Ioi, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [gammaPDFReal, if_pos ht.le]
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Squared radius of the normalized radial Gaussian integrates as the actual
Gamma law with shape dim(E)/2 and rate b. -/
theorem radialGaussianLaw_integral_norm_sq {b : ℝ} (hb : 0 < b) (φ : ℝ → ℝ) :
    (∫ x : E, φ (‖x‖ ^ 2) ∂radialGaussianLaw μ b) =
      ∫ t : ℝ, φ t ∂gammaMeasure ((Module.finrank ℝ E : ℝ) / 2) b := by
  have hm : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hmR : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr hm
  have hpos := radialGaussianMass_pos μ hb
  have hball : μ.real (Metric.ball (0 : E) 1) ≠ 0 := ne_of_gt
    (ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 (by norm_num)))
      (ne_of_lt measure_ball_lt_top))
  unfold radialGaussianLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun x : E => ENNReal.ofReal ((radialGaussianMass μ b)⁻¹ *
      Real.exp (-b * ‖x‖ ^ 2))))
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hpos.le) (Real.exp_nonneg _)),
    smul_eq_mul, mul_assoc]
  rw [integral_const_mul, integral_fun_norm_addHaar μ
    (fun r : ℝ => Real.exp (-b * r ^ 2) * φ (r ^ 2))]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [radial_square_substitution _ hm b φ,
    integral_gammaMeasure_eq_kernel (by positivity) hb φ]
  unfold radialGaussianMass
  rw [integral_gaussian_radial μ b hb]
  have he : -(Module.finrank ℝ E : ℝ) / 2 = -((Module.finrank ℝ E : ℝ) / 2) := by ring
  rw [he, Real.rpow_neg hb.le]
  have hbp : b ^ ((Module.finrank ℝ E : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hb _)
  field_simp [ne_of_gt hmR, hball, hbp]

/-- Full distributional identification, not merely a list of radial moments. -/
theorem radialGaussianLaw_map_norm_sq {b : ℝ} (hb : 0 < b) :
    (radialGaussianLaw μ b).map (fun x : E => ‖x‖ ^ 2) =
      gammaMeasure ((Module.finrank ℝ E : ℝ) / 2) b := by
  letI := radialGaussianLaw_isProbabilityMeasure μ hb
  have hmap : Measurable (fun x : E => ‖x‖ ^ 2) := by fun_prop
  letI := Measure.isProbabilityMeasure_map (μ := radialGaussianLaw μ b) hmap.aemeasurable
  letI := isProbabilityMeasure_gammaMeasure (show (0 : ℝ) < (Module.finrank ℝ E : ℝ) / 2 by
    exact div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)) hb
  ext s hs
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((radialGaussianLaw μ b).map (fun x : E => ‖x‖ ^ 2)).real s =
    (gammaMeasure ((Module.finrank ℝ E : ℝ) / 2) b).real s
  rw [← integral_indicator_one hs, ← integral_indicator_one hs]
  have hf : AEStronglyMeasurable (s.indicator (1 : ℝ → ℝ))
      ((radialGaussianLaw μ b).map (fun x : E => ‖x‖ ^ 2)) :=
    (measurable_const.indicator hs).aestronglyMeasurable
  rw [integral_map (μ := radialGaussianLaw μ b) hmap.aemeasurable hf]
  exact radialGaussianLaw_integral_norm_sq μ hb (s.indicator (fun _ => (1 : ℝ)))

end GaussianMixedNormHelpers
