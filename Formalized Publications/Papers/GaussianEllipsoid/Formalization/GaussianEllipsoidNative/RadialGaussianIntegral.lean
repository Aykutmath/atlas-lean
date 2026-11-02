import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

noncomputable section
open MeasureTheory Set Real

namespace GaussianMixedNormHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- General finite-dimensional radial Gaussian power integral, derived from
polar integration and the exact scalar Gamma integral. -/
theorem integral_norm_rpow_mul_gaussian {q b : ℝ}
    (hq : -(Module.finrank ℝ E : ℝ) < q) (hb : 0 < b) :
    (∫ x : E, ‖x‖ ^ q * Real.exp (-b * ‖x‖ ^ 2) ∂μ) =
      (Module.finrank ℝ E : ℝ) * μ.real (Metric.ball 0 1) *
        (b ^ (-(q + Module.finrank ℝ E) / 2) * (1 / 2) *
          Real.Gamma ((q + Module.finrank ℝ E) / 2)) := by
  have hd : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hrad := integral_fun_norm_addHaar μ (fun t : ℝ => t ^ q * Real.exp (-b * t ^ 2))
  simp only [nsmul_eq_mul, smul_eq_mul] at hrad
  rw [hrad]
  have hint : (∫ t : ℝ in Set.Ioi 0,
      t ^ (Module.finrank ℝ E - 1) * (t ^ q * Real.exp (-b * t ^ 2))) =
      (∫ t : ℝ in Set.Ioi 0,
        t ^ (q + Module.finrank ℝ E - 1) * Real.exp (-b * t ^ (2 : ℝ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [← Real.rpow_natCast t (Module.finrank ℝ E - 1),
      Nat.cast_sub (Nat.succ_le_of_lt hd), Nat.cast_one,
      ← mul_assoc, ← Real.rpow_add ht, Real.rpow_two]
    congr 2
    ring
  rw [hint, integral_rpow_mul_exp_neg_mul_rpow (show (0 : ℝ) < 2 by norm_num)
    (by linarith : -1 < q + (Module.finrank ℝ E : ℝ) - 1) hb]
  simp only [sub_add_cancel]
  ring

/-- Normalization integral as the q=0 case of the same radial calculation. -/
theorem integral_gaussian_radial (b : ℝ) (hb : 0 < b) :
    (∫ x : E, Real.exp (-b * ‖x‖ ^ 2) ∂μ) =
      (Module.finrank ℝ E : ℝ) * μ.real (Metric.ball 0 1) *
        (b ^ (-(Module.finrank ℝ E : ℝ) / 2) * (1 / 2) *
          Real.Gamma ((Module.finrank ℝ E : ℝ) / 2)) := by
  simpa using integral_norm_rpow_mul_gaussian μ
    (q := 0) (by exact neg_neg_of_pos (Nat.cast_pos.mpr Module.finrank_pos)) hb


/-- The finite positive normalizing mass of a radial Gaussian kernel. -/
def radialGaussianMass (b : ℝ) : ℝ := ∫ x : E, Real.exp (-b * ‖x‖ ^ 2) ∂μ

theorem radialGaussianMass_pos {b : ℝ} (hb : 0 < b) : 0 < radialGaussianMass μ b := by
  have hball : 0 < μ.real (Metric.ball (0 : E) 1) :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 (by norm_num)))
      (ne_of_lt measure_ball_lt_top)
  unfold radialGaussianMass
  rw [integral_gaussian_radial μ b hb]
  have hd : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  positivity

/-- The normalized radial Gaussian law, with an explicit density against Haar measure. -/
def radialGaussianLaw (b : ℝ) : Measure E :=
  μ.withDensity (fun x => ENNReal.ofReal ((radialGaussianMass μ b)⁻¹ *
    Real.exp (-b * ‖x‖ ^ 2)))

theorem radialGaussianLaw_isProbabilityMeasure {b : ℝ} (hb : 0 < b) :
    IsProbabilityMeasure (radialGaussianLaw μ b) := by
  have hpos := radialGaussianMass_pos μ hb
  have hint : Integrable (fun x : E => Real.exp (-b * ‖x‖ ^ 2)) μ :=
    Integrable.of_integral_ne_zero (ne_of_gt hpos)
  constructor
  unfold radialGaussianLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _) (Filter.Eventually.of_forall
      (fun x => mul_nonneg (inv_nonneg.mpr hpos.le) (Real.exp_nonneg _))), integral_const_mul]
  change ENNReal.ofReal ((radialGaussianMass μ b)⁻¹ * radialGaussianMass μ b) = 1
  rw [inv_mul_cancel₀ (ne_of_gt hpos), ENNReal.ofReal_one]

/-- Exact finite-dimensional Gaussian negative radial moment, with no assumed
Gaussian-radius distribution. The normalization cancels the sphere volume. -/
theorem radialGaussianLaw_negative_moment {b : ℝ} (hb : 0 < b) (s : ℕ)
    (hs : 2 * s < Module.finrank ℝ E) :
    (∫ x : E, ‖x‖ ^ (-(2 * (s : ℝ))) ∂radialGaussianLaw μ b) =
      b ^ s * (Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 - s) /
        Real.Gamma ((Module.finrank ℝ E : ℝ) / 2)) := by
  have hm : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hsm : 2 * (s : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hs
  have hshape : 0 < (Module.finrank ℝ E : ℝ) / 2 - s := by linarith
  have hpos := radialGaussianMass_pos μ hb
  have hball : μ.real (Metric.ball (0 : E) 1) ≠ 0 := ne_of_gt
    (ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos μ 0 (by norm_num)))
      (ne_of_lt measure_ball_lt_top))
  unfold radialGaussianLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by fun_prop : Measurable (fun x : E => ENNReal.ofReal ((radialGaussianMass μ b)⁻¹ *
      Real.exp (-b * ‖x‖ ^ 2))))
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hpos.le) (Real.exp_nonneg _)),
    smul_eq_mul]
  have hfun : (fun x : E => (radialGaussianMass μ b)⁻¹ * Real.exp (-b * ‖x‖ ^ 2) *
      ‖x‖ ^ (-(2 * (s : ℝ)))) =
      (fun x => (radialGaussianMass μ b)⁻¹ *
        (‖x‖ ^ (-(2 * (s : ℝ))) * Real.exp (-b * ‖x‖ ^ 2))) := by
    ext x; ring
  rw [hfun, integral_const_mul, integral_norm_rpow_mul_gaussian μ (by linarith) hb]
  unfold radialGaussianMass
  rw [integral_gaussian_radial μ b hb]
  rw [show -(-(2 * (s : ℝ)) + (Module.finrank ℝ E : ℝ)) / 2 =
      (s : ℝ) + (-(Module.finrank ℝ E : ℝ) / 2) by ring,
    show (-(2 * (s : ℝ)) + (Module.finrank ℝ E : ℝ)) / 2 =
      (Module.finrank ℝ E : ℝ) / 2 - s by ring,
    Real.rpow_add hb, Real.rpow_natCast]
  have hbp : b ^ (-(Module.finrank ℝ E : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hb _)
  field_simp [ne_of_gt hm, hball, hbp]

end GaussianMixedNormHelpers
