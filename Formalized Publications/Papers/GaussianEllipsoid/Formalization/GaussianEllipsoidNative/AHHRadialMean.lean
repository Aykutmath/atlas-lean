import AHHRadialDirection
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Exact first radial moment and the dimension-2h normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set GaussianMixedNormHelpers
open scoped ENNReal
namespace AHHRadial

/-- The mean of the genuine Gamma law is shape/rate. -/
theorem gamma_mean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ, t ∂gammaMeasure a b) = a / b := by
  rw [integral_gammaMeasure_eq_kernel ha hb]
  have hi : (∫ t : ℝ in Ioi 0, t ^ (a - 1) * (Real.exp (-b * t) * t)) =
      (∫ t : ℝ in Ioi 0, t ^ ((a+1) - 1) * Real.exp (-(b*t))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [show -b * t = -(b*t) by ring]
    calc
      _ = (t ^ (a-1) * t^ (1:ℝ)) * Real.exp (-(b*t)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add ht]; congr 2 <;> ring
  rw [hi, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hb,
    Real.Gamma_add_one ha.ne', Real.rpow_add (by positivity), Real.rpow_one,
    one_div, Real.inv_rpow hb.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hb a), ne_of_gt (Real.Gamma_pos_of_pos ha)]

theorem gamma_integrable_id {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun t : ℝ => t) (gammaMeasure a b) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_mean ha hb]
  exact ne_of_gt (div_pos ha hb)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Exact squared-radius marginal of the polar law. -/
theorem radiusLaw_map_sq {b : ℝ} (hb : 0 < b) :
    (radiusLaw μ b).map (fun r : Radius => (r : ℝ)^2) =
      gammaMeasure ((Module.finrank ℝ E : ℝ)/2) b := by
  have he := radialGaussianLaw_map_norm_sq μ hb
  rw [radialGaussianLaw_eq_map_polar, Measure.map_map (by fun_prop) measurable_assemble] at he
  have hf : (fun x : E => ‖x‖^2) ∘ assemble =
      (fun r : Radius => (r : ℝ)^2) ∘ Prod.snd := by
    funext p
    simp only [Function.comp_apply, norm_assemble]
  rw [hf, ← Measure.map_map (by fun_prop) measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul] at he
  exact he

theorem radiusLaw_integrable_sq {b : ℝ} (hb : 0 < b) :
    Integrable (fun r : Radius => (r : ℝ)^2) (radiusLaw μ b) := by
  have hi := gamma_integrable_id
    (show (0 : ℝ) < (Module.finrank ℝ E : ℝ)/2 from
      div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)) hb
  rw [← radiusLaw_map_sq μ hb] at hi
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    (by fun_prop : AEMeasurable (fun r : Radius => (r : ℝ)^2) (radiusLaw μ b))).mp hi

theorem radiusLaw_mean_sq {b : ℝ} (hb : 0 < b) :
    (∫ r : Radius, (r : ℝ)^2 ∂radiusLaw μ b) = (Module.finrank ℝ E : ℝ)/(2*b) := by
  have he := integral_map (μ := radiusLaw μ b) (φ := fun r : Radius => (r : ℝ)^2)
    (f := fun t : ℝ => t) (by fun_prop) measurable_id.aestronglyMeasurable
  rw [radiusLaw_map_sq μ hb] at he
  rw [← he, gamma_mean (div_pos (Nat.cast_pos.mpr Module.finrank_pos) (by norm_num)) hb]
  ring

/-- The real dimension of a complex h-dimensional Euclidean space is 2h. -/
theorem complex_finrank_real (h : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin h)) = 2*h := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

/-- The isotropic complex normalization exp(-h‖z‖²) has exact mean square radius one. -/
theorem complex_radius_mean_sq (h : ℕ) (hh : 0 < h) :
    (∫ r : Radius, (r : ℝ)^2 ∂radiusLaw
      (volume : Measure (EuclideanSpace ℂ (Fin h))) h) = 1 := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  rw [radiusLaw_mean_sq _ (by exact_mod_cast hh), complex_finrank_real]
  push_cast
  field_simp

#print axioms gamma_mean
#print axioms radiusLaw_map_sq
#print axioms complex_radius_mean_sq
end AHHRadial
