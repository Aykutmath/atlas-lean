import GammaProductLaw

noncomputable section
open Finset MeasureTheory ProbabilityTheory Set
namespace GaussianMixedNormHelpers

theorem chiSquareKernel_negative_real_moment {y : ℝ} (hy : 0 < y) (s : ℝ) :
    (∫ x : ℝ in Ioi 0, x ^ (-s) * chiSquareKernel (y + s) x) =
      ((2 : ℝ) ^ s)⁻¹ * (Real.Gamma y / Real.Gamma (y + s)) := by
  have hfun : Set.EqOn
      (fun x : ℝ => x ^ (-s) * chiSquareKernel (y + s) x)
      (fun x : ℝ => (2 ^ (y + s) * Real.Gamma (y + s))⁻¹ *
        (x ^ (y - 1) * Real.exp (-(1 / 2 * x))))
      (Ioi 0) := by
    intro x hx
    have hpow : x ^ (-s) * x ^ (y + s - 1) = x ^ (y - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    dsimp only [chiSquareKernel]
    rw [show x / 2 = 1 / 2 * x by ring]
    calc
      _ = (2 ^ (y + s) * Real.Gamma (y + s))⁻¹ *
          ((x ^ (-s) * x ^ (y + s - 1)) * Real.exp (-(1 / 2 * x))) := by ring
      _ = _ := by rw [hpow]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hy (show (0 : ℝ) < 1 / 2 by norm_num)
  norm_num only [one_div_div] at h
  rw [h]
  rw [Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
  have h2 : (2 : ℝ) ^ y ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp

theorem integral_gammaMeasure_half_negative_real {y : ℝ} (hy : 0 < y) (s : ℝ) (hs : 0 ≤ s) :
    (∫ x : ℝ, x ^ (-s) ∂gammaMeasure (y + s) (1 / 2)) =
      ((2 : ℝ) ^ s)⁻¹ * (Real.Gamma y / Real.Gamma (y + s)) := by
  have hα : 0 < y + s := by positivity
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  unfold gammaMeasure
  change (∫ x : ℝ, x ^ (-s) ∂volume.withDensity
    (fun x => ENNReal.ofReal (gammaPDFReal (y + s) (1 / 2) x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal (y + s) (1 / 2)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg hα hr _), smul_eq_mul]
  have hzero : ∀ x : ℝ, x ∉ Set.Ici 0 →
      gammaPDFReal (y + s) (1 / 2) x * x ^ (-s) = 0 := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp [gammaPDFReal, hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_Ici_eq_integral_Ioi]
  have hcongr : (∫ x : ℝ in Ioi 0, gammaPDFReal (y + s) (1 / 2) x * x ^ (-s)) =
      (∫ x : ℝ in Ioi 0, x ^ (-s) * chiSquareKernel (y + s) x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [gammaPDFReal_half_eq_chiSquareKernel hx, mul_comm]
  rw [hcongr]
  exact chiSquareKernel_negative_real_moment hy s

theorem integrable_gammaMeasure_half_negative_real {y : ℝ} (hy : 0 < y)
    (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => x ^ (-s)) (gammaMeasure (y + s) (1 / 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gammaMeasure_half_negative_real hy s hs]
  exact ne_of_gt (by positivity)

#print axioms integral_gammaMeasure_half_negative_real
#print axioms integrable_gammaMeasure_half_negative_real
end GaussianMixedNormHelpers
