import GammaProductLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaussianMixedNormHelpers

/-- Gamma laws put full mass on the strictly positive half-line. -/
theorem gammaMeasure_pos_ae (a b : ℝ) : ∀ᵐ x : ℝ ∂gammaMeasure a b, 0 < x := by
  have hneg : gammaMeasure a b (Set.Iio 0) = 0 := by
    rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
    exact lintegral_gammaPDF_of_nonpos (le_refl 0)
  have hzero : gammaMeasure a b {0} = 0 := by
    rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  rw [ae_iff]
  simp only [not_lt]
  change gammaMeasure a b (Set.Iic 0) = 0
  have hsub : Set.Iic (0 : ℝ) ⊆ Set.Iio 0 ∪ {0} := by
    intro x hx
    by_cases h : x = 0
    · exact Or.inr h
    · exact Or.inl (lt_of_le_of_ne hx h)
  exact measure_mono_null hsub (measure_union_null hneg hzero)

/-- Every independent Bartlett gamma factor is positive almost surely. -/
theorem bartlettGammaLaw_factors_pos_ae (r s : ℕ) :
    ∀ᵐ x : Fin r → ℝ ∂bartlettGammaLaw r s, ∀ i, 0 < x i := by
  let μ := fun k : Fin r => gammaMeasure (((k : ℝ) + 1) / 2 + s) (1 / 2)
  letI (k : Fin r) : IsProbabilityMeasure (μ k) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  change ∀ᵐ x : Fin r → ℝ ∂Measure.pi μ, ∀ i, 0 < x i
  apply ae_all_iff.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := μ) (i := i)).eventually
    (gammaMeasure_pos_ae _ _)

theorem bartlettGammaLaw_product_pos_ae (r s : ℕ) :
    ∀ᵐ x : Fin r → ℝ ∂bartlettGammaLaw r s, 0 < ∏ i, x i := by
  filter_upwards [bartlettGammaLaw_factors_pos_ae r s] with x hx
  exact Finset.prod_pos (fun i _ => hx i)

/-- ENNReal's singular=infinity inverse power agrees almost surely with the
integrable real inverse power under the genuine independent Gamma law. -/
theorem bartlettGammaLaw_extended_inverse_eq_real (r s : ℕ) :
    (fun x : Fin r → ℝ => (ENNReal.ofReal (∏ i, x i) ^ s)⁻¹) =ᵐ[bartlettGammaLaw r s]
      (fun x => ENNReal.ofReal ((∏ i, x i) ^ (-(s : ℝ)))) := by
  filter_upwards [bartlettGammaLaw_product_pos_ae r s] with x hx
  rw [rpow_negative_nat, ENNReal.ofReal_inv_of_pos (pow_pos hx s), ENNReal.ofReal_pow hx.le]

/-- The singular-safe extended inverse-product moment is finite with the
factorial bound, without any assumed Bartlett factorization. -/
theorem bartlettGammaLaw_extended_inverse_moment_le (r s : ℕ) :
    (∫⁻ x : Fin r → ℝ, (ENNReal.ofReal (∏ i, x i) ^ s)⁻¹ ∂bartlettGammaLaw r s) ≤
      ENNReal.ofReal (1 / (r.factorial : ℝ) ^ s) := by
  rw [lintegral_congr_ae (bartlettGammaLaw_extended_inverse_eq_real r s)]
  have hInt : Integrable (fun x : Fin r → ℝ => (∏ i, x i) ^ (-(s : ℝ)))
      (bartlettGammaLaw r s) := by
    simpa only [prod_negative_nat_rpow] using bartlettGammaLaw_negative_moment_integrable r s
  have hnn : 0 ≤ᵐ[bartlettGammaLaw r s]
      (fun x : Fin r → ℝ => (∏ i, x i) ^ (-(s : ℝ))) := by
    filter_upwards [bartlettGammaLaw_product_pos_ae r s] with x hx
    exact Real.rpow_nonneg hx.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  apply ENNReal.ofReal_le_ofReal
  simpa only [prod_negative_nat_rpow] using bartlettGammaLaw_negative_moment_le r s

/-- The scaled covariance product is positive almost surely when r>0. -/
theorem bartlettGammaLaw_scaled_product_pos_ae (r s : ℕ) (hr : 0 < r) :
    ∀ᵐ x : Fin r → ℝ ∂bartlettGammaLaw r s,
      0 < ((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i := by
  filter_upwards [bartlettGammaLaw_product_pos_ae r s] with x hx
  exact mul_pos (inv_pos.mpr (pow_pos (by positivity) _)) hx

/-- Singular-safe scaled inverse-determinant factor estimate in ENNReal. -/
theorem bartlettGammaLaw_scaled_extended_inverse_moment_le (r s : ℕ) (hr : 0 < r) :
    (∫⁻ x : Fin r → ℝ,
      (ENNReal.ofReal (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i) ^ s)⁻¹
        ∂bartlettGammaLaw r s) ≤ ENNReal.ofReal ((2 * Real.exp 1) ^ (r * s)) := by
  have heq : (fun x : Fin r → ℝ =>
      (ENNReal.ofReal (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i) ^ s)⁻¹) =ᵐ[bartlettGammaLaw r s]
      (fun x => ENNReal.ofReal ((((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i) ^ (-(s : ℝ)))) := by
    filter_upwards [bartlettGammaLaw_scaled_product_pos_ae r s hr] with x hx
    rw [rpow_negative_nat, ENNReal.ofReal_inv_of_pos (pow_pos hx s), ENNReal.ofReal_pow hx.le]
  rw [lintegral_congr_ae heq]
  have hfun : (fun x : Fin r → ℝ =>
      (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i) ^ (-(s : ℝ))) =
      (fun x => (2 * (r : ℝ)) ^ (r * s) * ∏ i, (x i) ^ (-(s : ℝ))) := by
    ext x
    simp only [rpow_negative_nat, mul_pow, inv_pow, mul_inv_rev, inv_inv,
      Finset.prod_inv_distrib, Finset.prod_pow, pow_mul]
    ring
  have hInt : Integrable (fun x : Fin r → ℝ =>
      (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i) ^ (-(s : ℝ))) (bartlettGammaLaw r s) := by
    rw [hfun]
    exact (bartlettGammaLaw_negative_moment_integrable r s).const_mul _
  have hnn : 0 ≤ᵐ[bartlettGammaLaw r s] (fun x : Fin r → ℝ =>
      (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ i, x i) ^ (-(s : ℝ))) := by
    filter_upwards [bartlettGammaLaw_scaled_product_pos_ae r s hr] with x hx
    exact Real.rpow_nonneg hx.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hnn]
  exact ENNReal.ofReal_le_ofReal (bartlettGammaLaw_scaled_product_inverse_moment_le r s)

end GaussianMixedNormHelpers
