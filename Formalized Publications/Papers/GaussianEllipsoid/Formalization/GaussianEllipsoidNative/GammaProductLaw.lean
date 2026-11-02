import GammaInverseMoment
import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Finset MeasureTheory ProbabilityTheory Set

namespace GaussianMixedNormHelpers

/-- The explicit scale-two kernel agrees with Mathlib's gamma density at rate 1/2. -/
theorem gammaPDFReal_half_eq_chiSquareKernel {α x : ℝ} (hx : 0 < x) :
    gammaPDFReal α (1 / 2) x = chiSquareKernel α x := by
  rw [gammaPDFReal, if_pos hx.le]
  unfold chiSquareKernel
  rw [one_div, Real.inv_rpow (show (0 : ℝ) ≤ 2 by norm_num)]
  have he : -(2⁻¹ * x) = -(x / 2) := by ring
  rw [he]
  ring

/-- Exact expectation under Mathlib's genuine gamma probability measure. -/
theorem integral_gammaMeasure_half_negative_nat {y : ℝ} (hy : 0 < y) (s : ℕ) :
    (∫ x : ℝ, x ^ (-(s : ℝ)) ∂gammaMeasure (y + s) (1 / 2)) =
      ((2 : ℝ) ^ s)⁻¹ * (Real.Gamma y / Real.Gamma (y + s)) := by
  have hα : 0 < y + (s : ℝ) := by positivity
  have hr : (0 : ℝ) < 1 / 2 := by norm_num
  unfold gammaMeasure
  change (∫ x : ℝ, x ^ (-(s : ℝ)) ∂volume.withDensity
    (fun x => ENNReal.ofReal (gammaPDFReal (y + s) (1 / 2) x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal (y + s) (1 / 2)).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg hα hr _), smul_eq_mul]
  have hzero : ∀ x : ℝ, x ∉ Set.Ici 0 →
      gammaPDFReal (y + s) (1 / 2) x * x ^ (-(s : ℝ)) = 0 := by
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp [gammaPDFReal, hx]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_Ici_eq_integral_Ioi]
  have hcongr : (∫ x : ℝ in Ioi 0, gammaPDFReal (y + s) (1 / 2) x * x ^ (-(s : ℝ))) =
      (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) * chiSquareKernel (y + s) x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [gammaPDFReal_half_eq_chiSquareKernel hx, mul_comm]
  rw [hcongr]
  exact chiSquareKernel_negative_nat_moment hy s

/-- Finite product integration for arbitrary sigma-finite coordinate laws.
All factorization is proved by Mathlib's finite Fubini theorem. -/
theorem integral_pi_prod_real {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)] (f : ι → ℝ → ℝ) :
    (∫ x : ι → ℝ, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫ x : ℝ, f i x ∂μ i := by
  exact integral_fintype_prod_eq_prod f

/-- The independent Bartlett factor law as an actual finite product measure. -/
def bartlettGammaLaw (r s : ℕ) : Measure (Fin r → ℝ) :=
  Measure.pi (fun k : Fin r => gammaMeasure (((k : ℝ) + 1) / 2 + s) (1 / 2))

/-- Independent chi-square inverse moments factor exactly without any premise
asserting independence or moment factorization. -/
theorem bartlettGammaLaw_negative_moment_eq_product (r s : ℕ) :
    (∫ x : Fin r → ℝ, ∏ k, (x k) ^ (-(s : ℝ)) ∂bartlettGammaLaw r s) =
      ∏ k ∈ Finset.range r,
        (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) *
          chiSquareKernel (((k : ℝ) + 1) / 2 + s) x) := by
  let μ := fun k : Fin r => gammaMeasure (((k : ℝ) + 1) / 2 + s) (1 / 2)
  letI (k : Fin r) : IsProbabilityMeasure (μ k) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  change (∫ x : Fin r → ℝ, ∏ k, (x k) ^ (-(s : ℝ)) ∂Measure.pi μ) = _
  rw [integral_pi_prod_real μ (fun _ x => x ^ (-(s : ℝ)))]
  calc
    _ = ∏ k : Fin r,
        (∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) *
          chiSquareKernel (((k : ℝ) + 1) / 2 + s) x) := by
      apply Finset.prod_congr rfl
      intro k hk
      change (∫ x : ℝ, x ^ (-(s : ℝ)) ∂gammaMeasure (((k : ℝ) + 1) / 2 + s) (1 / 2)) = _
      rw [integral_gammaMeasure_half_negative_nat (by positivity),
        chiSquareKernel_negative_nat_moment (by positivity)]
    _ = _ := Fin.prod_univ_eq_prod_range (fun k : ℕ =>
      ∫ x : ℝ in Ioi 0, x ^ (-(s : ℝ)) *
        chiSquareKernel (((k : ℝ) + 1) / 2 + s) x) r

/-- The negative determinant factor bound on a genuine independent gamma law. -/
theorem bartlettGammaLaw_negative_moment_le (r s : ℕ) :
    (∫ x : Fin r → ℝ, ∏ k, (x k) ^ (-(s : ℝ)) ∂bartlettGammaLaw r s) ≤
      1 / ((r.factorial : ℝ) ^ s) := by
  rw [bartlettGammaLaw_negative_moment_eq_product]
  exact chiSquareKernel_negative_nat_product_le r s

/-- Scaled negative moment on the genuine independent gamma product law. -/
theorem bartlettGammaLaw_scaled_negative_moment_le (r s : ℕ) :
    (2 * (r : ℝ)) ^ (r * s) *
      (∫ x : Fin r → ℝ, ∏ k, (x k) ^ (-(s : ℝ)) ∂bartlettGammaLaw r s) ≤
      (2 * Real.exp 1) ^ (r * s) := by
  rw [bartlettGammaLaw_negative_moment_eq_product]
  exact scaled_chiSquareKernel_negative_nat_product_le r s


/-- The scalar inverse moment is genuinely integrable, not merely a value
of the totalized Bochner integral. -/
theorem integrable_gammaMeasure_half_negative_nat {y : ℝ} (hy : 0 < y) (s : ℕ) :
    Integrable (fun x : ℝ => x ^ (-(s : ℝ))) (gammaMeasure (y + s) (1 / 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_gammaMeasure_half_negative_nat hy]
  exact ne_of_gt (by positivity)

/-- The finite independent gamma law is a probability measure. -/
theorem bartlettGammaLaw_isProbabilityMeasure (r s : ℕ) :
    IsProbabilityMeasure (bartlettGammaLaw r s) := by
  let μ := fun k : Fin r => gammaMeasure (((k : ℝ) + 1) / 2 + s) (1 / 2)
  letI (k : Fin r) : IsProbabilityMeasure (μ k) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  change IsProbabilityMeasure (Measure.pi μ)
  infer_instance

/-- Genuine integrability of the complete finite inverse-moment product. -/
theorem bartlettGammaLaw_negative_moment_integrable (r s : ℕ) :
    Integrable (fun x : Fin r → ℝ => ∏ k, (x k) ^ (-(s : ℝ)))
      (bartlettGammaLaw r s) := by
  apply Integrable.of_integral_ne_zero
  rw [bartlettGammaLaw_negative_moment_eq_product]
  apply ne_of_gt
  apply Finset.prod_pos
  intro k hk
  rw [chiSquareKernel_negative_nat_moment (by positivity : 0 < ((k : ℝ) + 1) / 2)]
  positivity


/-- Conversion of real negative integer powers, with no positivity assumption. -/
theorem rpow_negative_nat (x : ℝ) (s : ℕ) :
    x ^ (-(s : ℝ)) = (x ^ s)⁻¹ := by
  simpa only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] using
    Real.rpow_intCast x (-(s : ℤ))

/-- Integer inverse powers commute with finite products, including zero factors. -/
theorem prod_negative_nat_rpow {ι : Type*} [Fintype ι] (x : ι → ℝ) (s : ℕ) :
    (∏ i, x i) ^ (-(s : ℝ)) = ∏ i, (x i) ^ (-(s : ℝ)) := by
  simp_rw [rpow_negative_nat]
  rw [Finset.prod_inv_distrib, Finset.prod_pow]

/-- The completed scaled-product inverse moment, directly in determinant form. -/
theorem bartlettGammaLaw_scaled_product_inverse_moment_le (r s : ℕ) :
    (∫ x : Fin r → ℝ,
      (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ k, x k) ^ (-(s : ℝ))
        ∂bartlettGammaLaw r s) ≤ (2 * Real.exp 1) ^ (r * s) := by
  have hfun : (fun x : Fin r → ℝ =>
      (((2 * (r : ℝ)) ^ r)⁻¹ * ∏ k, x k) ^ (-(s : ℝ))) =
      (fun x => (2 * (r : ℝ)) ^ (r * s) * ∏ k, (x k) ^ (-(s : ℝ))) := by
    ext x
    simp only [rpow_negative_nat, mul_pow, inv_pow, mul_inv_rev, inv_inv,
      Finset.prod_inv_distrib, Finset.prod_pow, pow_mul]
    ring
  rw [hfun, integral_const_mul]
  exact bartlettGammaLaw_scaled_negative_moment_le r s

end GaussianMixedNormHelpers
