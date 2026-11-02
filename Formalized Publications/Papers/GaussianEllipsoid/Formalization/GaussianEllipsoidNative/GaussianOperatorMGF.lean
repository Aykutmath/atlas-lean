import GaussianFiniteMGF
import SpectralQuadraticForm
import OrthogonalGaussianProjection
import ConditionalMGFTail

open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers GaussianEllipsoid
open scoped ENNReal NNReal InnerProductSpace

namespace GaussianEllipsoidCandidate

/-- Integral transport by an orthogonal map under the actual Gaussian law. -/
theorem euclidean_gaussian_integral_isometry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) (f : EuclideanSpace ℝ κ → ℝ) :
    (∫ x, f (e x) ∂euclideanGaussianLaw ι) = ∫ y, f y ∂euclideanGaussianLaw κ := by
  calc
    (∫ x, f (e x) ∂euclideanGaussianLaw ι)
        = ∫ y, f y ∂(euclideanGaussianLaw ι).map e :=
      (e.toHomeomorph.measurableEmbedding.integral_map f).symm
    _ = ∫ y, f y ∂euclideanGaussianLaw κ := by
      rw [euclideanGaussianLaw_map_linearIsometryEquiv]

/-- Exact diagonal quadratic formula in Euclidean coordinates. -/
theorem euclidean_gaussian_quadratic_integral {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i < 1 / 2) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (∑ i, a i * (x i)^2) ∂euclideanGaussianLaw ι) =
      ∏ i, (Real.sqrt (1 - 2 * a i))⁻¹ := by
  rw [euclideanGaussianLaw, (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding.integral_map]
  exact gaussian_vector_quadratic_integral a ha

/-- The Euclidean diagonal quadratic estimate retains the trace exponent. -/
theorem euclidean_gaussian_quadratic_integral_le {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha : ∀ i, a i ≤ 1 / 4) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (∑ i, a i * (x i)^2) ∂euclideanGaussianLaw ι) ≤
      Real.exp (2 * ∑ i, a i) := by
  rw [euclideanGaussianLaw, (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding.integral_map]
  exact gaussian_vector_quadratic_integral_le a ha0 ha

/-- Exact arbitrary Euclidean Gaussian linear exponential integral. -/
theorem euclidean_gaussian_linear_integral {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (t * ⟪w,x⟫_ℝ) ∂euclideanGaussianLaw ι) =
      Real.exp ((t^2 / 2) * ‖w‖^2) := by
  rw [euclideanGaussianLaw, (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding.integral_map]
  have hinner : ∀ x : ι → ℝ, ⟪w, (MeasurableEquiv.toLp 2 (ι → ℝ)) x⟫_ℝ =
      ∑ i, w i * x i := by
    intro x
    simp [PiLp.inner_apply, mul_comm]
  simp_rw [hinner]
  rw [gaussian_vector_linear_integral]
  congr 2
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Integrability for the Euclidean linear exponential. -/
theorem euclidean_gaussian_linear_integrable {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (t * ⟪w,x⟫_ℝ)) (euclideanGaussianLaw ι) := by
  apply (mgf_pos_iff (X := fun x : EuclideanSpace ℝ ι => ⟪w,x⟫_ℝ) (t := t)).mp
  change 0 < ∫ x : EuclideanSpace ℝ ι, Real.exp (t * ⟪w,x⟫_ℝ) ∂euclideanGaussianLaw ι
  rw [euclidean_gaussian_linear_integral]
  exact Real.exp_pos _

/-- Nonnegative-integral version for conditional Gaussian integration. -/
theorem euclidean_gaussian_linear_lintegral {ι : Type*} [Fintype ι]
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    (∫⁻ x : EuclideanSpace ℝ ι, ENNReal.ofReal (Real.exp (t * ⟪w,x⟫_ℝ)) ∂euclideanGaussianLaw ι) =
      ENNReal.ofReal (Real.exp ((t^2 / 2) * ‖w‖^2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (euclidean_gaussian_linear_integrable w t)
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _), euclidean_gaussian_linear_integral w t]

/-- Exact Gaussian exponential norm-square integral for an arbitrary rectangular
operator, obtained from its genuine Gram spectrum and orthogonal invariance. -/
theorem gaussian_operator_normsq_integral {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (c : ℝ)
    (hc : ∀ i, c * gramEigenvalue T i < 1 / 2) :
    (∫ x : Euclid q, Real.exp (c * ‖T x‖^2) ∂euclideanGaussianLaw (Fin q)) =
      ∏ i, (Real.sqrt (1 - 2 * (c * gramEigenvalue T i)))⁻¹ := by
  calc
    (∫ x : Euclid q, Real.exp (c * ‖T x‖^2) ∂euclideanGaussianLaw (Fin q))
        = ∫ x : Euclid q, Real.exp (∑ i, (c * gramEigenvalue T i) *
            ((rightSingularBasis T).repr x i)^2) ∂euclideanGaussianLaw (Fin q) := by
      congr 1
      funext x
      rw [norm_sq_gram_diagonal, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∫ y : Euclid q, Real.exp (∑ i, (c * gramEigenvalue T i) * (y i)^2)
          ∂euclideanGaussianLaw (Fin q) :=
      euclidean_gaussian_integral_isometry (rightSingularBasis T).repr
        (fun y : Euclid q => Real.exp (∑ i, (c * gramEigenvalue T i) * (y i)^2))
    _ = ∏ i, (Real.sqrt (1 - 2 * (c * gramEigenvalue T i)))⁻¹ :=
      euclidean_gaussian_quadratic_integral _ hc

/-- Integrability for an arbitrary Gaussian operator quadratic form, derived
from the strictly positive exact spectral integral. -/
theorem gaussian_operator_normsq_integrable {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (c : ℝ)
    (hc : ∀ i, c * gramEigenvalue T i < 1 / 2) :
    Integrable (fun x : Euclid q => Real.exp (c * ‖T x‖^2)) (euclideanGaussianLaw (Fin q)) := by
  apply (mgf_pos_iff (X := fun x : Euclid q => ‖T x‖^2) (t := c)).mp
  change 0 < ∫ x : Euclid q, Real.exp (c * ‖T x‖^2) ∂euclideanGaussianLaw (Fin q)
  rw [gaussian_operator_normsq_integral T c hc]
  apply Finset.prod_pos
  intro i _
  have hd : 0 < 1 - 2 * (c * gramEigenvalue T i) := by linarith [hc i]
  exact inv_pos.mpr (Real.sqrt_pos.mpr hd)

/-- Spectral finite-radius bound, in exactly the Frobenius scale needed by
conditional bilinear cross terms. -/
theorem gaussian_operator_normsq_integral_le {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (c : ℝ) (hc0 : 0 ≤ c)
    (hcap : c * ‖T‖^2 ≤ 1 / 4) :
    (∫ x : Euclid q, Real.exp (c * ‖T x‖^2) ∂euclideanGaussianLaw (Fin q)) ≤
      Real.exp (2 * c * ‖operatorFrobenius T‖^2) := by
  have hcoef0 : ∀ i, 0 ≤ c * gramEigenvalue T i :=
    fun i => mul_nonneg hc0 (gramEigenvalue_bounds T i).1
  have hcoef : ∀ i, c * gramEigenvalue T i ≤ 1 / 4 := by
    intro i
    exact (mul_le_mul_of_nonneg_left (gramEigenvalue_bounds T i).2 hc0).trans hcap
  rw [gaussian_operator_normsq_integral T c (fun i => by linarith [hcoef i])]
  calc
    ∏ i, (Real.sqrt (1 - 2 * (c * gramEigenvalue T i)))⁻¹
        ≤ ∏ i, Real.exp (2 * (c * gramEigenvalue T i)) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        exact inv_sqrt_one_sub_le_exp _ (by linarith [hcoef0 i]) (by linarith [hcoef i])
    _ = Real.exp (2 * c * ‖operatorFrobenius T‖^2) := by
      rw [← Real.exp_sum]
      congr 1
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum, sum_gramEigenvalue]

/-- Nonnegative integral form of the operator quadratic estimate. -/
theorem gaussian_operator_normsq_lintegral_le {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (c : ℝ) (hc0 : 0 ≤ c)
    (hcap : c * ‖T‖^2 ≤ 1 / 4) :
    (∫⁻ x : Euclid q, ENNReal.ofReal (Real.exp (c * ‖T x‖^2)) ∂euclideanGaussianLaw (Fin q)) ≤
      ENNReal.ofReal (Real.exp (2 * c * ‖operatorFrobenius T‖^2)) := by
  have hcoef : ∀ i, c * gramEigenvalue T i < 1 / 2 := by
    intro i
    have hh := (mul_le_mul_of_nonneg_left (gramEigenvalue_bounds T i).2 hc0).trans hcap
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_operator_normsq_integrable T c hcoef)
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (gaussian_operator_normsq_integral_le T c hc0 hcap)

/-- Actual rectangular Gaussian bilinear finite-radius bound. The two Gaussian
vectors are independent under the displayed product measure; no determinant,
MGF, covariance, or integrability estimate is supplied as a hypothesis. -/
theorem gaussian_bilinear_lintegral_le {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (t : ℝ) (hcap : t^2 * ‖T‖^2 ≤ 1 / 2) :
    (∫⁻ p : Euclid q × Euclid r, ENNReal.ofReal (Real.exp (t * ⟪T p.1,p.2⟫_ℝ))
      ∂(euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) ≤
        ENNReal.ofReal (Real.exp (t^2 * ‖operatorFrobenius T‖^2)) := by
  rw [lintegral_prod _ (by fun_prop)]
  calc
    (∫⁻ x : Euclid q, ∫⁻ y : Euclid r, ENNReal.ofReal (Real.exp (t * ⟪T x,y⟫_ℝ))
        ∂euclideanGaussianLaw (Fin r) ∂euclideanGaussianLaw (Fin q))
        = ∫⁻ x : Euclid q, ENNReal.ofReal (Real.exp ((t^2/2) * ‖T x‖^2))
            ∂euclideanGaussianLaw (Fin q) := by
      apply lintegral_congr
      intro x
      exact euclidean_gaussian_linear_lintegral (T x) t
    _ ≤ ENNReal.ofReal (Real.exp (2 * (t^2/2) * ‖operatorFrobenius T‖^2)) :=
      gaussian_operator_normsq_lintegral_le T (t^2/2) (by positivity) (by nlinarith)
    _ = ENNReal.ofReal (Real.exp (t^2 * ‖operatorFrobenius T‖^2)) := by
      congr 2
      ring

/-- Integrability of the actual Gaussian bilinear exponential, established
from the finite nonnegative bound rather than assumed. -/
theorem gaussian_bilinear_exp_integrable {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (t : ℝ) (hcap : t^2 * ‖T‖^2 ≤ 1 / 2) :
    Integrable (fun p : Euclid q × Euclid r => Real.exp (t * ⟪T p.1,p.2⟫_ℝ))
      ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) :=
  integrable_exp_of_lintegral_bound _ _ (by fun_prop) t _ (gaussian_bilinear_lintegral_le T t hcap)

/-- The real MGF bound used in the multiscale future-cross-term argument. -/
theorem gaussian_bilinear_mgf_le {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (t : ℝ) (hcap : t^2 * ‖T‖^2 ≤ 1 / 2) :
    mgf (fun p : Euclid q × Euclid r => ⟪T p.1,p.2⟫_ℝ)
      ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) t ≤
        Real.exp (t^2 * ‖operatorFrobenius T‖^2) :=
  mgf_le_of_lintegral_bound _ _ (by fun_prop) t _ (Real.exp_nonneg _)
    (gaussian_bilinear_lintegral_le T t hcap)

#print axioms gaussian_operator_normsq_integral
#print axioms gaussian_operator_normsq_integrable
#print axioms gaussian_operator_normsq_integral_le
#print axioms gaussian_operator_normsq_lintegral_le
#print axioms gaussian_bilinear_lintegral_le
#print axioms gaussian_bilinear_exp_integrable
#print axioms gaussian_bilinear_mgf_le

#print axioms euclidean_gaussian_integral_isometry
#print axioms euclidean_gaussian_quadratic_integral
#print axioms euclidean_gaussian_quadratic_integral_le
#print axioms euclidean_gaussian_linear_integral
#print axioms euclidean_gaussian_linear_integrable
#print axioms euclidean_gaussian_linear_lintegral

end GaussianEllipsoidCandidate
