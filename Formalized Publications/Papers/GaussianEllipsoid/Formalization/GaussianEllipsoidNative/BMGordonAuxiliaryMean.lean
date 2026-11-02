import BMSaddleProbability

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid BMGeometry GaussianTensorMoments GaussianMixedNormHelpers MeasureTheory ProbabilityTheory
namespace BMSaddle

variable {ι : Type*} [Fintype ι]

theorem shifted_coordinate_sq_integrable (i : ι) (a : ℝ) :
    Integrable (fun x : ι → ℝ => (x i-a)^2) (gaussianProductLaw ι) := by
  have h := ((gaussian_coordinate_integrable_pow i 2).sub
    ((gaussian_coordinate_integrable_pow i 1).const_mul (2*a))).add (integrable_const (a^2))
  convert! h using 1
  funext x
  change (x i-a)^2 = (x i)^2-2*a*(x i)^1+a^2
  ring

theorem shifted_coordinate_sq_mean (i : ι) (a : ℝ) :
    (∫ x : ι → ℝ, (x i-a)^2 ∂gaussianProductLaw ι) = 1+a^2 := by
  have hi : Integrable (fun x : ι → ℝ => (x i)^2-2*a*x i) (gaussianProductLaw ι) :=
    (gaussian_coordinate_integrable_pow i 2).sub
      (by simpa only [pow_one] using (gaussian_coordinate_integrable_pow i 1).const_mul (2*a))
  simp_rw [show ∀ x : ι → ℝ, (x i-a)^2=(x i)^2-2*a*x i+a^2 by intro x; ring]
  rw [integral_add hi (integrable_const _), integral_sub (gaussian_coordinate_integrable_pow i 2)
    (by simpa only [pow_one] using (gaussian_coordinate_integrable_pow i 1).const_mul (2*a)), integral_const_mul]
  simp [gaussian_coordinate_second, gaussian_coordinate_mean]

theorem shifted_norm_lipschitz (a : EuclideanSpace ℝ ι) : LipschitzWith 1 (fun x => ‖x-a‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm]
  simpa only [sub_sub_sub_cancel_right, Real.norm_eq_abs] using abs_norm_sub_norm_le (x-a) (y-a)

/-- Actual second moment of a shifted iid standard Gaussian, with arbitrary deterministic shift. -/
theorem shifted_gaussian_norm_second (a : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, ‖x-a‖^2 ∂euclideanGaussianLaw ι) =
      (Fintype.card ι : ℝ)+‖a‖^2 := by
  rw [euclideanGaussianLaw, integral_map (f := fun x : EuclideanSpace ℝ ι => ‖x-a‖^2)
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable
    ((continuous_id.sub continuous_const).norm.pow 2).aestronglyMeasurable]
  simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  change (∫ x : ι → ℝ, ∑ i, (x i-a i)^2 ∂gaussianProductLaw ι) = _
  rw [integral_finset_sum _ (fun i _ => shifted_coordinate_sq_integrable i (a i))]
  simp only [shifted_coordinate_sq_mean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]

/-- Jensen/Cauchy bound derived from actual nonnegative Gaussian variance. -/
theorem shifted_gaussian_norm_mean_le (a : EuclideanSpace ℝ ι) :
    (∫ x : EuclideanSpace ℝ ι, ‖x-a‖ ∂euclideanGaussianLaw ι) ≤
      Real.sqrt ((Fintype.card ι : ℝ)+‖a‖^2) := by
  have hsq := GaussianVariance.lipschitz_sq_integrable (shifted_norm_lipschitz a)
  have hm := (memLp_two_iff_integrable_sq (shifted_norm_lipschitz a).continuous.aestronglyMeasurable).mpr hsq
  have hv := variance_nonneg (fun x : EuclideanSpace ℝ ι => ‖x-a‖) (euclideanGaussianLaw ι)
  rw [variance_eq_sub hm] at hv
  simp only [Pi.pow_apply,shifted_gaussian_norm_second] at hv
  apply (sq_le_sq₀ (integral_nonneg (fun _ => norm_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  linarith

/-- The exact drift-norm bound used after expectation Gordon. -/
theorem gaussian_drift_mean_le (n : ℕ) (R : ℝ) :
    (∫ h : Euclid n, ‖h-R⁻¹ • ones n‖ ∂euclideanGaussianLaw (Fin n)) ≤
      Real.sqrt ((n:ℝ)*(1+(R⁻¹)^2)) := by
  have h := shifted_gaussian_norm_mean_le (R⁻¹ • ones n)
  have heq : (Fintype.card (Fin n):ℝ)+‖R⁻¹ • ones n‖^2 = (n:ℝ)*(1+(R⁻¹)^2) := by
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,ones_norm,
      Real.sq_sqrt (Nat.cast_nonneg n)]
    simp only [Fintype.card_fin]
    ring
  rwa [heq] at h

/-- The exact unresolved expectation-Gordon boundary, before the separately proved
auxiliary Gaussian drift estimate. Both sides use the actual concrete Gaussian laws. -/
def ExpectedGordonComparison (n d : ℕ) (κ R : ℝ) : Prop :=
  conditionedWidth d κ - (∫ h : Euclid n, ‖h-R⁻¹ • ones n‖ ∂euclideanGaussianLaw (Fin n)) ≤
    statisticMean n d κ R

theorem expectedGordonLower_of_comparison {n d : ℕ} {κ R : ℝ}
    (hG : ExpectedGordonComparison n d κ R) : ExpectedGordonLower n d κ R := by
  have h := gaussian_drift_mean_le n R
  unfold ExpectedGordonComparison at hG
  unfold ExpectedGordonLower
  linarith

end BMSaddle
