import BMFiniteGibbsTest

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMSmoothSteinBounds BMFiniteGibbsTest
open scoped BigOperators BoundedContinuousFunction

namespace BMFiniteGibbsHessian
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A bounded C² potential, extending the already audited finite Gibbs data. -/
structure Data2 (κ : Type*) [Fintype κ] extends Data κ where
  potentialSecond : ℝ →ᵇ ℝ
  hasDeriv_second : ∀ t, HasDerivAt potentialDeriv (potentialSecond t) t

/-- Exact coordinate Hessian of the bounded-potential finite Gibbs log-partition. -/
def hessian (D : Data2 κ) (a b : κ) (y : κ → ℝ) : ℝ :=
  (if a = b then probability D.toData y a *
    (D.beta^2 * (D.potentialDeriv (y a))^2 - D.beta * D.potentialSecond (y a)) else 0) -
  D.beta^2 * probability D.toData y a * probability D.toData y b *
    D.potentialDeriv (y a) * D.potentialDeriv (y b)

/-- The derivative of one unnormalized Gibbs weight. -/
theorem hasFDerivAt_weight (D : Data κ) (a : κ) (y : κ → ℝ) :
    HasFDerivAt (fun z : κ → ℝ => D.weight a * Real.exp (-D.beta * D.potential (z a)))
      ((D.weight a * Real.exp (-D.beta * D.potential (y a)) *
        (-D.beta) * D.potentialDeriv (y a)) •
          (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y := by
  have hp : HasFDerivAt (fun z : κ → ℝ => D.potential (z a))
      (D.potentialDeriv (y a) • (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y := by
    simpa using! (D.hasDeriv (y a)).comp_hasFDerivAt y (hasFDerivAt_apply (𝕜 := ℝ) a y)
  have he := ((hp.const_mul (-D.beta)).exp).const_mul (D.weight a)
  convert! he using 1
  ext z
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Exact derivative of a Gibbs probability, keeping the prior normalization. -/
theorem hasFDerivAt_probability (D : Data κ) (a : κ) (y : κ → ℝ) :
    HasFDerivAt (fun z => probability D z a)
      ((-D.beta * probability D y a * D.potentialDeriv (y a)) •
          (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ) +
        (D.beta * probability D y a) •
          (∑ b, (probability D y b * D.potentialDeriv (y b)) •
            (ContinuousLinearMap.proj b : (κ → ℝ) →L[ℝ] ℝ))) y := by
  have hi := (hasDerivAt_inv (ne_of_gt (partition_pos D y))).comp_hasFDerivAt y
    (hasFDerivAt_partition D y)
  have h := (hasFDerivAt_weight D a y).mul hi
  convert! h using 1
  ext z
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, probability, Function.comp_apply,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  field_simp [ne_of_gt (partition_pos D y)]
  ring_nf
  congr 2
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- The Gibbs gradient has its genuine Hessian derivative. -/
theorem hasFDerivAt_gradient (D : Data2 κ) (a : κ) (y : κ → ℝ) :
    HasFDerivAt (gradient D.toData a)
      (∑ b, hessian D a b y • (ContinuousLinearMap.proj b : (κ → ℝ) →L[ℝ] ℝ)) y := by
  have hd : HasFDerivAt (fun z : κ → ℝ => D.potentialDeriv (z a))
      (D.potentialSecond (y a) • (ContinuousLinearMap.proj a : (κ → ℝ) →L[ℝ] ℝ)) y := by
    simpa using! (D.hasDeriv_second (y a)).comp_hasFDerivAt y
      (hasFDerivAt_apply (𝕜 := ℝ) a y)
  have h := ((hasFDerivAt_probability D.toData a y).const_mul (-D.beta)).mul hd
  convert! h using 1
  ext z
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    hessian, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum, Finset.sum_mul]
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  rw [Finset.sum_neg_distrib]
  ring

/-- The Hessian contracts into only one-prior and two-prior Gibbs terms. This
identity is what permits a bound independent of the finite state count. -/
theorem hessian_contraction (D : Data2 κ) (y : κ → ℝ) (R : κ → κ → ℝ) :
    (∑ a, ∑ b, R a b * hessian D a b y) =
      (∑ a, R a a * probability D.toData y a *
        (D.beta^2 * (D.potentialDeriv (y a))^2 - D.beta * D.potentialSecond (y a))) -
      D.beta^2 * ∑ a, ∑ b, R a b * probability D.toData y a * probability D.toData y b *
        D.potentialDeriv (y a) * D.potentialDeriv (y b) := by
  simp only [hessian, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  · simp only [mul_assoc]
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring

/-- The literal trigonometric interpolation derivative of finite Gibbs free energy. -/
theorem hasDerivAt_logPartition_interpolation (D : Data κ) (q g : κ → ℝ) (t : ℝ) :
    HasDerivAt (fun u => logPartition D (fun a => Real.cos u*q a + Real.sin u*g a))
      (∑ a, gradient D a (fun b => Real.cos t*q b + Real.sin t*g b) *
        (-Real.sin t*q a + Real.cos t*g a)) t := by
  have hcurve : HasDerivAt (fun u => (fun a => Real.cos u*q a + Real.sin u*g a))
      (fun a => -Real.sin t*q a + Real.cos t*g a) t := by
    apply hasDerivAt_pi.mpr
    intro a
    exact ((Real.hasDerivAt_cos t).mul_const (q a)).add
      ((Real.hasDerivAt_sin t).mul_const (g a))
  have h := (hasFDerivAt_logPartition D (fun a => Real.cos t*q a+Real.sin t*g a)).comp_hasDerivAt t hcurve
  simpa only [Function.comp_def, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using h

#print axioms hasFDerivAt_gradient
#print axioms hessian_contraction
#print axioms hasDerivAt_logPartition_interpolation
end BMFiniteGibbsHessian
