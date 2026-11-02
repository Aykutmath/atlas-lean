import BMRowInterpolation

/-!
Actual-law two-Gaussian interpolation for affine Gordon comparison.
Deterministic shifts are applied to the test function, never to the claim
that a Gaussian process is centered.  No Gaussian comparison is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMRowInterpolation MvPolynomial Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMGordonAffineInterpolation
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {d m : ℕ}

/-- Stein in the first independent linear Gaussian source. -/
theorem first_linear_product_stein (F : SmoothTest κ) (t : ℝ)
    (A : κ → Fin d → ℝ) (B : κ → Fin m → ℝ) (a : κ) :
    (∫ z, eval z.1 (linearPolynomial (A a)) * mixedValue F t
      (fun b => linearPolynomial (A b)) (fun b => linearPolynomial (B b)) z ∂law d m) =
    Real.cos t * ∑ b, (∑ i, A a i*A b i) *
      (∫ z, mixedGradient F t (fun b => linearPolynomial (A b))
        (fun b => linearPolynomial (B b)) b z ∂law d m) := by
  let q := fun b => linearPolynomial (A b)
  let g := fun b => linearPolynomial (B b)
  let C := fun b => ∑ i, A a i*A b i
  have hi := integrable_fst_poly_mul (q a) (mixedValue F t q g)
  have hh (b : κ) := integrable_bounded (mixedGradient F t q g b)
  have hp (y : Fin m → ℝ) :
      (∫ x, eval x (q a) * mixedValue F t q g (x,y) ∂gaussianProductLaw (Fin d)) =
      Real.cos t * ∑ b, C b *
        (∫ x, mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin d)) := by
    have h := linear_affine_stein F A a (Real.cos t)
      (Real.sin t • polynomialFamily g y)
    simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
      composedTest, composedGradient, BoundedContinuousFunction.compContinuous_apply,
      mixedValue, mixedGradient, mixMap, polynomialFamily, ContinuousMap.coe_mk,
      eval_affinePolynomials, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, one_mul,
      q, g, C] using! h
  change (∫ z, eval z.1 (q a)*mixedValue F t q g z ∂law d m) =
    Real.cos t * ∑ b, C b * (∫ z, mixedGradient F t q g b z ∂law d m)
  simp only [law]
  rw [integral_prod_symm _ hi]
  simp_rw [hp]
  rw [integral_const_mul]
  rw [integral_finset_sum _ (fun b _ => (hh b).integral_prod_right.const_mul (C b))]
  apply congrArg (fun x : ℝ => Real.cos t*x)
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_const_mul, ← integral_prod_symm _ (hh b)]

/-- Stein in the second independent linear Gaussian source. -/
theorem second_linear_product_stein (F : SmoothTest κ) (t : ℝ)
    (A : κ → Fin d → ℝ) (B : κ → Fin m → ℝ) (a : κ) :
    (∫ z, eval z.2 (linearPolynomial (B a)) * mixedValue F t
      (fun b => linearPolynomial (A b)) (fun b => linearPolynomial (B b)) z ∂law d m) =
    Real.sin t * ∑ b, (∑ i, B a i*B b i) *
      (∫ z, mixedGradient F t (fun b => linearPolynomial (A b))
        (fun b => linearPolynomial (B b)) b z ∂law d m) := by
  let q := fun b => linearPolynomial (A b)
  let g := fun b => linearPolynomial (B b)
  let C := fun b => ∑ i, B a i*B b i
  have hi := integrable_snd_poly_mul (g a) (mixedValue F t q g)
  have hh (b : κ) := integrable_bounded (mixedGradient F t q g b)
  have hp (x : Fin d → ℝ) :
      (∫ y, eval y (g a) * mixedValue F t q g (x,y) ∂gaussianProductLaw (Fin m)) =
      Real.sin t * ∑ b, C b *
        (∫ y, mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin m)) := by
    have h := linear_affine_stein F B a (Real.sin t) (Real.cos t • polynomialFamily q x)
    have hswap (y : Fin m → ℝ) :
        (fun b => Real.sin t*eval y (g b) + Real.cos t*eval x (q b)) =
        (fun b => Real.cos t*eval x (q b) + Real.sin t*eval y (g b)) := by funext b; ring
    simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
      composedTest, composedGradient, BoundedContinuousFunction.compContinuous_apply,
      mixedValue, mixedGradient, mixMap, polynomialFamily, ContinuousMap.coe_mk,
      eval_affinePolynomials, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, one_mul,
      hswap, q, g, C] using! h
  change (∫ z, eval z.2 (g a)*mixedValue F t q g z ∂law d m) =
    Real.sin t * ∑ b, C b * (∫ z, mixedGradient F t q g b z ∂law d m)
  simp only [law]
  rw [integral_prod _ hi]
  simp_rw [hp]
  rw [integral_const_mul]
  rw [integral_finset_sum _ (fun b _ => (hh b).integral_prod_left.const_mul (C b))]
  apply congrArg (fun x : ℝ => Real.sin t*x)
  apply Finset.sum_congr rfl
  intro b hb
  rw [integral_const_mul, ← integral_prod _ (hh b)]

/-- C² test with bounded first and second derivatives.  The value need not be
bounded; in particular this class accommodates the nested log-sum-exp. -/
structure C2Test (κ : Type*) [Fintype κ] where
  value : C((κ → ℝ), ℝ)
  gradient : κ → SmoothTest κ
  hasFDeriv : ∀ y, HasFDerivAt (𝕜 := ℝ) (fun y => value y)
    (∑ b, ((gradient b).value y) •
      (ContinuousLinearMap.proj b : (κ → ℝ) →L[ℝ] ℝ)) y

def C2Test.translate (F : C2Test κ) (v : κ → ℝ) : C2Test κ where
  value := F.value.comp (affineMap 1 v)
  gradient a := affineTest (F.gradient a) 1 v
  hasFDeriv y := by
    have hi := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul (1:ℝ)).add_const v
    have h := (F.hasFDeriv _).comp y hi
    convert! h using 1
    ext z
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.id_apply, ContinuousMap.comp_apply,
      BoundedContinuousFunction.compContinuous_apply, affineTest, affineMap,
      ContinuousMap.coe_mk, Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, id_eq]

/-- Unbounded value along the actual independent Gaussian interpolation. -/
def value (F : C2Test κ) (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (z : SamplePair d m) : ℝ :=
  F.value (mixMap t q g z)

def velocity (F : C2Test κ) (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (z : SamplePair d m) : ℝ :=
  ∑ a, mixedValue (F.gradient a) t q g z *
    (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a))

theorem hasDerivAt_value (F : C2Test κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (z : SamplePair d m) :
    HasDerivAt (fun u => value F u q g z) (velocity F t q g z) t := by
  have hi : HasDerivAt (fun u => mixMap u q g z)
      (fun a => -Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) t := by
    apply hasDerivAt_pi.mpr
    intro a
    exact ((Real.hasDerivAt_cos t).mul_const _).add ((Real.hasDerivAt_sin t).mul_const _)
  have h := (F.hasFDeriv (mixMap t q g z)).comp_hasDerivAt t hi
  simpa only [value, velocity, mixedValue, BoundedContinuousFunction.compContinuous_apply,
    Function.comp_def, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] using! h

theorem velocity_integrable (F : C2Test κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    Integrable (velocity F t q g) (law d m) := by
  apply integrable_finset_sum
  intro a ha
  have hq := (integrable_fst_poly_mul (q a) (mixedValue (F.gradient a) t q g)).const_mul (-Real.sin t)
  have hg := (integrable_snd_poly_mul (g a) (mixedValue (F.gradient a) t q g)).const_mul (Real.cos t)
  convert! hq.add hg using 1
  funext z
  dsimp only [Pi.add_apply]
  ring

def velocityBound (F : C2Test κ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (z : SamplePair d m) : ℝ :=
  ∑ a, ‖(F.gradient a).value‖ * (‖eval z.1 (q a)‖ + ‖eval z.2 (g a)‖)

theorem velocity_norm_le (F : C2Test κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (z : SamplePair d m) : ‖velocity F t q g z‖ ≤ velocityBound F q g z := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  have hg : ‖mixedValue (F.gradient a) t q g z‖ ≤ ‖(F.gradient a).value‖ :=
    (F.gradient a).value.norm_coe_le_norm (mixMap t q g z)
  have hv : ‖-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)‖ ≤
      ‖eval z.1 (q a)‖ + ‖eval z.2 (g a)‖ := by
    calc
      _ ≤ ‖-Real.sin t*eval z.1 (q a)‖ + ‖Real.cos t*eval z.2 (g a)‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul, norm_neg, Real.norm_eq_abs]
        nlinarith [Real.abs_sin_le_one t, Real.abs_cos_le_one t,
          mul_nonneg (sub_nonneg.mpr (Real.abs_sin_le_one t)) (abs_nonneg (eval z.1 (q a))),
          mul_nonneg (sub_nonneg.mpr (Real.abs_cos_le_one t)) (abs_nonneg (eval z.2 (g a)))]
  exact mul_le_mul hg hv (norm_nonneg _) (norm_nonneg _)

theorem velocityBound_integrable (F : C2Test κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    Integrable (velocityBound F q g) (law d m) := by
  exact integrable_finset_sum _ (fun a _ =>
    ((integrable_fst_poly (q a)).norm.add (integrable_snd_poly (g a)).norm).const_mul _)

/-- Differentiation under the integral for the unbounded smooth min-max class.
Only ordinary value integrability remains as an analytic hypothesis. -/
theorem hasDerivAt_expected_value (F : C2Test κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (hInt : Integrable (value F t q g) (law d m)) :
    HasDerivAt (fun u => ∫ z, value F u q g z ∂law d m)
      (∫ z, velocity F t q g z ∂law d m) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun u => (F.value.continuous.comp (mixMap u q g).continuous).aestronglyMeasurable)
    hInt (velocity_integrable F t q g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => fun u _ => velocity_norm_le F u q g z)
    (velocityBound_integrable F q g)
    (Filter.Eventually.of_forall fun z => fun u _ => hasDerivAt_value F u q g z)).2

/-- Exact covariance difference in the derivative: both Gaussian laws are
literal product standard Gaussians, and their covariances are coefficient sums. -/
theorem expected_velocity_eq_covariance_contraction (F : C2Test κ) (t : ℝ)
    (A : κ → Fin d → ℝ) (B : κ → Fin m → ℝ) :
    (∫ z, velocity F t (fun b => linearPolynomial (A b))
      (fun b => linearPolynomial (B b)) z ∂law d m) =
    Real.sin t*Real.cos t * ∑ a, ∑ b,
      ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) *
        (∫ z, mixedGradient (F.gradient a) t (fun b => linearPolynomial (A b))
          (fun b => linearPolynomial (B b)) b z ∂law d m) := by
  let q := fun b => linearPolynomial (A b)
  let g := fun b => linearPolynomial (B b)
  have hterm (a : κ) :
      (∫ z, mixedValue (F.gradient a) t q g z *
          (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) ∂law d m) =
        Real.sin t*Real.cos t * ∑ b,
          ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) *
            (∫ z, mixedGradient (F.gradient a) t q g b z ∂law d m) := by
    have hiQ := integrable_fst_poly_mul (q a) (mixedValue (F.gradient a) t q g)
    have hiG := integrable_snd_poly_mul (g a) (mixedValue (F.gradient a) t q g)
    have he (z : SamplePair d m) : mixedValue (F.gradient a) t q g z *
        (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) =
        -Real.sin t * (eval z.1 (q a)*mixedValue (F.gradient a) t q g z) +
        Real.cos t * (eval z.2 (g a)*mixedValue (F.gradient a) t q g z) := by ring
    simp_rw [he]
    rw [integral_add (hiQ.const_mul (-Real.sin t)) (hiG.const_mul (Real.cos t)),
      integral_const_mul, integral_const_mul,
      first_linear_product_stein (F.gradient a) t A B a,
      second_linear_product_stein (F.gradient a) t A B a]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  change (∫ z, ∑ a, mixedValue (F.gradient a) t q g z *
      (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) ∂law d m) = _
  have hti (a : κ) : Integrable (fun z => mixedValue (F.gradient a) t q g z *
      (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a))) (law d m) := by
    have hq := (integrable_fst_poly_mul (q a) (mixedValue (F.gradient a) t q g)).const_mul (-Real.sin t)
    have hg := (integrable_snd_poly_mul (g a) (mixedValue (F.gradient a) t q g)).const_mul (Real.cos t)
    convert! hq.add hg using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  rw [integral_finset_sum _ (fun a _ => hti a)]
  simp_rw [hterm]
  rw [← Finset.mul_sum]

/-- Exact affine Gaussian interpolation formula.  The deterministic translation
appears inside the Hessian; there is no centeredness claim for shifted values. -/
theorem hasDerivAt_expected_affine_value (F : C2Test κ) (v : κ → ℝ) (t : ℝ)
    (A : κ → Fin d → ℝ) (B : κ → Fin m → ℝ)
    (hInt : Integrable (value (F.translate v) t (fun b => linearPolynomial (A b))
      (fun b => linearPolynomial (B b))) (law d m)) :
    HasDerivAt (fun u => ∫ z, value (F.translate v) u (fun b => linearPolynomial (A b))
        (fun b => linearPolynomial (B b)) z ∂law d m)
      (Real.sin t*Real.cos t * ∑ a, ∑ b,
        ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) *
          (∫ z, mixedGradient ((F.translate v).gradient a) t
            (fun b => linearPolynomial (A b)) (fun b => linearPolynomial (B b)) b z ∂law d m)) t := by
  rw [← expected_velocity_eq_covariance_contraction]
  exact hasDerivAt_expected_value _ t _ _ hInt

/-- Gaussian expectation comparison from the pointwise covariance-Hessian sign.
This is an analytic sign criterion, not a finite min-max comparison premise. -/
theorem expected_value_le_of_covariance_hessian_sign (F : C2Test κ)
    (A : κ → Fin d → ℝ) (B : κ → Fin m → ℝ)
    (hInt : ∀ t, Integrable (value F t (fun b => linearPolynomial (A b))
      (fun b => linearPolynomial (B b))) (law d m))
    (hSign : ∀ a b y,
      0 ≤ ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) * (F.gradient a).gradient b y) :
    (∫ x, F.value (polynomialFamily (fun a => linearPolynomial (A a)) x)
      ∂gaussianProductLaw (Fin d)) ≤
    (∫ y, F.value (polynomialFamily (fun a => linearPolynomial (B a)) y)
      ∂gaussianProductLaw (Fin m)) := by
  let q := fun b => linearPolynomial (A b)
  let g := fun b => linearPolynomial (B b)
  let f := fun t => ∫ z, value F t q g z ∂law d m
  let f' := fun t => Real.sin t*Real.cos t * ∑ a, ∑ b,
    ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) *
      (∫ z, mixedGradient (F.gradient a) t q g b z ∂law d m)
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    dsimp only [f, f']
    rw [← expected_velocity_eq_covariance_contraction]
    exact hasDerivAt_expected_value F t q g (hInt t)
  have hnonneg (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) (Real.pi/2)) : 0 ≤ f' t := by
    apply mul_nonneg
    · exact mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, Real.pi_pos]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    · apply Finset.sum_nonneg
      intro a ha
      apply Finset.sum_nonneg
      intro b hb
      rw [← integral_const_mul]
      apply integral_nonneg
      intro z
      exact hSign a b (mixMap t q g z)
  have hmono : MonotoneOn f (Set.Icc (0:ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · exact fun t ht => (hd t).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t).hasDerivWithinAt
    · exact fun t ht => hnonneg t (interior_subset ht)
  have hh : f 0 ≤ f (Real.pi/2) := hmono
    ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩ (by positivity)
  have hzero : f 0 = ∫ x, F.value (polynomialFamily q x) ∂gaussianProductLaw (Fin d) := by
    dsimp only [f, value, mixMap, ContinuousMap.coe_mk]
    simp only [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
    exact (integral_fun_fst (μ := gaussianProductLaw (Fin d))
      (ν := gaussianProductLaw (Fin m)) (fun x => F.value (polynomialFamily q x))).trans (by simp)
  have hlast : f (Real.pi/2) = ∫ y, F.value (polynomialFamily g y) ∂gaussianProductLaw (Fin m) := by
    dsimp only [f, value, mixMap, ContinuousMap.coe_mk]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, one_smul, zero_smul, zero_add]
    exact (integral_fun_snd (μ := gaussianProductLaw (Fin d))
      (ν := gaussianProductLaw (Fin m)) (fun y => F.value (polynomialFamily g y))).trans (by simp)
  rwa [hzero, hlast] at hh

/-- A common deterministic shift leaves the covariance-Hessian comparison valid. -/
theorem expected_affine_value_le_of_covariance_hessian_sign (F : C2Test κ)
    (v : κ → ℝ) (A : κ → Fin d → ℝ) (B : κ → Fin m → ℝ)
    (hInt : ∀ t, Integrable (value (F.translate v) t (fun b => linearPolynomial (A b))
      (fun b => linearPolynomial (B b))) (law d m))
    (hSign : ∀ a b y,
      0 ≤ ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) * (F.gradient a).gradient b y) :
    (∫ x, F.value (polynomialFamily (fun a => linearPolynomial (A a)) x + v)
      ∂gaussianProductLaw (Fin d)) ≤
    (∫ y, F.value (polynomialFamily (fun a => linearPolynomial (B a)) y + v)
      ∂gaussianProductLaw (Fin m)) := by
  have h := expected_value_le_of_covariance_hessian_sign (F.translate v) A B hInt
    (fun a b y => by
      simpa only [C2Test.translate, affineTest, BoundedContinuousFunction.smul_apply,
        BoundedContinuousFunction.compContinuous_apply, affineMap, ContinuousMap.coe_mk,
        one_smul, smul_eq_mul, one_mul] using hSign a b (y+v))
  simpa only [C2Test.translate, ContinuousMap.comp_apply, affineMap,
    ContinuousMap.coe_mk, one_smul] using! h

#print axioms hasDerivAt_expected_affine_value
#print axioms expected_affine_value_le_of_covariance_hessian_sign
end BMGordonAffineInterpolation
