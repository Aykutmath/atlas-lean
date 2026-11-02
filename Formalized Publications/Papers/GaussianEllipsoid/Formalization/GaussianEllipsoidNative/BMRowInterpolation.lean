import BMAffineSmooth
import BMFiniteGibbsHessian

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth MvPolynomial Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMRowInterpolation
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {d m : ℕ}

abbrev SamplePair (d m : ℕ) := (Fin d → ℝ) × (Fin m → ℝ)

def law (d m : ℕ) : Measure (SamplePair d m) :=
  (gaussianProductLaw (Fin d)).prod (gaussianProductLaw (Fin m))

instance law_probability (d m : ℕ) : IsProbabilityMeasure (law d m) := by
  unfold law
  infer_instance

def mixMap (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) : C(SamplePair d m, κ → ℝ) where
  toFun z := Real.cos t • polynomialFamily q z.1 + Real.sin t • polynomialFamily g z.2
  continuous_toFun := by
    simpa only [Function.comp_def, Pi.smul_apply, Pi.add_apply] using!
      (((polynomialFamily q).continuous.comp continuous_fst).const_smul (Real.cos t)).add
        (((polynomialFamily g).continuous.comp continuous_snd).const_smul (Real.sin t))

def mixedValue (F : SmoothTest κ) (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) : SamplePair d m →ᵇ ℝ :=
  F.value.compContinuous (mixMap t q g)

def mixedGradient (F : SmoothTest κ) (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (a : κ) : SamplePair d m →ᵇ ℝ :=
  (F.gradient a).compContinuous (mixMap t q g)

def mixedHessian (H : κ → SmoothTest κ) (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (a b : κ) : SamplePair d m →ᵇ ℝ :=
  ((H a).gradient b).compContinuous (mixMap t q g)

theorem integrable_fst_poly (P : MvPolynomial (Fin d) ℝ) :
    Integrable (fun z : SamplePair d m => eval z.1 P) (law d m) := by
  simpa only [mul_one, law] using (gaussianProductLaw_integrable_polynomial P).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : Fin m → ℝ => (1 : ℝ)) (gaussianProductLaw (Fin m)))

theorem integrable_snd_poly (P : MvPolynomial (Fin m) ℝ) :
    Integrable (fun z : SamplePair d m => eval z.2 P) (law d m) := by
  simpa only [one_mul, law] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Fin d → ℝ => (1 : ℝ)) (gaussianProductLaw (Fin d))).mul_prod
    (gaussianProductLaw_integrable_polynomial P)

theorem integrable_bounded (f : SamplePair d m →ᵇ ℝ) : Integrable f (law d m) := by
  simpa only [mul_one] using (integrable_const (1 : ℝ) : Integrable (fun _ : SamplePair d m => (1 : ℝ)) (law d m)).bdd_mul
    f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall f.norm_coe_le_norm)

theorem integrable_fst_poly_mul (P : MvPolynomial (Fin d) ℝ) (f : SamplePair d m →ᵇ ℝ) :
    Integrable (fun z => eval z.1 P * f z) (law d m) := by
  simpa only [mul_comm] using (integrable_fst_poly P).bdd_mul
    f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall f.norm_coe_le_norm)

theorem integrable_snd_poly_mul (P : MvPolynomial (Fin m) ℝ) (f : SamplePair d m →ᵇ ℝ) :
    Integrable (fun z => eval z.2 P * f z) (law d m) := by
  simpa only [mul_comm] using (integrable_snd_poly P).bdd_mul
    f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- Exact pointwise derivative of a bounded C¹ test along row interpolation. -/
theorem hasDerivAt_mixedValue (F : SmoothTest κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (z : SamplePair d m) :
    HasDerivAt (fun u => mixedValue F u q g z)
      (∑ a, mixedGradient F t q g a z *
        (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a))) t := by
  have hi : HasDerivAt (fun u => mixMap u q g z)
      (fun a => -Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a)) t := by
    apply hasDerivAt_pi.mpr
    intro a
    simpa only [mixMap, polynomialFamily, ContinuousMap.coe_mk, Pi.smul_apply,
      Pi.add_apply, smul_eq_mul] using!
      ((Real.hasDerivAt_cos t).mul_const (eval z.1 (q a))).add
        ((Real.hasDerivAt_sin t).mul_const (eval z.2 (g a)))
  have h := (F.hasFDeriv (mixMap t q g z)).comp_hasDerivAt t hi
  simpa only [mixedValue, mixedGradient, BoundedContinuousFunction.compContinuous_apply,
    Function.comp_def, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] using h

/-- Explicit derivative integrand, before either Gaussian integration by parts. -/
def velocity (F : SmoothTest κ) (t : ℝ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (z : SamplePair d m) : ℝ :=
  ∑ a, mixedGradient F t q g a z *
    (-Real.sin t*eval z.1 (q a) + Real.cos t*eval z.2 (g a))

theorem velocity_integrable (F : SmoothTest κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    Integrable (velocity F t q g) (law d m) := by
  apply integrable_finset_sum
  intro a ha
  have hq := (integrable_fst_poly_mul (q a) (mixedGradient F t q g a)).const_mul (-Real.sin t)
  have hg := (integrable_snd_poly_mul (g a) (mixedGradient F t q g a)).const_mul (Real.cos t)
  convert hq.add hg using 1
  funext z
  dsimp only [Pi.add_apply]
  ring

/-- A t-independent integrable majorant for differentiation under the integral. -/
def velocityBound (F : SmoothTest κ) (q : κ → MvPolynomial (Fin d) ℝ)
    (g : κ → MvPolynomial (Fin m) ℝ) (z : SamplePair d m) : ℝ :=
  ∑ a, ‖F.gradient a‖ * (‖eval z.1 (q a)‖ + ‖eval z.2 (g a)‖)

theorem velocity_norm_le (F : SmoothTest κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (z : SamplePair d m) : ‖velocity F t q g z‖ ≤ velocityBound F q g z := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul]
  have hg : ‖mixedGradient F t q g a z‖ ≤ ‖F.gradient a‖ :=
    (F.gradient a).norm_coe_le_norm (mixMap t q g z)
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

theorem velocityBound_integrable (F : SmoothTest κ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    Integrable (velocityBound F q g) (law d m) := by
  exact integrable_finset_sum _ (fun a _ =>
    ((integrable_fst_poly (q a)).norm.add (integrable_snd_poly (g a)).norm).const_mul _)

/-- Fully justified interchange of differentiation and the actual product
Gaussian integral. The majorant is explicit and uses only first polynomial moments. -/
theorem hasDerivAt_expected_mixedValue (F : SmoothTest κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ) :
    HasDerivAt (fun u => ∫ z, mixedValue F u q g z ∂law d m)
      (∫ z, velocity F t q g z ∂law d m) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun u => (mixedValue F u q g).continuous.aestronglyMeasurable)
    (integrable_bounded (mixedValue F t q g))
    (velocity_integrable F t q g).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => fun u _ => velocity_norm_le F u q g z)
    (velocityBound_integrable F q g)
    (Filter.Eventually.of_forall fun z => fun u _ => hasDerivAt_mixedValue F u q g z)).2

#print axioms hasDerivAt_expected_mixedValue
#print axioms hasDerivAt_mixedValue
end BMRowInterpolation
