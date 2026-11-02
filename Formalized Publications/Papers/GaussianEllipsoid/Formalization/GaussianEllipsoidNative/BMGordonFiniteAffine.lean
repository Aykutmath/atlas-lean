import BMGordonSoftMinMaxTest
import BMGordonSoftMinMaxExpectation

/-! Finite affine Gordon comparison for concrete linear Gaussian processes.
The proof differentiates the genuine nested soft minmax along the actual
independent Gaussian interpolation, checks the covariance-Hessian sign,
and takes the zero-temperature limit. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMRowInterpolation MvPolynomial Filter
open BMGordonAffineInterpolation BMGordonSoftMinMax
open scoped BigOperators BoundedContinuousFunction

namespace BMGordonFiniteAffine
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
variable {d m : ℕ}

/-- Finite affine Gordon comparison for literal linear forms of standard Gaussians.
The covariance agrees within every row, and the second covariance is larger
between rows. The common deterministic shift is completely arbitrary. -/
theorem minMax_expectation_le
    (A : I × J → Fin d → ℝ) (B : I × J → Fin m → ℝ) (v : I × J → ℝ)
    (hSame : ∀ a b, a.1 = b.1 → (∑ i, A a i*A b i) = (∑ i, B a i*B b i))
    (hCov : ∀ a b, (∑ i, A a i*A b i) ≤ (∑ i, B a i*B b i)) :
    (∫ x, minMax (polynomialFamily (fun a => linearPolynomial (A a)) x + v)
      ∂gaussianProductLaw (Fin d)) ≤
    (∫ y, minMax (polynomialFamily (fun a => linearPolynomial (B a)) y + v)
      ∂gaussianProductLaw (Fin m)) := by
  let q := fun a => linearPolynomial (A a)
  let g := fun a => linearPolynomial (B a)
  have hAx : Continuous (fun x : Fin d → ℝ => polynomialFamily q x + v) :=
    (polynomialFamily q).continuous.add continuous_const
  have hBx : Continuous (fun y : Fin m → ℝ => polynomialFamily g y + v) :=
    (polynomialFamily g).continuous.add continuous_const
  have hAi (a : I × J) : Integrable (fun x : Fin d → ℝ => (polynomialFamily q x + v) a)
      (gaussianProductLaw (Fin d)) :=
    (gaussianProductLaw_integrable_polynomial (q a)).add (integrable_const (v a))
  have hBi (a : I × J) : Integrable (fun y : Fin m → ℝ => (polynomialFamily g y + v) a)
      (gaussianProductLaw (Fin m)) :=
    (gaussianProductLaw_integrable_polynomial (g a)).add (integrable_const (v a))
  have hsmooth (β : ℝ) (hβ : 0 < β) :
      (∫ x, softMinMax β (polynomialFamily q x + v) ∂gaussianProductLaw (Fin d)) ≤
      (∫ y, softMinMax β (polynomialFamily g y + v) ∂gaussianProductLaw (Fin m)) := by
    let F := softMinMaxTest (I := I) (J := J) β (ne_of_gt hβ)
    have hInt (t : ℝ) : Integrable
        (BMGordonAffineInterpolation.value (F.translate v) t q g) (law d m) := by
      have hc : Continuous (fun z : SamplePair d m => mixMap t q g z + v) :=
        (mixMap t q g).continuous.add continuous_const
      have hi (a : I × J) : Integrable
          (fun z : SamplePair d m => (mixMap t q g z + v) a) (law d m) := by
        exact (((integrable_fst_poly (q a)).const_mul (Real.cos t)).add
          ((integrable_snd_poly (g a)).const_mul (Real.sin t))).add (integrable_const (v a))
      have h := softMinMax_integrable (law d m) β hβ _ hc hi
      simpa only [BMGordonAffineInterpolation.value, C2Test.translate,
        ContinuousMap.comp_apply, affineMap, ContinuousMap.coe_mk, one_smul,
        F, softMinMaxTest_value] using! h
    have hsign (a b : I × J) (y : I × J → ℝ) :
        0 ≤ ((∑ i, B a i*B b i) - (∑ i, A a i*A b i)) * (F.gradient a).gradient b y := by
      change 0 ≤ _ * hessian β y a b
      by_cases hab : a.1 = b.1
      · rw [hSame a b hab, sub_self, zero_mul]
      · exact mul_nonneg (sub_nonneg.mpr (hCov a b))
          (hessian_nonneg_of_row_ne β hβ.le y a b hab)
    have h := expected_affine_value_le_of_covariance_hessian_sign F v A B hInt hsign
    simpa only [F, softMinMaxTest_value] using! h
  apply le_of_tendsto_of_tendsto
    (tendsto_expected_softMinMax (gaussianProductLaw (Fin d)) _ hAx hAi)
    (tendsto_expected_softMinMax (gaussianProductLaw (Fin m)) _ hBx hBi)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with β hβ
  exact hsmooth β hβ

/-- Coordinate-sum formulation, with no polynomial API or comparison premise. -/
theorem minMax_expectation_le_linear
    (A : I × J → Fin d → ℝ) (B : I × J → Fin m → ℝ) (v : I × J → ℝ)
    (hSame : ∀ a b, a.1 = b.1 → (∑ i, A a i*A b i) = (∑ i, B a i*B b i))
    (hCov : ∀ a b, (∑ i, A a i*A b i) ≤ (∑ i, B a i*B b i)) :
    (∫ x, minMax (fun a => (∑ i, A a i*x i) + v a) ∂gaussianProductLaw (Fin d)) ≤
    (∫ y, minMax (fun a => (∑ i, B a i*y i) + v a) ∂gaussianProductLaw (Fin m)) := by
  have h := minMax_expectation_le A B v hSame hCov
  simpa only [polynomialFamily, ContinuousMap.coe_mk, linearPolynomial,
    map_sum, MvPolynomial.smul_eq_C_mul, eval_mul, eval_C, eval_X, Pi.add_def] using h

#print axioms minMax_expectation_le
#print axioms minMax_expectation_le_linear
end BMGordonFiniteAffine
