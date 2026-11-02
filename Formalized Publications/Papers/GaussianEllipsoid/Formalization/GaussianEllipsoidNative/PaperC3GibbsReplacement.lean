import PaperGibbsThirdMass
import PaperThirdQuadraticBound
import PaperCavityContraction
import PaperCavityEndpointBridge
import PaperAffineSecondStein
import UCFrobeniusReplacement
import UCNormalizedRows

/-! New reconstruction, currently proof-development support for C3 replacement.
Endpoint claims below remain proof drafts until kernel checking succeeds. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMRowInterpolation MvPolynomial
open BMFiniteGibbsTest BMFiniteGibbsHessian PaperGibbsThird PaperGibbsThirdTest
open PaperCavityThird PaperNormalizedSecondStein PaperAffineSecondStein
open PaperGibbsThirdMass PaperTensorMass PaperThirdQuadraticBound
open GaussianEllipsoid.UCFrobeniusReplacement
open scoped BigOperators BoundedContinuousFunction
namespace PaperC3GibbsReplacement
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {d m : ℕ}

/-- A Hessian coordinate has the actual third derivative as its C1 gradient. -/
def hessianSmoothTest (D : Data3 κ) (a b : κ) : SmoothTest κ where
  value := boundedHessian D.toData2 a b
  gradient c := boundedThird D a b c
  hasFDeriv y := by
    simpa only [boundedHessian_apply, boundedThird_apply] using!
      PaperGibbsThird.hasFDerivAt_hessian D a b y

def gibbsGradientTest2 (D : Data3 κ) (a : κ) : SmoothTest2 κ where
  first := gradientSmoothTest D.toData2 a
  gradientTest b := hessianSmoothTest D a b
  gradient_value b := rfl

lemma rowPoly_eq (R : Matrix (Fin d) (Fin d) ℝ) :
    PaperRowSecondStein.rowPoly R = centeredQuadratic (rowMatrix R) := by
  rw [rowMatrix, centeredQuadratic_smul]
  rfl

/-- The third derivative's mixed quadratic test is controlled by its own
sup norm, after conditioning on the independent comparison Gaussian. -/
theorem mixed_triple_abs_le (T : (κ → ℝ) →ᵇ ℝ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (A B C : Matrix (Fin d) (Fin d) ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA : spectralNorm A ≤ τ) (hB : spectralNorm B ≤ τ)
    (hFA : frobeniusSq A ≤ 1) (hFC : frobeniusSq C ≤ 1) :
    |∫ z, eval z.1 (rawQuadratic (A*B*C)) *
      T (mixMap t q g z) ∂law d m| ≤ Real.sqrt 3*τ*‖T‖ := by
  let f := T.compContinuous (mixMap t q g)
  have hi := integrable_fst_poly_mul (rawQuadratic (A*B*C)) f
  have hp (y : Fin m → ℝ) :
      |∫ x, eval x (rawQuadratic (A*B*C))*f (x,y) ∂gaussianProductLaw (Fin d)| ≤
        Real.sqrt 3*τ*‖T‖ := by
    change |boundedExpectation (f.compContinuous (firstSlice y)) (quadratic (A*B*C))| ≤ _
    apply (bounded_triple_test_le A B C _ hτ hτ1 hA hB hFA hFC).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (BoundedContinuousFunction.norm_compContinuous_le _ _).trans
      (BoundedContinuousFunction.norm_compContinuous_le _ _)
  change |∫ z, eval z.1 (rawQuadratic (A*B*C))*f z ∂law d m| ≤ _
  simp only [law]
  rw [integral_prod_symm _ hi]
  have h := norm_integral_le_of_norm_le_const (μ := gaussianProductLaw (Fin m))
    (Filter.Eventually.of_forall fun y => (show
      ‖∫ x, eval x (rawQuadratic (A*B*C))*f (x,y) ∂gaussianProductLaw (Fin d)‖ ≤
        Real.sqrt 3*τ*‖T‖ from hp y))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- Direct C3 mixed tensor bound, retaining the exact sparse replica mass. -/
theorem mixed_gibbs_third_sum_le (D : Data3 κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hop : ∀ a, spectralNorm (R a) ≤ τ) (hfrob : ∀ a, frobeniusSq (R a) ≤ 1) :
    |∑ a, ∑ b, ∑ c, ∫ z, eval z.1 (rawQuadratic (R b*R a*R c)) *
      boundedThird D a b c (mixMap t q g z) ∂law d m| ≤
      Real.sqrt 3*τ*Real.exp (3*D.beta)*
        (D.beta*‖D.potentialThird‖ +
          6*D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖ +
          6*D.beta^3*‖D.potentialDeriv‖^3) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ a, ∑ b, ∑ c, |∫ z, eval z.1 (rawQuadratic (R b*R a*R c)) *
        boundedThird D a b c (mixMap t q g z) ∂law d m| := by
      exact Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a, ∑ b, ∑ c, Real.sqrt 3*τ*‖boundedThird D a b c‖ := by
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
        Finset.sum_le_sum fun c _ => mixed_triple_abs_le _ t q g _ _ _ hτ hτ1
          (hop b) (hop a) (hfrob b) (hfrob c)
    _ = Real.sqrt 3*τ*mass (fun a b c => boundedThird D a b c) := by
      simp only [mass, ← Finset.mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (boundedThird_mass_le D hunit)
        (show 0 ≤ Real.sqrt 3*τ by positivity)
      simpa only [mul_assoc] using h

/-- Exact normalized second Stein identity under the independent-pair law. -/
theorem quadratic_product_second (F : SmoothTest2 κ) (t : ℝ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) (hR : ∀ a, (R a).transpose=R a)
    (B : κ → Fin m → ℝ) (a : κ) :
    (∫ z, eval z.1 (centeredQuadratic (rowMatrix (R a))) *
      mixedValue F.first t (fun b => centeredQuadratic (rowMatrix (R b)))
        (fun b => linearPolynomial (B b)) z ∂law d m) =
      ∑ b, (Real.cos t * Matrix.trace (R a*R b) *
        (∫ z, mixedGradient F.first t (fun e => centeredQuadratic (rowMatrix (R e)))
          (fun e => linearPolynomial (B e)) b z ∂law d m) +
        (Real.cos t)^2 * Real.sqrt 2 * ∑ c, ∫ z,
          eval z.1 (rawQuadratic (R b*R a*R c)) *
          mixedGradient (F.gradientTest b) t (fun e => centeredQuadratic (rowMatrix (R e)))
            (fun e => linearPolynomial (B e)) c z ∂law d m) := by
  let q := fun b => centeredQuadratic (rowMatrix (R b))
  let g := fun b => linearPolynomial (B b)
  let K := fun b c => rawQuadratic (R b*R a*R c)
  have hi := integrable_fst_poly_mul (q a) (mixedValue F.first t q g)
  have hh (b : κ) := integrable_bounded (mixedGradient F.first t q g b)
  have hr (b c : κ) := integrable_fst_poly_mul (K b c) (mixedGradient (F.gradientTest b) t q g c)
  have hp (y : Fin m → ℝ) :
      (∫ x, eval x (q a)*mixedValue F.first t q g (x,y) ∂gaussianProductLaw (Fin d)) =
      ∑ b, (Real.cos t*Matrix.trace (R a*R b)*
        (∫ x, mixedGradient F.first t q g b (x,y) ∂gaussianProductLaw (Fin d)) +
        (Real.cos t)^2*Real.sqrt 2*∑ c, ∫ x, eval x (K b c)*
          mixedGradient (F.gradientTest b) t q g c (x,y) ∂gaussianProductLaw (Fin d)) := by
    have h := normalized_affine_second_stein F R hR a (Real.cos t)
      (Real.sin t • polynomialFamily g y)
    simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
      composedTest, composedGradient, BoundedContinuousFunction.compContinuous_apply,
      mixedValue, mixedGradient, mixMap, polynomialFamily, ContinuousMap.coe_mk,
      eval_affinePolynomials, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, one_mul,
      q, g, K] using! h
  change (∫ z, eval z.1 (q a)*mixedValue F.first t q g z ∂law d m) = _
  simp only [law]
  rw [integral_prod_symm _ hi]
  simp_rw [hp]
  have ho (b : κ) : Integrable (fun y : Fin m → ℝ =>
      Real.cos t*Matrix.trace (R a*R b)*
        (∫ x, mixedGradient F.first t q g b (x,y) ∂gaussianProductLaw (Fin d)) +
        (Real.cos t)^2*Real.sqrt 2*∑ c, ∫ x, eval x (K b c)*
          mixedGradient (F.gradientTest b) t q g c (x,y) ∂gaussianProductLaw (Fin d))
        (gaussianProductLaw (Fin m)) :=
    ((hh b).integral_prod_right.const_mul _).add
      ((integrable_finset_sum _ (fun c _ => (hr b c).integral_prod_right)).const_mul _)
  rw [integral_finset_sum _ (fun b _ => ho b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_add ((hh b).integral_prod_right.const_mul _)
      ((integrable_finset_sum _ (fun c _ => (hr b c).integral_prod_right)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finset_sum _ (fun c _ => (hr b c).integral_prod_right),
    ← integral_prod_symm _ (hh b)]
  simp_rw [← integral_prod_symm _ (hr b _)]
  rfl

theorem linear_product_general (F : SmoothTest κ) (t : ℝ)
    (q : κ → MvPolynomial (Fin d) ℝ) (B : κ → Fin m → ℝ) (a : κ) :
    (∫ z, eval z.2 (linearPolynomial (B a))*mixedValue F t q
      (fun b => linearPolynomial (B b)) z ∂law d m) =
    Real.sin t*∑ b, (∑ i, B a i*B b i)*
      (∫ z, mixedGradient F t q (fun e => linearPolynomial (B e)) b z ∂law d m) := by
  let g := fun b => linearPolynomial (B b)
  let C := fun b => ∑ i, B a i*B b i
  have hi := integrable_snd_poly_mul (g a) (mixedValue F t q g)
  have hh (b : κ) := integrable_bounded (mixedGradient F t q g b)
  have hp (x : Fin d → ℝ) :
      (∫ y, eval y (g a)*mixedValue F t q g (x,y) ∂gaussianProductLaw (Fin m)) =
      Real.sin t*∑ b, C b*
        (∫ y, mixedGradient F t q g b (x,y) ∂gaussianProductLaw (Fin m)) := by
    have h := linear_affine_stein F B a (Real.sin t) (Real.cos t • polynomialFamily q x)
    have hswap (y : Fin m → ℝ) :
        (fun b => Real.sin t*eval y (g b)+Real.cos t*eval x (q b)) =
        (fun b => Real.cos t*eval x (q b)+Real.sin t*eval y (g b)) := by funext b; ring
    simpa only [boundedExpectation, weightedExpectation, LinearMap.coe_mk, AddHom.coe_mk,
      composedTest, composedGradient, BoundedContinuousFunction.compContinuous_apply,
      mixedValue, mixedGradient, mixMap, polynomialFamily, ContinuousMap.coe_mk,
      eval_affinePolynomials, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_one, one_mul,
      hswap, g, C] using! h
  change (∫ z, eval z.2 (g a)*mixedValue F t q g z ∂law d m) =
    Real.sin t*∑ b, C b*(∫ z, mixedGradient F t q g b z ∂law d m)
  simp only [law]
  rw [integral_prod _ hi]
  simp_rw [hp]
  rw [integral_const_mul,
    integral_finset_sum _ (fun b _ => (hh b).integral_prod_left.const_mul (C b))]
  apply congrArg (fun x : ℝ => Real.sin t*x)
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul, ← integral_prod _ (hh b)]

theorem expected_velocity_eq_second_remainder
    (F : SmoothTest κ) (H : κ → SmoothTest2 κ)
    (hH : ∀ a, (H a).first.value = F.gradient a) (t : ℝ)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) (hR : ∀ a, (R a).transpose=R a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i)=Matrix.trace (R a*R b)) :
    (∫ z, velocity F t (fun a => centeredQuadratic (rowMatrix (R a)))
      (fun a => linearPolynomial (B a)) z ∂law d m) =
      -Real.sin t*(Real.cos t)^2*Real.sqrt 2 * ∑ a, ∑ b, ∑ c,
        ∫ z, eval z.1 (rawQuadratic (R b*R a*R c)) *
          mixedGradient ((H a).gradientTest b) t
            (fun e => centeredQuadratic (rowMatrix (R e)))
            (fun e => linearPolynomial (B e)) c z ∂law d m := by
  let q := fun a => centeredQuadratic (rowMatrix (R a))
  let g := fun a => linearPolynomial (B a)
  have hv (a : κ) : mixedGradient F t q g a = mixedValue (H a).first t q g := by
    ext z
    change F.gradient a (mixMap t q g z) = (H a).first.value (mixMap t q g z)
    rw [hH]
  have ht (a : κ) :
      (∫ z, mixedGradient F t q g a z *
        (-Real.sin t*eval z.1 (q a)+Real.cos t*eval z.2 (g a)) ∂law d m) =
      -Real.sin t*(Real.cos t)^2*Real.sqrt 2 * ∑ b, ∑ c,
        ∫ z, eval z.1 (rawQuadratic (R b*R a*R c)) *
          mixedGradient ((H a).gradientTest b) t q g c z ∂law d m := by
    rw [hv]
    have hiQ := integrable_fst_poly_mul (q a) (mixedValue (H a).first t q g)
    have hiG := integrable_snd_poly_mul (g a) (mixedValue (H a).first t q g)
    have he (z : SamplePair d m) : mixedValue (H a).first t q g z *
        (-Real.sin t*eval z.1 (q a)+Real.cos t*eval z.2 (g a)) =
        -Real.sin t*(eval z.1 (q a)*mixedValue (H a).first t q g z) +
        Real.cos t*(eval z.2 (g a)*mixedValue (H a).first t q g z) := by ring
    simp_rw [he]
    rw [integral_add (hiQ.const_mul _) (hiG.const_mul _), integral_const_mul,
      integral_const_mul, quadratic_product_second (H a) t R hR B a,
      linear_product_general (H a).first t q B a]
    dsimp only [q, g]
    simp_rw [hCov, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hi (a : κ) : Integrable (fun z => mixedGradient F t q g a z *
      (-Real.sin t*eval z.1 (q a)+Real.cos t*eval z.2 (g a))) (law d m) := by
    have hq := (integrable_fst_poly_mul (q a) (mixedGradient F t q g a)).const_mul (-Real.sin t)
    have hg := (integrable_snd_poly_mul (g a) (mixedGradient F t q g a)).const_mul (Real.cos t)
    convert! hq.add hg using 1
    funext z
    dsimp only [Pi.add_apply]
    ring
  change (∫ z, ∑ a, mixedGradient F t q g a z *
      (-Real.sin t*eval z.1 (q a)+Real.cos t*eval z.2 (g a)) ∂law d m) = _
  rw [integral_finset_sum _ (fun a _ => hi a)]
  simp_rw [ht, ← Finset.mul_sum]
  rfl

/-- Generic C3 comparison, for a bounded test whose first derivatives are C2
bounded tests. The constant is dimension- and candidate-count free. -/
theorem one_row_second_replacement (F : SmoothTest κ) (H : κ → SmoothTest2 κ)
    (hH : ∀ a, (H a).first.value = F.gradient a)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) (hR : ∀ a, (R a).transpose=R a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i)=Matrix.trace (R a*R b))
    {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hop : ∀ a, spectralNorm (R a) ≤ τ) (hfrob : ∀ a, frobeniusSq (R a) ≤ 1) :
    |(∫ x, F.value (polynomialFamily (fun a => centeredQuadratic (rowMatrix (R a))) x)
        ∂gaussianProductLaw (Fin d)) -
      ∫ z, F.value (polynomialFamily (fun a => linearPolynomial (B a)) z)
        ∂gaussianProductLaw (Fin m)| ≤
      (Real.pi/2)*Real.sqrt 2*Real.sqrt 3*τ*
        mass (fun a b c => ((H a).gradientTest b).gradient c) := by
  let q := fun a => centeredQuadratic (rowMatrix (R a))
  let g := fun a => linearPolynomial (B a)
  let E := fun t => ∫ z, mixedValue F t q g z ∂law d m
  let E' := fun t => -Real.sin t*(Real.cos t)^2*Real.sqrt 2 * ∑ a, ∑ b, ∑ c,
    ∫ z, eval z.1 (rawQuadratic (R b*R a*R c))*mixedGradient ((H a).gradientTest b) t q g c z ∂law d m
  let K := Real.sqrt 2*Real.sqrt 3*τ*mass (fun a b c => ((H a).gradientTest b).gradient c)
  have hdE (t : ℝ) : HasDerivAt E (E' t) t := by
    have hd := hasDerivAt_expected_mixedValue F t q g
    rw [expected_velocity_eq_second_remainder F H hH t R hR B hCov] at hd
    exact hd
  have hsum (t : ℝ) : |∑ a, ∑ b, ∑ c, ∫ z,
      eval z.1 (rawQuadratic (R b*R a*R c))*mixedGradient ((H a).gradientTest b) t q g c z ∂law d m| ≤
      Real.sqrt 3*τ*mass (fun a b c => ((H a).gradientTest b).gradient c) := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ a, ∑ b, ∑ c, |∫ z, eval z.1 (rawQuadratic (R b*R a*R c))*
          mixedGradient ((H a).gradientTest b) t q g c z ∂law d m| := by
        exact Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a, ∑ b, ∑ c, Real.sqrt 3*τ*‖((H a).gradientTest b).gradient c‖ := by
        exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Finset.sum_le_sum fun c _ => mixed_triple_abs_le _ t q g _ _ _ hτ hτ1
            (hop b) (hop a) (hfrob b) (hfrob c)
      _ = _ := by simp only [mass, ← Finset.mul_sum]
  have hbound (t : ℝ) : ‖E' t‖ ≤ K := by
    have htrig : |(-Real.sin t)*(Real.cos t)^2| ≤ 1 := by
      rw [abs_mul, abs_neg, abs_pow]
      have hcos := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_cos_le_one t) 2
      have h := mul_le_mul (Real.abs_sin_le_one t) hcos (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      simpa using h
    change ‖((-Real.sin t)*(Real.cos t)^2*Real.sqrt 2)*_‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
    have h := mul_le_mul (mul_le_mul_of_nonneg_right htrig (Real.sqrt_nonneg 2)) (hsum t)
      (abs_nonneg _) (by positivity : (0:ℝ) ≤ 1*Real.sqrt 2)
    exact h.trans_eq (by dsimp [K]; ring)
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := (Set.univ : Set ℝ)) (x := 0) (y := Real.pi/2)
    (fun t _ => (hdE t).hasDerivWithinAt) (fun t _ => hbound t)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ _) (Set.mem_univ _)
  change ‖E (Real.pi/2)-E 0‖ ≤ K*‖Real.pi/2-0‖ at hm
  dsimp only [E] at hm
  rw [expected_mixedValue_pi_div_two, expected_mixedValue_zero, Real.norm_eq_abs,
    sub_zero, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi/2)] at hm
  rw [abs_sub_comm]
  exact hm.trans_eq (by dsimp [K]; ring)

/-- The literal shifted one-row C3 bound required by the immutable cavity
product consumer. Valid for all dimensions and nonnegative tau, including zero. -/
theorem one_row_logPartition_shifted_replacement (D : Data3 κ)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (R : κ → Matrix (Fin d) (Fin d) ℝ) (hR : ∀ a, (R a).transpose=R a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i)=Matrix.trace (R a*R b))
    (v : κ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hop : ∀ a, spectralNorm (R a) ≤ τ) (hfrob : ∀ a, frobeniusSq (R a) ≤ 1) :
    |(∫ x, logPartition D.toData
        (polynomialFamily (fun a => PaperRowSecondStein.rowPoly (R a)) x+v)
          ∂gaussianProductLaw (Fin d))-
      ∫ z, logPartition D.toData (polynomialFamily (fun a => linearPolynomial (B a)) z+v)
          ∂gaussianProductLaw (Fin m)| ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (D.beta*‖D.potentialThird‖+D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^3*‖D.potentialDeriv‖^3) := by
  let F := affineTest (smoothTest D.toData) 1 v
  let H := fun a => affineTest2 (gibbsGradientTest2 D a) 1 v
  have hH (a : κ) : (H a).first.value = F.gradient a := by
    simp only [H, F, affineTest2, affineTest, gibbsGradientTest2, gradientSmoothTest,
      smoothTest, one_smul]
  have hop1 (a : κ) : spectralNorm (R a) ≤ 1 := by
    rw [GaussianEllipsoid.UCNormalizedRows.spectralNorm_eq_matrixOpNorm]
    apply (GaussianEllipsoid.matrixOpNorm_le_frobeniusNorm _).trans
    have hsq : (GaussianEllipsoid.frobeniusNorm (R a))^2 ≤ 1 := by
      rw [GaussianEllipsoid.frobeniusNorm_sq]
      exact hfrob a
    nlinarith [GaussianEllipsoid.frobeniusNorm_nonneg (R a)]
  have hmin : 0 ≤ min τ 1 := le_min hτ (by norm_num)
  have h := one_row_second_replacement F H hH R hR B hCov hmin (min_le_right _ _)
    (fun a => le_min (hop a) (hop1 a)) hfrob
  have hmass : mass (fun a b c => ((H a).gradientTest b).gradient c) ≤
      mass (fun a b c => boundedThird D a b c) := by
    unfold mass
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro b _
    apply Finset.sum_le_sum
    intro c _
    simpa only [H, affineTest2, scaleTest, affineTest, gibbsGradientTest2,
      hessianSmoothTest, one_smul] using
      BoundedContinuousFunction.norm_compContinuous_le (boundedThird D a b c) (affineMap 1 v)
  have hmass' := hmass.trans (boundedThird_mass_le D hunit)
  have hscalar : D.beta*‖D.potentialThird‖ +
      6*D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖ +
      6*D.beta^3*‖D.potentialDeriv‖^3 ≤
      6*(D.beta*‖D.potentialThird‖+D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖+
        D.beta^3*‖D.potentialDeriv‖^3) := by
    nlinarith [mul_nonneg D.beta_nonneg (norm_nonneg D.potentialThird)]
  have hmass'' := hmass'.trans (mul_le_mul_of_nonneg_left hscalar (Real.exp_nonneg _))
  have hm0 : 0 ≤ mass (fun a b c => ((H a).gradientTest b).gradient c) := by
    unfold mass
    positivity
  have hc0 : 0 ≤ (Real.pi/2)*Real.sqrt 2*Real.sqrt 3 := by positivity
  have hb := mul_le_mul
    (mul_le_mul_of_nonneg_left (min_le_left τ 1) hc0) hmass'' hm0
    (mul_nonneg hc0 hτ)
  have he : (Real.pi/2)*Real.sqrt 2*Real.sqrt 3*τ *
      (Real.exp (3*D.beta)*(6*(D.beta*‖D.potentialThird‖+
        D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖+D.beta^3*‖D.potentialDeriv‖^3))) =
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (D.beta*‖D.potentialThird‖+D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^3*‖D.potentialDeriv‖^3) := by ring
  have hfinal := h.trans (hb.trans_eq he)
  simpa only [F, affineTest, smoothTest, boundedLogPartition,
    BoundedContinuousFunction.compContinuous_apply,
    BoundedContinuousFunction.coe_ofNormedAddCommGroup, affineMap, ContinuousMap.coe_mk,
    one_smul, rowPoly_eq] using hfinal

#print axioms mixed_gibbs_third_sum_le
#print axioms quadratic_product_second
#print axioms one_row_second_replacement
#print axioms one_row_logPartition_shifted_replacement
end PaperC3GibbsReplacement
