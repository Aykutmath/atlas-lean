import GaussianProductMoments
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic

/-! Actual product-Gaussian polynomial integration by parts. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators

namespace GaussianTensorMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Extract a designated coordinate from a monomial after changing its exponent. -/
theorem prod_power_update (k : ι → ℕ) (i : ι) (n : ℕ) (x : ι → ℝ) :
    (∏ j, x j ^ Function.update k i n j) =
      x i ^ n * ∏ j ∈ Finset.univ.erase i, x j ^ k j := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun j => x j ^ Function.update k i n j)
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- Multiplication by a coordinate raises exactly that exponent. -/
theorem coordinate_mul_prod_powers (k : ι → ℕ) (i : ι) (x : ι → ℝ) :
    x i * (∏ j, x j ^ k j) = ∏ j, x j ^ Function.update k i (k i+1) j := by
  classical
  rw [prod_power_update, ← Finset.mul_prod_erase Finset.univ (fun j => x j ^ k j)
    (Finset.mem_univ i), pow_succ']
  ring

/-- Fubini with one designated exponent gives a scalar moment times the rest. -/
theorem gaussianProductLaw_moment_update (k : ι → ℕ) (i : ι) (n : ℕ) :
    (∫ x, ∏ j, x j ^ Function.update k i n j ∂gaussianProductLaw ι) =
      (∫ x : ℝ, x^n ∂gaussianReal 0 1) *
        ∏ j ∈ Finset.univ.erase i, ∫ x : ℝ, x^(k j) ∂gaussianReal 0 1 := by
  classical
  rw [gaussianProductLaw_monomial_moment]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => ∫ x : ℝ, x^(Function.update k i n j) ∂gaussianReal 0 1) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

/-- Product-Gaussian integration by parts for one monomial, with all moments
integrated under the actual product law. -/
theorem gaussianProductLaw_monomial_stein (k : ι → ℕ) (i : ι) :
    (∫ x, x i * (∏ j, x j^k j) ∂gaussianProductLaw ι) =
      (k i : ℝ) * ∫ x, ∏ j, x j^Function.update k i (k i-1) j ∂gaussianProductLaw ι := by
  classical
  simp_rw [coordinate_mul_prod_powers]
  rw [gaussianProductLaw_moment_update, gaussianProductLaw_moment_update]
  cases hn : k i with
  | zero => simp [standardGaussian_moment_one]
  | succ n =>
    simp only [Nat.add_sub_cancel, Nat.succ_eq_add_one]
    rw [standardGaussian_moment_succ_succ]
    ring

/-- Finite-type form of multivariate monomial evaluation. -/
theorem eval_monomial_fintype (k : ι →₀ ℕ) (a : ℝ) (x : ι → ℝ) :
    MvPolynomial.eval x (MvPolynomial.monomial k a) = a * ∏ j, x j ^ k j := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

/-- Every multivariate polynomial is integrable under the actual iid Gaussian law. -/
theorem gaussianProductLaw_integrable_polynomial (P : MvPolynomial ι ℝ) :
    Integrable (fun x => MvPolynomial.eval x P) (gaussianProductLaw ι) := by
  induction P using MvPolynomial.induction_on' with
  | monomial k a =>
    simp_rw [eval_monomial_fintype]
    exact (gaussianProductLaw_integrable_monomial k).const_mul a
  | add P Q hP hQ =>
    simp_rw [MvPolynomial.eval_add]
    exact hP.add hQ

/-- Subtracting one basis exponent is the same as updating that coordinate. -/
theorem finsupp_sub_single_coe (k : ι →₀ ℕ) (i : ι) :
    (fun j : ι => (k-Finsupp.single i 1 : ι →₀ ℕ) j) =
      Function.update (fun j => k j) i (k i-1) := by
  classical
  funext j
  by_cases hji : j=i
  · subst j; simp
  · simp [hji, Ne.symm hji]

/-- Full polynomial Stein identity for the finite iid standard Gaussian law. -/
theorem gaussianProductLaw_polynomial_stein (P : MvPolynomial ι ℝ) (i : ι) :
    (∫ x, x i * MvPolynomial.eval x P ∂gaussianProductLaw ι) =
      ∫ x, MvPolynomial.eval x (MvPolynomial.pderiv i P) ∂gaussianProductLaw ι := by
  have hxp (P : MvPolynomial ι ℝ) :
      Integrable (fun x => x i * MvPolynomial.eval x P) (gaussianProductLaw ι) := by
    have h := gaussianProductLaw_integrable_polynomial (MvPolynomial.X i*P)
    convert h using 1
    funext x
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, MvPolynomial.eval_add, mul_add]
    rw [integral_add (hxp P) (hxp Q),
      integral_add (gaussianProductLaw_integrable_polynomial _) (gaussianProductLaw_integrable_polynomial _),
      hP, hQ]
  | monomial k a =>
    simp only [MvPolynomial.pderiv_monomial, eval_monomial_fintype]
    have hl (x : ι → ℝ) : x i*(a*∏ j, x j^k j) = a*(x i*∏ j, x j^k j) := by ring
    simp_rw [hl]
    rw [integral_const_mul, integral_const_mul, gaussianProductLaw_monomial_stein]
    have hsub := finsupp_sub_single_coe k i
    have hr (x : ι → ℝ) : (∏ j, x j^((k-Finsupp.single i 1 : ι →₀ ℕ) j)) =
        ∏ j, x j^Function.update (fun j => k j) i (k i-1) j := by
      rw [← hsub]
    simp_rw [hr]
    ring

#print axioms gaussianProductLaw_monomial_stein
#print axioms gaussianProductLaw_polynomial_stein

end GaussianTensorMoments
