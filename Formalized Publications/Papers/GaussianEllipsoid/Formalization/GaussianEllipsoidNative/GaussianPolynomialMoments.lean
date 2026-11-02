import GaussianScalarTail
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-! Actual scalar standard-Gaussian polynomial moments, derived from its exact
MGF through differentiation. This is the probabilistic ingredient for Wick's rule. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

namespace GaussianTensorMoments

/-- Iterated Leibniz rule when one factor is the coordinate function. -/
theorem iteratedDeriv_coordinate_mul {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (n : ℕ) :
    iteratedDeriv (n+1) (fun x => x*f x) =
      fun x => x*iteratedDeriv (n+1) f x + (n+1:ℕ)*iteratedDeriv n f x := by
  have hd (k : ℕ) : Differentiable ℝ (iteratedDeriv k f) :=
    hf.differentiable_iteratedDeriv k (by simp)
  induction n with
  | zero =>
    funext x
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    have hh := ((hasDerivAt_id x).mul ((hd 0 x).hasDerivAt)).deriv
    simpa [iteratedDeriv_zero, iteratedDeriv_succ, Pi.mul_def, id_def, mul_comm, add_comm] using hh
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h₁ := (hasDerivAt_id x).mul ((hd (n+1) x).hasDerivAt)
    have h₂ := ((hd n x).hasDerivAt).const_mul ((n+1:ℕ):ℝ)
    simp only [Pi.mul_def, id_def] at h₁
    have hsum := (h₁.add h₂).deriv
    simp only [Pi.add_def] at hsum
    rw [hsum]
    simp only [one_mul, ← iteratedDeriv_succ]
    push_cast
    ring

/-- Exact full real MGF of the standard Gaussian. -/
theorem standardGaussian_mgf :
    mgf (id : ℝ → ℝ) (gaussianReal 0 1) = fun t => exp (t^2/2) := by
  funext t
  simpa using (mgf_gaussianReal (X := (id : ℝ → ℝ)) (p := gaussianReal 0 1)
    (μ := 0) (v := 1) (by simp) t)

/-- Its MGF is finite on all of R, so every differentiation below is justified. -/
theorem standardGaussian_integrableExpSet :
    integrableExpSet (id : ℝ → ℝ) (gaussianReal 0 1) = univ := by
  ext t
  simp only [mem_univ, iff_true, integrableExpSet, mem_setOf_eq]
  exact (hasSubgaussianMGF_of_centered_gaussian (X := (id : ℝ → ℝ))
    (μ := gaussianReal 0 1) (v := 1) (by simp)).integrable_exp_mul t

/-- All standard Gaussian polynomial moments are genuinely integrable. -/
theorem standardGaussian_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (gaussianReal 0 1) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := (id : ℝ → ℝ))
  simp [standardGaussian_integrableExpSet]

/-- Differential equation for the actual standard-Gaussian MGF. -/
theorem standardGaussian_mgf_deriv :
    deriv (mgf (id : ℝ → ℝ) (gaussianReal 0 1)) =
      fun t => t*mgf (id : ℝ → ℝ) (gaussianReal 0 1) t := by
  rw [standardGaussian_mgf]
  funext t
  have hh := (((hasDerivAt_id t).pow 2).div_const 2).exp
  convert hh.deriv using 1 <;> simp <;> ring

/-- Gaussian moments satisfy the exact integration-by-parts recurrence. -/
theorem standardGaussian_moment_succ_succ (n : ℕ) :
    (∫ x : ℝ, x^(n+2) ∂gaussianReal 0 1) =
      (n+1:ℕ)*(∫ x : ℝ, x^n ∂gaussianReal 0 1) := by
  have hi : (0:ℝ) ∈ interior (integrableExpSet (id : ℝ → ℝ) (gaussianReal 0 1)) := by
    simp [standardGaussian_integrableExpSet]
  have hm (k : ℕ) : iteratedDeriv k (mgf (id : ℝ → ℝ) (gaussianReal 0 1)) 0 =
      ∫ x : ℝ, x^k ∂gaussianReal 0 1 := by
    simpa using iteratedDeriv_mgf_zero hi k
  have hc : ContDiff ℝ ⊤ (mgf (id : ℝ → ℝ) (gaussianReal 0 1)) := by
    rw [standardGaussian_mgf]
    exact ((contDiff_id.pow 2).div_const (2:ℝ)).exp
  rw [← hm (n+2), ← hm n, show n+2=(n+1)+1 by omega, iteratedDeriv_succ',
    standardGaussian_mgf_deriv, iteratedDeriv_coordinate_mul hc n]
  simp

/-- The first standard Gaussian moment vanishes. -/
theorem standardGaussian_moment_one :
    (∫ x : ℝ, x ∂gaussianReal 0 1) = 0 := by
  have hi : (0:ℝ) ∈ interior (integrableExpSet (id : ℝ → ℝ) (gaussianReal 0 1)) := by
    simp [standardGaussian_integrableExpSet]
  have hh := deriv_mgf_zero hi
  rw [standardGaussian_mgf_deriv] at hh
  simpa using hh.symm

/-- Every odd Gaussian moment vanishes. -/
theorem standardGaussian_moment_odd (k : ℕ) :
    (∫ x : ℝ, x^(2*k+1) ∂gaussianReal 0 1) = 0 := by
  induction k with
  | zero => simpa using standardGaussian_moment_one
  | succ k ih =>
    rw [show 2*(k+1)+1=(2*k+1)+2 by omega, standardGaussian_moment_succ_succ, ih, mul_zero]

/-- Every even Gaussian moment is the number of pair partitions of its endpoints. -/
theorem standardGaussian_moment_even (k : ℕ) :
    (∫ x : ℝ, x^(2*k) ∂gaussianReal 0 1) = ((2*k-1)‼ : ℝ) := by
  induction k with
  | zero => simp [Nat.doubleFactorial]
  | succ k ih =>
    rw [show 2*(k+1)=2*k+2 by ring, standardGaussian_moment_succ_succ, ih]
    rw [show 2*k+2-1=2*k+1 by omega, Nat.doubleFactorial_add_one]
    push_cast
    ring

/-- Integrability of every polynomial against the standard Gaussian. -/
theorem standardGaussian_integrable_polynomial (P : Polynomial ℝ) :
    Integrable (fun x : ℝ => P.eval x) (gaussianReal 0 1) := by
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply integrable_finset_sum
  intro n hn
  exact (standardGaussian_integrable_pow n).const_mul _

/-- Scalar polynomial Stein identity, with the actual Gaussian measure. -/
theorem standardGaussian_polynomial_stein (P : Polynomial ℝ) :
    (∫ x : ℝ, x*P.eval x ∂gaussianReal 0 1) =
      ∫ x : ℝ, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hxp (P : Polynomial ℝ) :
      Integrable (fun x : ℝ => x*P.eval x) (gaussianReal 0 1) := by
    have h := standardGaussian_integrable_polynomial (Polynomial.X*P)
    convert h using 1
    funext x
    rw [Polynomial.eval_mul, Polynomial.eval_X]
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp_rw [Polynomial.eval_add, mul_add, Polynomial.derivative_add, Polynomial.eval_add]
    rw [integral_add (hxp P) (hxp Q),
      integral_add (standardGaussian_integrable_polynomial P.derivative)
        (standardGaussian_integrable_polynomial Q.derivative), hP, hQ]
  | monomial n a =>
    cases n with
    | zero =>
      simp [Polynomial.eval_monomial, Polynomial.derivative_monomial,
        integral_mul_const, standardGaussian_moment_one]
    | succ n =>
      have hfun (x : ℝ) : x*(Polynomial.monomial (n+1) a).eval x = a*x^(n+2) := by
        simp only [Polynomial.eval_monomial]
        ring
      simp_rw [hfun, Polynomial.derivative_monomial_succ, Polynomial.eval_monomial]
      rw [integral_const_mul, integral_const_mul, standardGaussian_moment_succ_succ]
      push_cast
      ring

#print axioms standardGaussian_moment_even
#print axioms standardGaussian_polynomial_stein
#print axioms standardGaussian_integrable_pow
#print axioms standardGaussian_moment_succ_succ

end GaussianTensorMoments
