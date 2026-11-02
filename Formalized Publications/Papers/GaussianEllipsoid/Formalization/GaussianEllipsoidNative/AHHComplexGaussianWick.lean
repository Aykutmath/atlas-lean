import GaussianWickRecurrence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Exact complex Gaussian polynomial integration

All integrals in this file use the concrete finite product of real N(0,1)
measures already constructed in `GaussianTensorMoments`.  In particular no
moment identity or abstract Gaussian integration oracle is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace AHH
open GaussianTensorMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluate a complex polynomial on actual real Gaussian coordinates. -/
abbrev complexEval (P : MvPolynomial ι ℂ) (x : ι → ℝ) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) P

@[simp] theorem complexEval_add (P Q : MvPolynomial ι ℂ) (x : ι → ℝ) :
    complexEval (P + Q) x = complexEval P x + complexEval Q x := by
  simp [complexEval]

@[simp] theorem complexEval_mul (P Q : MvPolynomial ι ℂ) (x : ι → ℝ) :
    complexEval (P * Q) x = complexEval P x * complexEval Q x := by
  simp [complexEval]

theorem complexEval_monomial (k : ι →₀ ℕ) (a : ℂ) (x : ι → ℝ) :
    complexEval (MvPolynomial.monomial k a) x =
      a * ((∏ i, x i ^ k i : ℝ) : ℂ) := by
  simp only [complexEval, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Complex.ofReal_prod, Complex.ofReal_pow]

/-- All complex coefficient polynomials are genuinely Bochner integrable. -/
theorem gaussian_integrable_complex_polynomial (P : MvPolynomial ι ℂ) :
    Integrable (complexEval P) (gaussianProductLaw ι) := by
  induction P using MvPolynomial.induction_on' with
  | monomial k a =>
    change Integrable (fun x => complexEval (MvPolynomial.monomial k a) x) _
    simp_rw [complexEval_monomial]
    exact (gaussianProductLaw_integrable_monomial k).ofReal.const_mul a
  | add P Q hP hQ =>
    apply (hP.add hQ).congr
    filter_upwards with x
    simp [complexEval]

theorem gaussian_complex_monomial_stein (k : ι → ℕ) (i : ι) :
    (∫ x, (x i : ℂ) * ((∏ j, x j ^ k j : ℝ) : ℂ) ∂gaussianProductLaw ι) =
      (k i : ℂ) *
        ∫ x, ((∏ j, x j ^ Function.update k i (k i - 1) j : ℝ) : ℂ)
          ∂gaussianProductLaw ι := by
  simp_rw [← Complex.ofReal_mul, integral_complex_ofReal,
    gaussianProductLaw_monomial_stein, Complex.ofReal_mul, Complex.ofReal_natCast]

/-- Integration by parts for complex polynomials, with no hypothesis on their
moments: polynomial integrability is discharged above. -/
theorem gaussian_complex_polynomial_stein (P : MvPolynomial ι ℂ) (i : ι) :
    (∫ x, (x i : ℂ) * complexEval P x ∂gaussianProductLaw ι) =
      ∫ x, complexEval (MvPolynomial.pderiv i P) x ∂gaussianProductLaw ι := by
  have hxp (Q : MvPolynomial ι ℂ) :
      Integrable (fun x => (x i : ℂ) * complexEval Q x) (gaussianProductLaw ι) := by
    convert gaussian_integrable_complex_polynomial (MvPolynomial.X i * Q) using 1
    funext x
    simp [complexEval]
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, complexEval, MvPolynomial.eval_add, mul_add] at *
    rw [integral_add (hxp P) (hxp Q), integral_add
      (gaussian_integrable_complex_polynomial _)
      (gaussian_integrable_complex_polynomial _), hP, hQ]
  | monomial k a =>
    simp only [MvPolynomial.pderiv_monomial, complexEval_monomial]
    have hl (x : ι → ℝ) :
        (x i : ℂ) * (a * ((∏ j, x j ^ k j : ℝ) : ℂ)) =
          a * ((x i : ℂ) * ((∏ j, x j ^ k j : ℝ) : ℂ)) := by ring
    simp_rw [hl]
    rw [integral_const_mul, integral_const_mul, gaussian_complex_monomial_stein]
    have hsub := finsupp_sub_single_coe k i
    have hr (x : ι → ℝ) :
        (∏ j, x j ^ ((k - Finsupp.single i 1 : ι →₀ ℕ) j)) =
          ∏ j, x j ^ Function.update (fun j => k j) i (k i - 1) j := by
      rw [← hsub]
    simp_rw [hr]
    ring

/-- The imaginary coefficient for a complex coordinate or its conjugate.
`false` is z; `true` is conjugate z. -/
def imaginaryCoefficient (b : Bool) : ℂ := if b then -Complex.I else Complex.I

/-- An unnormalized complex Gaussian endpoint, represented as a polynomial
in the independent real and imaginary coordinates. -/
def endpointPolynomial (a : ι × Bool) : MvPolynomial (ι × Bool) ℂ :=
  MvPolynomial.X (a.1, false) +
    MvPolynomial.C (imaginaryCoefficient a.2) * MvPolynomial.X (a.1, true)

/-- The matching complex integration-by-parts derivative. -/
def endpointDerivative (a : ι × Bool) :
    Derivation ℂ (MvPolynomial (ι × Bool) ℂ) (MvPolynomial (ι × Bool) ℂ) :=
  MvPolynomial.pderiv (a.1, false) +
    (MvPolynomial.C (imaginaryCoefficient a.2) : MvPolynomial (ι × Bool) ℂ) •
      (MvPolynomial.pderiv (a.1, true) :
        Derivation ℂ (MvPolynomial (ι × Bool) ℂ) (MvPolynomial (ι × Bool) ℂ))

def endpointValue (a : ι × Bool) (x : (ι × Bool) → ℝ) : ℂ :=
  (x (a.1, false) : ℂ) + imaginaryCoefficient a.2 * (x (a.1, true) : ℂ)

@[simp] theorem complexEval_endpointPolynomial (a : ι × Bool) (x : (ι × Bool) → ℝ) :
    complexEval (endpointPolynomial a) x = endpointValue a x := by
  simp [complexEval, endpointPolynomial, endpointValue]

/-- Only a coordinate and its conjugate have nonzero contraction. -/
def endpointsMatch (a b : ι × Bool) : Prop := a.1 = b.1 ∧ a.2 ≠ b.2

instance (a b : ι × Bool) : Decidable (endpointsMatch a b) := inferInstanceAs
  (Decidable (a.1 = b.1 ∧ a.2 ≠ b.2))

theorem endpointDerivative_endpointPolynomial (a b : ι × Bool) :
    endpointDerivative a (endpointPolynomial b) =
      if endpointsMatch a b then 2 else 0 := by
  obtain ⟨i, s⟩ := a
  obtain ⟨j, t⟩ := b
  by_cases hij : i = j
  · subst j
    cases s <;> cases t <;>
      simp [endpointDerivative, endpointPolynomial, imaginaryCoefficient, endpointsMatch,
        Derivation.add_apply, Derivation.smul_apply, Derivation.leibniz, smul_eq_mul,
        ← MvPolynomial.C_mul] <;> norm_num
  · cases s <;> cases t <;>
      simp [endpointDerivative, endpointPolynomial, imaginaryCoefficient, endpointsMatch,
        Derivation.add_apply, Derivation.smul_apply, Derivation.leibniz, smul_eq_mul,
        hij, Ne.symm hij, MvPolynomial.pderiv_X_of_ne]

/-- Complex Stein identity for z and conjugate z. -/
theorem gaussian_endpoint_stein (a : ι × Bool) (P : MvPolynomial (ι × Bool) ℂ) :
    (∫ x, endpointValue a x * complexEval P x ∂gaussianProductLaw (ι × Bool)) =
      ∫ x, complexEval (endpointDerivative a P) x ∂gaussianProductLaw (ι × Bool) := by
  have hi (i : ι × Bool) : Integrable
      (fun x => (x i : ℂ) * complexEval P x) (gaussianProductLaw (ι × Bool)) := by
    convert gaussian_integrable_complex_polynomial (MvPolynomial.X i * P) using 1
    funext x
    simp [complexEval]
  simp only [endpointValue, add_mul, mul_assoc, endpointDerivative,
    Derivation.add_apply, Derivation.smul_apply, smul_eq_mul,
    complexEval, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [integral_add (hi _) ((hi _).const_mul _), integral_add
    (gaussian_integrable_complex_polynomial _)
    ((gaussian_integrable_complex_polynomial _).const_mul _),
    integral_const_mul, integral_const_mul]
  rw [gaussian_complex_polynomial_stein, gaussian_complex_polynomial_stein]

def endpointProduct (l : List (ι × Bool)) : MvPolynomial (ι × Bool) ℂ :=
  (l.map endpointPolynomial).prod

@[simp] theorem endpointProduct_nil : endpointProduct ([] : List (ι × Bool)) = 1 := rfl

@[simp] theorem endpointProduct_cons (a : ι × Bool) (l : List (ι × Bool)) :
    endpointProduct (a :: l) = endpointPolynomial a * endpointProduct l := rfl

@[simp] theorem complexEval_endpointProduct (l : List (ι × Bool)) (x : (ι × Bool) → ℝ) :
    complexEval (endpointProduct l) x = (l.map (fun a => endpointValue a x)).prod := by
  induction l with
  | nil => simp [endpointProduct, complexEval]
  | cons a l ih =>
    change complexEval (endpointPolynomial a * endpointProduct l) x = _
    rw [complexEval, MvPolynomial.eval_mul]
    change complexEval (endpointPolynomial a) x * complexEval (endpointProduct l) x = _
    simp only [complexEval_endpointPolynomial, ih, List.map_cons, List.prod_cons]

theorem endpointDerivative_endpointProduct (a : ι × Bool) (l : List (ι × Bool)) :
    endpointDerivative a (endpointProduct l) =
      ∑ j : Fin l.length, if endpointsMatch a (l.get j) then
        2 * endpointProduct (l.eraseIdx j) else 0 := by
  induction l with
  | nil => simp [Derivation.map_one_eq_zero]
  | cons b l ih =>
    rw [endpointProduct_cons, Derivation.leibniz, ih,
      endpointDerivative_endpointPolynomial]
    simp only [smul_eq_mul, List.length_cons, Fin.sum_univ_succ,
      List.get_cons_zero, List.get_cons_succ, Fin.val_zero, Fin.val_succ,
      List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, endpointProduct_cons]
    rw [Finset.mul_sum]
    have hsum : (∑ j : Fin l.length, endpointPolynomial b *
        (if endpointsMatch a (l.get j) then 2 * endpointProduct (l.eraseIdx j) else 0)) =
        ∑ j : Fin l.length, if endpointsMatch a (l.get j) then
          2 * (endpointPolynomial b * endpointProduct (l.eraseIdx j)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [hsum]
    by_cases h : endpointsMatch a b <;>
      simp [h, List.get_eq_getElem, add_comm, mul_comm]

/-- Absolute integrability is established before using any endpoint moment. -/
theorem gaussian_integrable_endpointProduct (l : List (ι × Bool)) :
    Integrable (fun x => (l.map (fun a => endpointValue a x)).prod)
      (gaussianProductLaw (ι × Bool)) := by
  convert gaussian_integrable_complex_polynomial (endpointProduct l) using 1
  funext x
  exact (complexEval_endpointProduct l x).symm

/-- Exact complex Wick recurrence under the actual independent real-coordinate
Gaussian law. Unnormalized z=x+iy has contraction 2. -/
theorem gaussian_complex_wick_recurrence (a : ι × Bool) (l : List (ι × Bool)) :
    (∫ x, ((a :: l).map (fun b => endpointValue b x)).prod
      ∂gaussianProductLaw (ι × Bool)) =
      ∑ j : Fin l.length, if endpointsMatch a (l.get j) then
        2 * (∫ x, ((l.eraseIdx j).map (fun b => endpointValue b x)).prod
          ∂gaussianProductLaw (ι × Bool)) else 0 := by
  have hs := gaussian_endpoint_stein a (endpointProduct l)
  simp only [complexEval_endpointProduct, endpointDerivative_endpointProduct] at hs
  simp_rw [complexEval, map_sum, apply_ite, map_zero, MvPolynomial.eval_mul,
    map_ofNat] at hs
  change (∫ x, endpointValue a x * (l.map (fun b => endpointValue b x)).prod
    ∂gaussianProductLaw (ι × Bool)) =
      ∫ x, ∑ j : Fin l.length, if endpointsMatch a (l.get j) then
        2 * complexEval (endpointProduct (l.eraseIdx j)) x else 0
        ∂gaussianProductLaw (ι × Bool) at hs
  simp_rw [complexEval_endpointProduct] at hs
  have hi (j : Fin l.length) : Integrable
      (fun x => if endpointsMatch a (l.get j) then
        (2 : ℂ) * ((l.eraseIdx j).map (fun b => endpointValue b x)).prod else 0)
        (gaussianProductLaw (ι × Bool)) := by
    split_ifs
    · exact (gaussian_integrable_endpointProduct _).const_mul _
    · exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun j _ => hi j)] at hs
  simp only [List.map_cons, List.prod_cons]
  rw [hs]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp [integral_const_mul]

/-- Integer-valued contraction count, including each real/imaginary factor 2. -/
def complexWickCount : List (ι × Bool) → ℕ
  | [] => 1
  | a :: l => ∑ j : Fin l.length,
      if endpointsMatch a (l.get j) then 2 * complexWickCount (l.eraseIdx j) else 0
termination_by l => l.length
decreasing_by
  simp_wf
  exact (List.eraseIdx_sublist _ _).length_le

/-- Every mixed complex Gaussian coordinate moment is a nonnegative integer.
This includes arbitrary repeated coordinate labels and unbalanced words. -/
theorem gaussian_complex_wickCount (l : List (ι × Bool)) :
    (∫ x, (l.map (fun a => endpointValue a x)).prod
      ∂gaussianProductLaw (ι × Bool)) = (complexWickCount l : ℂ) := by
  cases l with
  | nil => simp [complexWickCount]
  | cons a l =>
    rw [gaussian_complex_wick_recurrence, complexWickCount]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [gaussian_complex_wickCount]
    · rfl
termination_by l.length
decreasing_by
  simp_wf
  exact (List.eraseIdx_sublist _ _).length_le

theorem gaussian_complex_endpoint_moment_im_zero (l : List (ι × Bool)) :
    (∫ x, (l.map (fun a => endpointValue a x)).prod
      ∂gaussianProductLaw (ι × Bool)).im = 0 := by
  rw [gaussian_complex_wickCount]
  simp

theorem gaussian_complex_endpoint_moment_re_nonneg (l : List (ι × Bool)) :
    0 ≤ (∫ x, (l.map (fun a => endpointValue a x)).prod
      ∂gaussianProductLaw (ι × Bool)).re := by
  rw [gaussian_complex_wickCount]
  simp

end AHH
