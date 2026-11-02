import GaussianMultivariateStein
import Mathlib.Tactic

/-! The actual Gaussian Wick recurrence and its canonical recursive count,
obtained from polynomial Stein rather than assumed as an external Wick formula. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace GaussianTensorMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateProduct (l : List ι) : MvPolynomial ι ℝ :=
  (l.map MvPolynomial.X).prod

@[simp] theorem coordinateProduct_nil : coordinateProduct ([] : List ι) = 1 := rfl
@[simp] theorem coordinateProduct_cons (a : ι) (l : List ι) :
    coordinateProduct (a::l) = MvPolynomial.X a * coordinateProduct l := rfl

@[simp] theorem eval_coordinateProduct (l : List ι) (x : ι → ℝ) :
    MvPolynomial.eval x (coordinateProduct l) = (l.map x).prod := by
  induction l with
  | nil => simp [coordinateProduct]
  | cons a l ih => simp [coordinateProduct_cons, MvPolynomial.eval_mul, ih]

/-- Product differentiation picks exactly one endpoint at a time. -/
theorem pderiv_coordinateProduct (i : ι) (l : List ι) :
    MvPolynomial.pderiv i (coordinateProduct l) =
      ∑ j : Fin l.length, if i = l.get j then coordinateProduct (l.eraseIdx j) else 0 := by
  induction l with
  | nil => simp [MvPolynomial.pderiv_one]
  | cons a l ih =>
    rw [coordinateProduct_cons, Derivation.leibniz, ih]
    simp only [smul_eq_mul, List.length_cons, Fin.sum_univ_succ,
      List.get_cons_zero, List.get_cons_succ, Fin.val_zero, Fin.val_succ,
      List.eraseIdx_cons_zero, List.eraseIdx_cons_succ, coordinateProduct_cons]
    rw [Finset.mul_sum]
    have hsum : (∑ j : Fin l.length, MvPolynomial.X a *
        (if i=l.get j then coordinateProduct (l.eraseIdx j) else 0)) =
        ∑ j : Fin l.length, if i=l.get j then
          MvPolynomial.X a * coordinateProduct (l.eraseIdx j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp
    rw [hsum]
    by_cases ha : i=a
    · subst a
      simp [MvPolynomial.pderiv_X_self, add_comm]
    · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm ha)]
      simp [ha]

/-- Integrability of any ordered endpoint product. -/
theorem gaussianProductLaw_integrable_listProduct (l : List ι) :
    Integrable (fun x : ι → ℝ => (l.map x).prod) (gaussianProductLaw ι) := by
  simpa using gaussianProductLaw_integrable_polynomial (coordinateProduct l)

/-- Exact Gaussian integration-by-parts recurrence: the leading endpoint may
pair with any later endpoint of the same coordinate label. -/
theorem gaussianProductLaw_wick_recurrence (i : ι) (l : List ι) :
    (∫ x, ((i::l).map x).prod ∂gaussianProductLaw ι) =
      ∑ j : Fin l.length, if i=l.get j then
        (∫ x, ((l.eraseIdx j).map x).prod ∂gaussianProductLaw ι) else 0 := by
  have hs := gaussianProductLaw_polynomial_stein (coordinateProduct l) i
  simp only [eval_coordinateProduct, pderiv_coordinateProduct] at hs
  simp_rw [map_sum, apply_ite, map_zero, eval_coordinateProduct] at hs
  have hint (j : Fin l.length) : Integrable
      (fun x : ι → ℝ => if i=l.get j then ((l.eraseIdx j).map x).prod else 0)
      (gaussianProductLaw ι) := by
    split_ifs
    · exact gaussianProductLaw_integrable_listProduct _
    · exact integrable_zero _ _ _
  rw [integral_finset_sum _ (fun j _ => hint j)] at hs
  simp only [List.map_cons, List.prod_cons]
  rw [hs]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp

/-- Number of label-compatible canonical pairings, recursively pairing the
first endpoint with one later endpoint and deleting both. -/
def wickCount : List ι → ℕ
  | [] => 1
  | i::l => ∑ j : Fin l.length, if i=l.get j then wickCount (l.eraseIdx j) else 0
termination_by l => l.length
decreasing_by
  simp_wf
  exact (List.eraseIdx_sublist _ _).length_le

/-- Actual Gaussian endpoint moments equal the canonical pairing count. -/
theorem gaussianProductLaw_wickCount (l : List ι) :
    (∫ x, (l.map x).prod ∂gaussianProductLaw ι) = (wickCount l : ℝ) := by
  cases l with
  | nil => simp [wickCount]
  | cons i l =>
    rw [gaussianProductLaw_wick_recurrence, wickCount]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs
    · exact gaussianProductLaw_wickCount (l.eraseIdx j)
    · rfl
termination_by l.length
decreasing_by
  simp_wf
  exact (List.eraseIdx_sublist _ _).length_le

#print axioms gaussianProductLaw_wickCount
#print axioms gaussianProductLaw_wick_recurrence

end GaussianTensorMoments
