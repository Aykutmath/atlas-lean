import AHHGaussianWordPositivity

/-! Polynomial matrix differentiation for the actual complex Gaussian
rank-one word integration-by-parts equation. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
set_option maxHeartbeats 200000

namespace AHH
open GaussianTensorMoments

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

abbrev WordPolynomial (ι n : Type*) := MvPolynomial ((ι × n) × Bool) ℂ

def matrixDerivative (D : Derivation ℂ (WordPolynomial ι n) (WordPolynomial ι n))
    (A : Matrix n n (WordPolynomial ι n)) : Matrix n n (WordPolynomial ι n) :=
  fun i j => D (A i j)

theorem matrixDerivative_mul (D : Derivation ℂ (WordPolynomial ι n) (WordPolynomial ι n))
    (A B : Matrix n n (WordPolynomial ι n)) :
    matrixDerivative D (A * B) = matrixDerivative D A * B + A * matrixDerivative D B := by
  apply Matrix.ext
  intro i j
  simp only [matrixDerivative, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem matrixDerivative_one (D : Derivation ℂ (WordPolynomial ι n) (WordPolynomial ι n)) :
    matrixDerivative D (1 : Matrix n n (WordPolynomial ι n)) = 0 := by
  apply Matrix.ext
  intro i j
  simp [matrixDerivative, Matrix.one_apply, apply_ite, Derivation.map_one_eq_zero]

theorem gaussianWordPolynomial_nil :
    gaussianWordPolynomial ([] : List ι) = (1 : Matrix n n (WordPolynomial ι n)) := rfl

theorem gaussianWordPolynomial_cons (s : ι) (w : List ι) :
    gaussianWordPolynomial (s :: w) =
      (gaussianProjectorPolynomial s * gaussianWordPolynomial w : Matrix n n (WordPolynomial ι n)) := rfl

theorem gaussianWordPolynomial_append (v w : List ι) :
    gaussianWordPolynomial (v ++ w) =
      (gaussianWordPolynomial v * gaussianWordPolynomial w : Matrix n n (WordPolynomial ι n)) := by
  simp [gaussianWordPolynomial]

theorem matrixDerivative_gaussianWordPolynomial
    (D : Derivation ℂ (WordPolynomial ι n) (WordPolynomial ι n)) (w : List ι) :
    matrixDerivative D (gaussianWordPolynomial w) =
      ∑ k : Fin w.length,
        gaussianWordPolynomial (w.take k) *
          matrixDerivative D (gaussianProjectorPolynomial (w.get k)) *
            gaussianWordPolynomial (w.drop (k + 1)) := by
  induction w with
  | nil => simp [gaussianWordPolynomial_nil, matrixDerivative_one]
  | cons s w ih =>
    rw [gaussianWordPolynomial_cons, matrixDerivative_mul, ih]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      List.take_zero, List.get_cons_zero, zero_add, List.drop_succ_cons,
      gaussianWordPolynomial_nil, Matrix.one_mul, List.take_succ_cons,
      gaussianWordPolynomial_cons]
    rw [Finset.mul_sum]
    simp only [List.drop_zero, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ,
      Matrix.mul_assoc]

theorem endpointDerivative_gaussianProjectorPolynomial (s t : ι) (i j k : n) :
    endpointDerivative ((s, i), false) (gaussianProjectorPolynomial t j k) =
      if s = t ∧ i = k then 2 * endpointPolynomial ((t, j), false) else 0 := by
  simp only [gaussianProjectorPolynomial, Derivation.leibniz, smul_eq_mul,
    endpointDerivative_endpointPolynomial, endpointsMatch, Bool.false_eq_true,
    not_false_eq_true, and_true, Prod.mk.injEq, ne_eq, not_true_eq_false,
    and_false, if_false, mul_zero, add_zero]
  split_ifs <;> ring

def wordContraction (s : ι) (A : n → Matrix n n (WordPolynomial ι n)) :
    WordPolynomial ι n :=
  ∑ i, ∑ j, endpointPolynomial ((s, j), true) * A i j i

theorem wordContraction_add (s : ι) (A B : n → Matrix n n (WordPolynomial ι n)) :
    wordContraction s (fun i => A i + B i) = wordContraction s A + wordContraction s B := by
  simp [wordContraction, mul_add, Finset.sum_add_distrib]

theorem wordContraction_finsetSum {κ : Type*} (s : ι) (K : Finset κ)
    (A : κ → n → Matrix n n (WordPolynomial ι n)) :
    wordContraction s (fun i => ∑ k ∈ K, A k i) = ∑ k ∈ K, wordContraction s (A k) := by
  simp only [wordContraction, Matrix.sum_apply, Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k ∈ K, endpointPolynomial ((s, j), true) * A k i j i) =
        ∑ i, ∑ k ∈ K, ∑ j, endpointPolynomial ((s, j), true) * A k i j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem wordContraction_projectorDerivative (s t : ι)
    (A B : Matrix n n (WordPolynomial ι n)) :
    wordContraction s (fun i =>
      A * matrixDerivative (endpointDerivative ((s, i), false))
        (gaussianProjectorPolynomial t) * B) =
      if s = t then
        2 * Matrix.trace (gaussianProjectorPolynomial s * A) * Matrix.trace B else 0 := by
  by_cases hst : s = t
  · subst t
    simp only [Matrix.mul_assoc]
    simp only [wordContraction, Matrix.mul_apply, matrixDerivative,
      endpointDerivative_gaussianProjectorPolynomial, true_and,
      Finset.sum_mul, Finset.mul_sum, ite_true]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      gaussianProjectorPolynomial, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · simp [wordContraction, Matrix.mul_apply, matrixDerivative,
      endpointDerivative_gaussianProjectorPolynomial, hst]


/-- Expectation is a complex-linear functional on the polynomial algebra.
Every polynomial here is integrable by the previously proved Gaussian theorem. -/
def gaussianPolynomialExpectation : WordPolynomial ι n →ₗ[ℂ] ℂ where
  toFun P := ∫ x, complexEval P x ∂gaussianProductLaw ((ι × n) × Bool)
  map_add' P Q := by
    simp_rw [complexEval_add]
    exact integral_add (gaussian_integrable_complex_polynomial P)
      (gaussian_integrable_complex_polynomial Q)
  map_smul' c P := by
    simp only [complexEval, MvPolynomial.smul_eq_C_mul, MvPolynomial.eval_mul,
      MvPolynomial.eval_C, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul c _

theorem gaussianPolynomialExpectation_endpoint (a : (ι × n) × Bool)
    (P : WordPolynomial ι n) :
    gaussianPolynomialExpectation (endpointPolynomial a * P) =
      gaussianPolynomialExpectation (endpointDerivative a P) := by
  change (∫ x, complexEval (endpointPolynomial a * P) x
    ∂gaussianProductLaw ((ι × n) × Bool)) = _
  simp_rw [complexEval_mul, complexEval_endpointPolynomial]
  exact gaussian_endpoint_stein a P

theorem gaussianPolynomialExpectation_projector_mul (s : ι)
    (A : Matrix n n (WordPolynomial ι n)) :
    gaussianPolynomialExpectation (Matrix.trace (gaussianProjectorPolynomial s * A)) =
      gaussianPolynomialExpectation (2 * Matrix.trace A +
        wordContraction s (fun i => matrixDerivative (endpointDerivative ((s, i), false)) A)) := by
  have htrace : Matrix.trace (gaussianProjectorPolynomial s * A) =
      ∑ i, ∑ j, endpointPolynomial ((s, i), false) *
        (endpointPolynomial ((s, j), true) * A j i) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, gaussianProjectorPolynomial]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hpoly : (∑ i, ∑ j, endpointDerivative ((s, i), false)
      (endpointPolynomial ((s, j), true) * A j i)) =
      2 * Matrix.trace A + wordContraction s
        (fun i => matrixDerivative (endpointDerivative ((s, i), false)) A) := by
    simp only [Derivation.leibniz, smul_eq_mul, endpointDerivative_endpointPolynomial,
      endpointsMatch, Prod.mk.injEq, true_and, Bool.false_eq_true, not_false_eq_true,
      and_true, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      wordContraction, matrixDerivative]
    simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    rw [add_comm]
    apply congrArg (fun P : WordPolynomial ι n => P +
      (∑ i, ∑ j, endpointPolynomial ((s, j), true) *
        endpointDerivative ((s, i), false) (A j i)))
    apply Finset.sum_congr rfl
    intro i _
    simp [mul_comm]
  rw [htrace, ← hpoly]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact gaussianPolynomialExpectation_endpoint ((s, i), false) _

/-- Exact finite word loop equation, including repeated letters. The raw
complex coordinate z=x+iy has covariance two; normalization later divides by
2h and changes this prefactor to 1/h. -/
theorem gaussian_word_loop_equation (s : ι) (w : List ι) :
    gaussianPolynomialExpectation (Matrix.trace (gaussianWordPolynomial (s :: w) :
      Matrix n n (WordPolynomial ι n))) =
      gaussianPolynomialExpectation (ι := ι) (n := n)
        (2 * Matrix.trace (gaussianWordPolynomial w) +
          ∑ k : Fin w.length, if s = w.get k then
            2 * Matrix.trace (gaussianWordPolynomial (s :: w.take k)) *
              Matrix.trace (gaussianWordPolynomial (w.drop (k + 1))) else 0) := by
  rw [gaussianWordPolynomial_cons, gaussianPolynomialExpectation_projector_mul]
  apply congrArg gaussianPolynomialExpectation
  apply congrArg (fun P : WordPolynomial ι n =>
    2 * Matrix.trace (gaussianWordPolynomial w) + P)
  simp_rw [matrixDerivative_gaussianWordPolynomial]
  rw [wordContraction_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [wordContraction_projectorDerivative]
  simp only [gaussianWordPolynomial_cons]

theorem gaussianPolynomialExpectation_two_mul (P : WordPolynomial ι n) :
    gaussianPolynomialExpectation (2 * P) = 2 * gaussianPolynomialExpectation P := by
  simp only [two_mul, map_add]

theorem gaussianPolynomialExpectation_wordTrace (w : List ι) :
    gaussianPolynomialExpectation (Matrix.trace (gaussianWordPolynomial w :
      Matrix n n (WordPolynomial ι n))) =
      ∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x w)
        ∂gaussianProductLaw ((ι × n) × Bool) := by
  change (∫ x, complexEval _ x ∂_) = _
  apply integral_congr_ae
  filter_upwards with x
  exact complexEval_gaussianWordTracePolynomial x w

theorem gaussianPolynomialExpectation_wordTrace_mul (v w : List ι) :
    gaussianPolynomialExpectation (Matrix.trace (gaussianWordPolynomial v :
      Matrix n n (WordPolynomial ι n)) * Matrix.trace (gaussianWordPolynomial w)) =
      ∫ x : ((ι × n) × Bool) → ℝ,
        Matrix.trace (gaussianWordMatrix x v) * Matrix.trace (gaussianWordMatrix x w)
        ∂gaussianProductLaw ((ι × n) × Bool) := by
  change (∫ x, complexEval _ x ∂_) = _
  apply integral_congr_ae
  filter_upwards with x
  rw [complexEval_mul, complexEval_gaussianWordTracePolynomial,
    complexEval_gaussianWordTracePolynomial]

/-- The loop equation for literal traces and the actual product Gaussian
measure; every integrability obligation was discharged in the construction. -/
theorem gaussian_wordTrace_integral_loop (s : ι) (w : List ι) :
    (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x (s :: w))
      ∂gaussianProductLaw ((ι × n) × Bool)) =
      2 * (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x w)
        ∂gaussianProductLaw ((ι × n) × Bool)) +
      ∑ k : Fin w.length, if s = w.get k then
        2 * (∫ x : ((ι × n) × Bool) → ℝ,
          Matrix.trace (gaussianWordMatrix x (s :: w.take k)) *
            Matrix.trace (gaussianWordMatrix x (w.drop (k + 1)))
          ∂gaussianProductLaw ((ι × n) × Bool)) else 0 := by
  have h := gaussian_word_loop_equation (n := n) s w
  simp only [map_add, map_sum] at h
  simp_rw [apply_ite, map_zero, mul_assoc, gaussianPolynomialExpectation_two_mul,
    gaussianPolynomialExpectation_wordTrace, gaussianPolynomialExpectation_wordTrace_mul] at h
  exact h

theorem gaussian_wordTrace_integral_loop_re (s : ι) (w : List ι) :
    (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x (s :: w))
      ∂gaussianProductLaw ((ι × n) × Bool)).re =
      2 * (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x w)
        ∂gaussianProductLaw ((ι × n) × Bool)).re +
      ∑ k : Fin w.length, if s = w.get k then
        2 * (∫ x : ((ι × n) × Bool) → ℝ,
          Matrix.trace (gaussianWordMatrix x (s :: w.take k)) *
            Matrix.trace (gaussianWordMatrix x (w.drop (k + 1)))
          ∂gaussianProductLaw ((ι × n) × Bool)).re else 0 := by
  rw [gaussian_wordTrace_integral_loop]
  simp [apply_ite]

end AHH
