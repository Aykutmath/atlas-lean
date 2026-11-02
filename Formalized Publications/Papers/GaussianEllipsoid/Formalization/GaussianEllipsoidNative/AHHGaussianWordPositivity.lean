import AHHComplexGaussianWick
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.MeasureTheory.Integral.Prod

/-! Exact positivity and tensor factorization of actual complex Gaussian
projector-word expectations. The Gaussian measure is explicit throughout. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace AHH
open GaussianTensorMoments

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite sum of mixed coordinate monomials with nonnegative integer
coefficients. The witness is algebraic; it is not a moment assumption. -/
def IsEndpointSum (P : MvPolynomial (ι × Bool) ℂ) : Prop :=
  ∃ L : List (List (ι × Bool)), P = (L.map endpointProduct).sum

theorem isEndpointSum_zero : IsEndpointSum (0 : MvPolynomial (ι × Bool) ℂ) :=
  ⟨[], by simp⟩

theorem isEndpointSum_one : IsEndpointSum (1 : MvPolynomial (ι × Bool) ℂ) :=
  ⟨[[]], by simp⟩

theorem isEndpointSum_endpointProduct (l : List (ι × Bool)) :
    IsEndpointSum (endpointProduct l) := ⟨[l], by simp⟩

theorem IsEndpointSum.add {P Q : MvPolynomial (ι × Bool) ℂ}
    (hP : IsEndpointSum P) (hQ : IsEndpointSum Q) : IsEndpointSum (P + Q) := by
  obtain ⟨L, rfl⟩ := hP
  obtain ⟨K, rfl⟩ := hQ
  exact ⟨L ++ K, by simp⟩

@[simp] theorem endpointProduct_append (l k : List (ι × Bool)) :
    endpointProduct (l ++ k) = endpointProduct l * endpointProduct k := by
  simp [endpointProduct]

theorem IsEndpointSum.endpoint_mul {P : MvPolynomial (ι × Bool) ℂ}
    (l : List (ι × Bool)) (hP : IsEndpointSum P) :
    IsEndpointSum (endpointProduct l * P) := by
  obtain ⟨K, rfl⟩ := hP
  induction K with
  | nil => simpa using (isEndpointSum_zero (ι := ι))
  | cons k K ih =>
    simpa [mul_add, ← endpointProduct_append] using
      (isEndpointSum_endpointProduct (l ++ k)).add ih

theorem IsEndpointSum.mul {P Q : MvPolynomial (ι × Bool) ℂ}
    (hP : IsEndpointSum P) (hQ : IsEndpointSum Q) : IsEndpointSum (P * Q) := by
  obtain ⟨L, rfl⟩ := hP
  induction L with
  | nil => simpa using (isEndpointSum_zero (ι := ι))
  | cons l L ih =>
    simpa [add_mul] using (hQ.endpoint_mul l).add ih

theorem isEndpointSum_finsetSum {κ : Type*} (S : Finset κ)
    (P : κ → MvPolynomial (ι × Bool) ℂ) (hP : ∀ k ∈ S, IsEndpointSum (P k)) :
    IsEndpointSum (∑ k ∈ S, P k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (isEndpointSum_zero (ι := ι))
  | @insert k S hk ih =>
    rw [Finset.sum_insert hk]
    exact (hP k (by simp)).add (ih (fun j hj => hP j (by simp [hj])))

/-- A closed formula for the expectation of each finite endpoint sum. -/
theorem integral_endpointSum (L : List (List (ι × Bool))) :
    (∫ x, complexEval ((L.map endpointProduct).sum) x
      ∂gaussianProductLaw (ι × Bool)) =
        ((L.map complexWickCount).sum : ℂ) := by
  induction L with
  | nil => simp [complexEval]
  | cons l L ih =>
    simp only [List.map_cons, List.sum_cons]
    simp_rw [complexEval_add]
    change (∫ x, complexEval (endpointProduct l) x +
      complexEval ((L.map endpointProduct).sum) x ∂gaussianProductLaw (ι × Bool)) = _
    rw [integral_add (gaussian_integrable_complex_polynomial _)
      (gaussian_integrable_complex_polynomial _), ih]
    simp only [complexEval_endpointProduct, gaussian_complex_wickCount, Nat.cast_add]

theorem IsEndpointSum.integral_im_zero {P : MvPolynomial (ι × Bool) ℂ}
    (hP : IsEndpointSum P) :
    (∫ x, complexEval P x ∂gaussianProductLaw (ι × Bool)).im = 0 := by
  obtain ⟨L, rfl⟩ := hP
  rw [integral_endpointSum]
  exact Complex.natCast_im _

theorem IsEndpointSum.integral_re_nonneg {P : MvPolynomial (ι × Bool) ℂ}
    (hP : IsEndpointSum P) :
    0 ≤ (∫ x, complexEval P x ∂gaussianProductLaw (ι × Bool)).re := by
  obtain ⟨L, rfl⟩ := hP
  rw [integral_endpointSum, Complex.natCast_re]
  exact Nat.cast_nonneg _

theorem endpointValue_true_eq_conj (i : ι) (x : (ι × Bool) → ℝ) :
    endpointValue (i, true) x = star (endpointValue (i, false) x) := by
  simp [endpointValue, imaginaryCoefficient, map_add, map_mul]

variable {n : Type*} [Fintype n] [DecidableEq n]

def gaussianProjectorPolynomial (s : ι) :
    Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ) :=
  fun i j => endpointPolynomial ((s, i), false) * endpointPolynomial ((s, j), true)

def gaussianWordPolynomial (w : List ι) :
    Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ) :=
  (w.map gaussianProjectorPolynomial).prod

theorem gaussianProjectorPolynomial_isEndpointSum (s : ι) (i j : n) :
    IsEndpointSum (gaussianProjectorPolynomial s i j) := by
  convert isEndpointSum_endpointProduct [((s, i), false), ((s, j), true)] using 1 <;>
    simp [gaussianProjectorPolynomial, endpointProduct]

theorem matrix_mul_isEndpointSum
    {P Q : Matrix n n (MvPolynomial (ι × Bool) ℂ)}
    (hP : ∀ i j, IsEndpointSum (P i j))
    (hQ : ∀ i j, IsEndpointSum (Q i j)) :
    ∀ i j, IsEndpointSum ((P * Q) i j) := by
  intro i j
  rw [Matrix.mul_apply]
  apply isEndpointSum_finsetSum
  intro k _
  exact (hP i k).mul (hQ k j)

theorem gaussianWordPolynomial_isEndpointSum (w : List ι) (i j : n) :
    IsEndpointSum (gaussianWordPolynomial w i j) := by
  induction w generalizing i j with
  | nil =>
    simp only [gaussianWordPolynomial, List.map_nil, List.prod_nil, Matrix.one_apply]
    split_ifs
    · exact isEndpointSum_one
    · exact isEndpointSum_zero
  | cons s w ih =>
    change IsEndpointSum (((gaussianProjectorPolynomial s * gaussianWordPolynomial w : Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ)) i j))
    exact matrix_mul_isEndpointSum (gaussianProjectorPolynomial_isEndpointSum s)
      ih i j

theorem gaussianWordTracePolynomial_isEndpointSum (w : List ι) :
    IsEndpointSum (Matrix.trace (gaussianWordPolynomial w :
      Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ))) := by
  apply isEndpointSum_finsetSum
  intro i _
  exact gaussianWordPolynomial_isEndpointSum w i i

/-- The actual rank-one Hermitian matrix z z*, with z=x+iy. -/
def gaussianProjector (x : ((ι × n) × Bool) → ℝ) (s : ι) : Matrix n n ℂ :=
  fun i j => endpointValue ((s, i), false) x * star (endpointValue ((s, j), false) x)

def gaussianWordMatrix (x : ((ι × n) × Bool) → ℝ) (w : List ι) : Matrix n n ℂ :=
  (w.map (gaussianProjector x)).prod

theorem complexEval_gaussianProjectorPolynomial
    (x : ((ι × n) × Bool) → ℝ) (s : ι) (i j : n) :
    complexEval (gaussianProjectorPolynomial s i j) x = gaussianProjector x s i j := by
  simp only [gaussianProjectorPolynomial, gaussianProjector, complexEval_mul,
    complexEval_endpointPolynomial, endpointValue_true_eq_conj]

theorem complexEval_gaussianWordPolynomial
    (x : ((ι × n) × Bool) → ℝ) (w : List ι) (i j : n) :
    complexEval (gaussianWordPolynomial w i j) x = gaussianWordMatrix x w i j := by
  induction w generalizing i j with
  | nil => simp [gaussianWordPolynomial, gaussianWordMatrix, Matrix.one_apply, complexEval]
  | cons s w ih =>
    change complexEval (((gaussianProjectorPolynomial s * gaussianWordPolynomial w : Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ)) i j)) x =
      ((gaussianProjector x s * gaussianWordMatrix x w) i j)
    simp only [Matrix.mul_apply, complexEval, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg₂ (· * ·) (complexEval_gaussianProjectorPolynomial x s i k) (ih k j)

theorem complexEval_gaussianWordTracePolynomial
    (x : ((ι × n) × Bool) → ℝ) (w : List ι) :
    complexEval (Matrix.trace (gaussianWordPolynomial w :
      Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ))) x =
        Matrix.trace (gaussianWordMatrix x w) := by
  simp only [Matrix.trace, Matrix.diag_apply, complexEval, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact complexEval_gaussianWordPolynomial x w i i

/-- Integrability is proved for each actual matrix-word trace. -/
theorem gaussian_integrable_wordTrace (w : List ι) :
    Integrable (fun x : ((ι × n) × Bool) → ℝ => Matrix.trace (gaussianWordMatrix x w))
      (gaussianProductLaw ((ι × n) × Bool)) := by
  apply (gaussian_integrable_complex_polynomial (Matrix.trace
    (gaussianWordPolynomial w : Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ)))).congr
  filter_upwards with x
  exact complexEval_gaussianWordTracePolynomial x w

theorem gaussian_wordTrace_integral_im_zero (w : List ι) :
    (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x w)
      ∂gaussianProductLaw ((ι × n) × Bool)).im = 0 := by
  simp_rw [← complexEval_gaussianWordTracePolynomial]
  exact (gaussianWordTracePolynomial_isEndpointSum (n := n) w).integral_im_zero

theorem gaussian_wordTrace_integral_re_nonneg (w : List ι) :
    0 ≤ (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x w)
      ∂gaussianProductLaw ((ι × n) × Bool)).re := by
  simp_rw [← complexEval_gaussianWordTracePolynomial]
  exact (gaussianWordTracePolynomial_isEndpointSum (n := n) w).integral_re_nonneg

/-- Products of traces are also integrable, including words sharing labels. -/
theorem gaussian_integrable_wordTrace_mul (w v : List ι) :
    Integrable (fun x : ((ι × n) × Bool) → ℝ =>
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v))
      (gaussianProductLaw ((ι × n) × Bool)) := by
  apply (gaussian_integrable_complex_polynomial (Matrix.trace
      (gaussianWordPolynomial w : Matrix n n (MvPolynomial ((ι × n) × Bool) ℂ)) *
        Matrix.trace (gaussianWordPolynomial v))).congr
  filter_upwards with x
  rw [complexEval_mul]
  change complexEval (Matrix.trace (gaussianWordPolynomial w)) x *
    complexEval (Matrix.trace (gaussianWordPolynomial v)) x = _
  rw [complexEval_gaussianWordTracePolynomial, complexEval_gaussianWordTracePolynomial]

theorem gaussian_wordTrace_mul_integral_im_zero (w v : List ι) :
    (∫ x : ((ι × n) × Bool) → ℝ,
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v)
      ∂gaussianProductLaw ((ι × n) × Bool)).im = 0 := by
  have h := ((gaussianWordTracePolynomial_isEndpointSum (n := n) w).mul
    (gaussianWordTracePolynomial_isEndpointSum (n := n) v)).integral_im_zero
  simpa only [complexEval, map_mul, ← complexEval_gaussianWordTracePolynomial] using h

theorem gaussian_wordTrace_mul_integral_re_nonneg (w v : List ι) :
    0 ≤ (∫ x : ((ι × n) × Bool) → ℝ,
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v)
      ∂gaussianProductLaw ((ι × n) × Bool)).re := by
  have h := ((gaussianWordTracePolynomial_isEndpointSum (n := n) w).mul
    (gaussianWordTracePolynomial_isEndpointSum (n := n) v)).integral_re_nonneg
  simpa only [complexEval, map_mul, ← complexEval_gaussianWordTracePolynomial] using h

end AHH
