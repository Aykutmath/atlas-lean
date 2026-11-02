import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

noncomputable section
open scoped BigOperators Matrix
namespace GaussianTensorTrace

variable {α β R : Type*}

def consEquiv (α : Type*) (m : ℕ) : (α × (Fin m → α)) ≃ (Fin (m+1) → α) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by simp
  right_inv f := by simp

theorem sum_tuple_cons [Fintype α] [AddCommMonoid R] (m : ℕ)
    (F : (Fin (m+1) → α) → R) :
    (∑ f, F f) = ∑ a, ∑ f : Fin m → α, F (Fin.cons a f) := by
  rw [← (consEquiv α m).sum_comp]
  exact Fintype.sum_prod_type _

/-- Exact finite path expansion; no injectivity condition is imposed on paths. -/
theorem pow_succ_apply [Fintype α] [DecidableEq α] [CommSemiring R]
    (A : Matrix α α R) (m : ℕ) (i j : α) :
    (A ^ (m+1)) i j =
      ∑ f : Fin m → α, ∏ t : Fin (m+1),
        A (@Fin.cons m (fun _ => α) i f t) (@Fin.snoc m (fun _ => α) f j t) := by
  induction m generalizing i j with
  | zero => simp [Fin.snoc]
  | succ m ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    rw [sum_tuple_cons]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro f hf
    simp only [← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- Finite cyclic word expansion of a positive matrix trace power. -/
theorem trace_pow_succ [Fintype α] [DecidableEq α] [CommSemiring R]
    (A : Matrix α α R) (m : ℕ) :
    Matrix.trace (A ^ (m+1)) =
      ∑ f : Fin (m+1) → α, ∏ t : Fin (m+1), A (f t) (f (finRotate _ t)) := by
  rw [Matrix.trace, sum_tuple_cons]
  apply Finset.sum_congr rfl
  intro i hi
  change (A ^ (m+1)) i i = _
  rw [pow_succ_apply]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Fin.snoc_eq_cons_rotate]


/-- Rectangular products have matching positive trace powers. -/
theorem trace_mul_pow_succ [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (A : Matrix α β R) (B : Matrix β α R) (m : ℕ) :
    Matrix.trace ((A * B) ^ (m+1)) = Matrix.trace ((B * A) ^ (m+1)) := by
  have hpow : ∀ k : ℕ, (A * B) ^ (k+1) = A * (B * A)^k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc]
  rw [hpow, Matrix.trace_mul_cycle, ← pow_succ']

/-- Covariance matrix of the columns, with entries specified explicitly. -/
def covariance [Fintype α] [CommSemiring R] (v : α → β → R) : Matrix β β R :=
  fun r s => ∑ i, v i r * v i s

theorem covariance_eq_mul_transpose [Fintype α] [CommSemiring R]
    (v : α → β → R) : covariance v = (Matrix.of v)ᵀ * Matrix.of v := by
  ext r s
  rfl

/-- Trace expansion in sample slots and row slots. -/
theorem covariance_trace_pow_succ [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (v : α → β → R) (m : ℕ) :
    Matrix.trace ((covariance v) ^ (m+1)) =
      ∑ f : Fin (m+1) → α, ∑ g : Fin (m+1) → β,
        ∏ t : Fin (m+1), v (f t) (g t) * v (f (finRotate _ t)) (g t) := by
  rw [covariance_eq_mul_transpose, trace_mul_pow_succ, trace_pow_succ]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  simp_rw [Fintype.prod_sum]

/-- The two endpoints at each trace slot. -/
def endpointColumn (m : ℕ) (e : Fin m × Fin 2) : Fin m :=
  if e.2 = 0 then e.1 else finRotate m e.1

def endpointRow (m : ℕ) (e : Fin m × Fin 2) : Fin m := e.1

/-- Coordinate monomial for an endpoint network. -/
def endpointMonomial [CommSemiring R] (v : α → β → R) (m : ℕ)
    (f : Fin m → α) (g : Fin m → β) : R :=
  ∏ e : Fin m × Fin 2, v (f (endpointColumn m e)) (g (endpointRow m e))

theorem endpointMonomial_eq [CommSemiring R] (v : α → β → R) (m : ℕ)
    (f : Fin m → α) (g : Fin m → β) :
    endpointMonomial v m f g =
      ∏ t : Fin m, v (f t) (g t) * v (f (finRotate _ t)) (g t) := by
  simp [endpointMonomial, endpointColumn, endpointRow, Fintype.prod_prod_type,
    Fin.prod_univ_two]

/-- Positive trace powers are exactly the network finite sum; empty row or
sample spaces require no exceptional convention. -/
theorem covarianceTrace_eq_endpointSum [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (v : α → β → R) (m : ℕ) (hm : 0 < m) :
    Matrix.trace ((covariance v)^m) =
      ∑ f : Fin m → α, ∑ g : Fin m → β, endpointMonomial v m f g := by
  cases m with
  | zero => omega
  | succ k => simpa only [endpointMonomial_eq] using covariance_trace_pow_succ v k


/-- Coordinate realization of a tensor-product column vector. -/
def tensorColumns {γ : Type*} [CommSemiring R]
    (a : α → β → R) (b : α → γ → R) : α → (β × γ) → R :=
  fun i r => a i r.1 * b i r.2

/-- Each tensor endpoint monomial splits into the two factor monomials. -/
theorem tensor_endpointMonomial {γ : Type*} [CommSemiring R]
    (a : α → β → R) (b : α → γ → R) (m : ℕ)
    (f : Fin m → α) (g : Fin m → β × γ) :
    endpointMonomial (tensorColumns a b) m f g =
      endpointMonomial a m f (fun t => (g t).1) *
      endpointMonomial b m f (fun t => (g t).2) := by
  simp only [endpointMonomial, tensorColumns, Finset.prod_mul_distrib]

/-- Exact tensor-covariance finite endpoint-network expansion. The same
sample assignment is shared between the two row assignments. -/
theorem tensorCovarianceTrace_eq_endpointSum {γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [CommSemiring R]
    (a : α → β → R) (b : α → γ → R) (m : ℕ) (hm : 0 < m) :
    Matrix.trace ((covariance (tensorColumns a b))^m) =
      ∑ f : Fin m → α, ∑ g : Fin m → β, ∑ k : Fin m → γ,
        endpointMonomial a m f g * endpointMonomial b m f k := by
  rw [covarianceTrace_eq_endpointSum _ _ hm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => β) (fun _ => γ)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [tensor_endpointMonomial, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]

/-- The covariance matrix is the literal finite sum of outer products. -/
theorem covariance_eq_sum_outer [Fintype α] [CommSemiring R]
    (v : α → β → R) :
    covariance v = ∑ i, Matrix.vecMulVec (v i) (v i) := by
  ext r s
  simp [covariance, Matrix.vecMulVec, Matrix.sum_apply]

/-- Row-major matrix-entry realization of the one-factor comparison matrix. -/
theorem matrix_mul_transpose_trace_eq_endpointSum
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [CommSemiring R]
    (G : Matrix β α R) (m : ℕ) (hm : 0 < m) :
    Matrix.trace ((G * Gᵀ)^m) =
      ∑ f : Fin m → α, ∑ g : Fin m → β,
        endpointMonomial (fun i r => G r i) m f g := by
  convert covarianceTrace_eq_endpointSum (fun i r => G r i) m hm using 1
  rfl

#print axioms pow_succ_apply
#print axioms trace_pow_succ
#print axioms trace_mul_pow_succ
#print axioms covarianceTrace_eq_endpointSum
#print axioms tensorCovarianceTrace_eq_endpointSum
#print axioms covariance_eq_sum_outer
#print axioms matrix_mul_transpose_trace_eq_endpointSum
end GaussianTensorTrace

