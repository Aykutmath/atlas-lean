import CovarianceTraceExpansion

noncomputable section
open scoped BigOperators Matrix
open GaussianTensorTrace

namespace GaussianTensorTraceConsumers

/-- Coordinate input uses the sample-major product-law index convention. -/
theorem entry_covariance_trace (n h m : ℕ) (hm : 0 < m)
    (x : (Fin n × Fin h) → ℝ) :
    Matrix.trace ((covariance (fun i r => x (i,r)))^m) =
      ∑ f : Fin m → Fin n, ∑ g : Fin m → Fin h,
        ∏ e : Fin m × Fin 2, x (f (endpointColumn m e),g (endpointRow m e)) := by
  exact covarianceTrace_eq_endpointSum (fun i r => x (i,r)) m hm

/-- Literal sum of tensor outer products, with explicit independent coordinate
arrays. This statement is directly usable under either a joint product integral
or two nested independent integrals. -/
theorem entry_tensor_covariance_trace (n h m : ℕ) (hm : 0 < m)
    (x y : (Fin n × Fin h) → ℝ) :
    Matrix.trace ((∑ i : Fin n,
      Matrix.vecMulVec (fun r : Fin h × Fin h => x (i,r.1) * y (i,r.2))
        (fun r : Fin h × Fin h => x (i,r.1) * y (i,r.2)))^m) =
      ∑ f : Fin m → Fin n, ∑ g : Fin m → Fin h, ∑ k : Fin m → Fin h,
        (∏ e : Fin m × Fin 2, x (f (endpointColumn m e),g (endpointRow m e))) *
        (∏ e : Fin m × Fin 2, y (f (endpointColumn m e),k (endpointRow m e))) := by
  simpa only [covariance_eq_sum_outer, tensorColumns, endpointMonomial] using!
    tensorCovarianceTrace_eq_endpointSum (fun i r => x (i,r)) (fun i r => y (i,r)) m hm

/-- The conventional row-major h by q rectangular matrix expansion. -/
theorem gaussian_rectangular_trace (h q m : ℕ) (hm : 0 < m)
    (x : (Fin h × Fin q) → ℝ) :
    Matrix.trace (((Matrix.of (fun r i => x (r,i))) *
      (Matrix.of (fun r i => x (r,i)))ᵀ)^m) =
      ∑ f : Fin m → Fin q, ∑ g : Fin m → Fin h,
        ∏ e : Fin m × Fin 2, x (g (endpointRow m e),f (endpointColumn m e)) := by
  exact matrix_mul_transpose_trace_eq_endpointSum (Matrix.of (fun r i => x (r,i))) m hm

#print axioms entry_covariance_trace
#print axioms entry_tensor_covariance_trace
#print axioms gaussian_rectangular_trace
end GaussianTensorTraceConsumers
