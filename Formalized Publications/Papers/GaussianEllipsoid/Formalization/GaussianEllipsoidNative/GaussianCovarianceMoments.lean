import GaussianNetworkMoments
import CovarianceTraceConsumers
import Mathlib.Tactic

/-! Exact expectation comparison for actual one-factor and two-factor Gaussian
covariance matrices, including all trace-power integrability obligations. -/

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorTrace GaussianTensorTraceConsumers
open scoped BigOperators Matrix

namespace GaussianTensorMoments

abbrev GaussianEntries (n h : ℕ) := (Fin n × Fin h) → ℝ

def gaussianCovariance (n h : ℕ) (x : GaussianEntries n h) : Matrix (Fin h) (Fin h) ℝ :=
  covariance (fun i r => x (i,r))

def tensorGaussianLaw (n h : ℕ) : Measure (GaussianEntries n h × GaussianEntries n h) :=
  (gaussianProductLaw (Fin n × Fin h)).prod (gaussianProductLaw (Fin n × Fin h))

instance tensorGaussianLaw_probability (n h : ℕ) : IsProbabilityMeasure (tensorGaussianLaw n h) := by
  unfold tensorGaussianLaw
  infer_instance

def tensorGaussianCovariance (n h : ℕ) (z : GaussianEntries n h × GaussianEntries n h) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℝ :=
  ∑ i : Fin n,
    Matrix.vecMulVec (fun r : Fin h × Fin h => z.1 (i,r.1) * z.2 (i,r.2))
      (fun r : Fin h × Fin h => z.1 (i,r.1) * z.2 (i,r.2))

/-- Every positive trace power of the Gaussian sample covariance is integrable. -/
theorem gaussianCovariance_integrable_trace_power (n h m : ℕ) (hm : 0 < m) :
    Integrable (fun x => Matrix.trace ((gaussianCovariance n h x)^m))
      (gaussianProductLaw (Fin n × Fin h)) := by
  simp_rw [gaussianCovariance, entry_covariance_trace n h m hm]
  apply integrable_finset_sum
  intro f hf
  apply integrable_finset_sum
  intro g hg
  exact gaussianProductLaw_integrable_endpoints
    (fun e : Fin m × Fin 2 => (f (endpointColumn m e),g (endpointRow m e)))

/-- Its expectation is exactly the one-factor Gaussian endpoint network. -/
theorem gaussianCovariance_trace_moment_eq_network (n h m : ℕ) (hm : 0 < m) :
    (∫ x, Matrix.trace ((gaussianCovariance n h x)^m)
      ∂gaussianProductLaw (Fin n × Fin h)) =
      oneNetworkMoment (endpointColumn m) (endpointRow m) n h := by
  have hi (f : Fin m → Fin n) (g : Fin m → Fin h) :=
    gaussianProductLaw_integrable_endpoints
      (fun e : Fin m × Fin 2 => (f (endpointColumn m e),g (endpointRow m e)))
  simp_rw [gaussianCovariance, entry_covariance_trace n h m hm]
  rw [integral_finset_sum _ (fun f _ => integrable_finset_sum _ (fun g _ => hi f g))]
  unfold oneNetworkMoment
  apply Finset.sum_congr rfl
  intro f hf
  exact integral_finset_sum _ (fun g _ => hi f g)

/-- Tensor trace-power integrability is proved under the actual independent
pair of finite Gaussian product laws. -/
theorem tensorGaussianCovariance_integrable_trace_power (n h m : ℕ) (hm : 0 < m) :
    Integrable (fun z => Matrix.trace ((tensorGaussianCovariance n h z)^m))
      (tensorGaussianLaw n h) := by
  simp_rw [tensorGaussianCovariance, entry_tensor_covariance_trace n h m hm]
  apply integrable_finset_sum
  intro f hf
  apply integrable_finset_sum
  intro g hg
  apply integrable_finset_sum
  intro k hk
  exact (gaussianProductLaw_integrable_endpoints
    (fun e : Fin m × Fin 2 => (f (endpointColumn m e),g (endpointRow m e)))).mul_prod
    (gaussianProductLaw_integrable_endpoints
      (fun e : Fin m × Fin 2 => (f (endpointColumn m e),k (endpointRow m e))))

/-- The actual tensor covariance trace expectation equals the joined network. -/
theorem tensorGaussianCovariance_trace_moment_eq_network (n h m : ℕ) (hm : 0 < m) :
    (∫ z, Matrix.trace ((tensorGaussianCovariance n h z)^m) ∂tensorGaussianLaw n h) =
      twoNetworkMoment (endpointColumn m) (endpointRow m) n h := by
  have hi (f : Fin m → Fin n) (g k : Fin m → Fin h) :=
    (gaussianProductLaw_integrable_endpoints
      (fun e : Fin m × Fin 2 => (f (endpointColumn m e),g (endpointRow m e)))).mul_prod
    (gaussianProductLaw_integrable_endpoints
      (fun e : Fin m × Fin 2 => (f (endpointColumn m e),k (endpointRow m e))))
  simp_rw [tensorGaussianCovariance, entry_tensor_covariance_trace n h m hm]
  unfold tensorGaussianLaw
  rw [integral_finset_sum _ (fun f _ =>
    integrable_finset_sum _ (fun g _ => integrable_finset_sum _ (fun k _ => hi f g k)))]
  unfold twoNetworkMoment
  apply Finset.sum_congr rfl
  intro f hf
  rw [integral_finset_sum _ (fun g _ => integrable_finset_sum _ (fun k _ => hi f g k))]
  apply Finset.sum_congr rfl
  intro g hg
  rw [integral_finset_sum _ (fun k _ => hi f g k)]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_prod_mul (L := ℝ)
    (fun x : GaussianEntries n h => ∏ e : Fin m × Fin 2,
      x (f (endpointColumn m e),g (endpointRow m e)))
    (fun y : GaussianEntries n h => ∏ e : Fin m × Fin 2,
      y (f (endpointColumn m e),k (endpointRow m e)))

/-- Unconditional Gaussian tensor trace-moment comparison. The only hypotheses
are positive moment order and the integer sample-count enlargement n≤q². -/
theorem tensorGaussianCovariance_trace_moment_le_square
    (n q h m : ℕ) (hm : 0 < m) (hq : 1 ≤ q) (hn : n ≤ q^2) :
    (∫ z, Matrix.trace ((tensorGaussianCovariance n h z)^m) ∂tensorGaussianLaw n h) ≤
      (∫ x, Matrix.trace ((gaussianCovariance q h x)^m)
        ∂gaussianProductLaw (Fin q × Fin h))^2 := by
  rw [tensorGaussianCovariance_trace_moment_eq_network n h m hm,
    gaussianCovariance_trace_moment_eq_network q h m hm]
  exact twoNetworkMoment_le_oneNetworkMoment_sq _ _ hq hn

#print axioms gaussianCovariance_integrable_trace_power
#print axioms tensorGaussianCovariance_integrable_trace_power
#print axioms tensorGaussianCovariance_trace_moment_le_square

end GaussianTensorMoments
