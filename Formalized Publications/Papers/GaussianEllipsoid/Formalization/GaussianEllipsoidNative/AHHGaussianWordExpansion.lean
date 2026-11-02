import AHHGaussianTensorMoments
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite, order-preserving noncommutative power expansions and their actual
Gaussian expectations. Every word of the specified length occurs once. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix
namespace AHH
open GaussianTensorMoments

/-- Noncommutative multinomial expansion indexed by all functions on `Fin m`. -/
theorem sum_pow_eq_sum_wordProducts {ι R : Type*} [Fintype ι] [Semiring R]
    (P : ι → R) (m : ℕ) :
    (∑ s, P s) ^ m = ∑ w : Fin m → ι, ((List.ofFn w).map P).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Fintype.sum_prod_type (fun p : ι × (Fin m → ι) =>
      P p.1 * ((List.ofFn p.2).map P).prod)]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => ι))
    intro p
    simp [Fin.consEquiv, List.ofFn_succ]

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- Pathwise expansion of the Gaussian sample covariance power into all words. -/
theorem gaussian_projectorSum_pow (x : ((ι × n) × Bool) → ℝ) (m : ℕ) :
    (∑ s, gaussianProjector x s) ^ m =
      ∑ w : Fin m → ι, gaussianWordMatrix x (List.ofFn w) :=
  sum_pow_eq_sum_wordProducts (gaussianProjector x) m

/-- Actual covariance-power traces are Bochner integrable. -/
theorem gaussian_integrable_projectorSum_pow_trace (m : ℕ) :
    Integrable (fun x : ((ι × n) × Bool) → ℝ =>
      Matrix.trace ((∑ s, gaussianProjector x s) ^ m))
      (gaussianProductLaw ((ι × n) × Bool)) := by
  simp_rw [gaussian_projectorSum_pow, Matrix.trace_sum]
  exact integrable_finsetSum _ (fun w _ => gaussian_integrable_wordTrace (List.ofFn w))

/-- The covariance trace moment equals the finite sum of actual word moments. -/
theorem gaussian_projectorSum_trace_moment (m : ℕ) :
    (∫ x : ((ι × n) × Bool) → ℝ,
      Matrix.trace ((∑ s, gaussianProjector x s) ^ m)
      ∂gaussianProductLaw ((ι × n) × Bool)) =
    ∑ w : Fin m → ι, ∫ x : ((ι × n) × Bool) → ℝ,
      Matrix.trace (gaussianWordMatrix x (List.ofFn w))
      ∂gaussianProductLaw ((ι × n) × Bool) := by
  simp_rw [gaussian_projectorSum_pow, Matrix.trace_sum]
  exact integral_finsetSum _ (fun w _ => gaussian_integrable_wordTrace (List.ofFn w))

/-- The tensor covariance power has the same complete ordered-word expansion. -/
theorem gaussian_tensorProjectorSum_pow (x y : GaussianCoordinates ι n) (m : ℕ) :
    (∑ s, gaussianTensorProjector x y s) ^ m =
      ∑ w : Fin m → ι, gaussianTensorWordMatrix x y (List.ofFn w) :=
  sum_pow_eq_sum_wordProducts (gaussianTensorProjector x y) m

/-- Tensor covariance-power traces are integrable under the actual two-factor law. -/
theorem gaussian_integrable_tensorProjectorSum_pow_trace (m : ℕ) :
    Integrable (fun z : GaussianCoordinates ι n × GaussianCoordinates ι n =>
      Matrix.trace ((∑ s, gaussianTensorProjector z.1 z.2 s) ^ m))
      gaussianTensorLaw := by
  simp_rw [gaussian_tensorProjectorSum_pow, Matrix.trace_sum]
  exact integrable_finsetSum _ (fun w _ => gaussian_integrable_tensorWordTrace (List.ofFn w))

/-- Exact finite all-word expansion of the actual tensor covariance trace moment. -/
theorem gaussian_tensorProjectorSum_trace_moment (m : ℕ) :
    (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace ((∑ s, gaussianTensorProjector z.1 z.2 s) ^ m)
      ∂gaussianTensorLaw) =
    ∑ w : Fin m → ι, ∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 (List.ofFn w))
      ∂gaussianTensorLaw := by
  simp_rw [gaussian_tensorProjectorSum_pow, Matrix.trace_sum]
  exact integral_finsetSum _ (fun w _ => gaussian_integrable_tensorWordTrace (List.ofFn w))

/-- The tensor covariance trace moment is the sum of the squares of the
one-factor Gaussian word moments, with no abstract moment assumptions. -/
theorem gaussian_tensorProjectorSum_trace_moment_eq_sum_squares (m : ℕ) :
    (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace ((∑ s, gaussianTensorProjector z.1 z.2 s) ^ m)
      ∂gaussianTensorLaw) =
    ∑ w : Fin m → ι,
      (∫ x : GaussianCoordinates ι n,
        Matrix.trace (gaussianWordMatrix x (List.ofFn w))
        ∂gaussianProductLaw ((ι × n) × Bool)) ^ 2 := by
  rw [gaussian_tensorProjectorSum_trace_moment]
  apply Finset.sum_congr rfl
  intro w _
  exact gaussian_tensorWordTrace_integral (List.ofFn w)

end AHH
