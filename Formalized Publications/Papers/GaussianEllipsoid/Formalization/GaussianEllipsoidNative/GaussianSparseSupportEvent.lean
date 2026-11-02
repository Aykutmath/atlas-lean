import GaussianSparseSupport
import SparseSupportEntropy

noncomputable section
open MeasureTheory GaussianTensorMoments
namespace GaussianEllipsoid.SparseSupport

/-- Absolute sparse-prefix parameter. -/
def sparseKappa : ℝ := 1/8192

/-- The support cutoff used by the multiscale sparse prefix. -/
def sparseSupportSize (d : ℕ) : ℕ := Nat.floor ((d : ℝ)/(8192*Real.log (d : ℝ)))

theorem sparseSupportSize_eq (d : ℕ) :
    sparseSupportSize d = Nat.floor (sparseKappa*(d : ℝ)/Real.log (d : ℝ)) := by
  unfold sparseSupportSize sparseKappa
  congr 1
  ring

/-- Actual simultaneous Gaussian small-support event, with explicit aspect-ratio
cutoff and exponential probability. This replaces the imported Davidson–Szarek
step by a proved product-law chi-square/net argument. -/
theorem sparse_good_event (A : ℝ) (hA : 0 < A) (d n : ℕ)
    (hd : GaussianEllipsoid.sparseEntropyCutoff A ≤ d)
    (hn : (n : ℝ) ≤ A*(d : ℝ)^2) :
    MeasurableSet (sparseGood (2*(d/4)) n (sparseSupportSize d)) ∧
    (matrixPairLaw (2*(d/4)) n).real
      (sparseGood (2*(d/4)) n (sparseSupportSize d))ᶜ ≤ Real.exp (-(d : ℝ)/2048) ∧
    ∀ p ∈ sparseGood (2*(d/4)) n (sparseSupportSize d),
      ∀ I : Finset (Fin n), I.card ≤ sparseSupportSize d →
      ∀ v : EuclideanSpace ℝ (Fin I.card),
        (d : ℝ)/12 * ‖v‖^2 ≤ ‖supportOperator (2*(d/4)) n I p.1 v‖^2 ∧
        (d : ℝ)/12 * ‖v‖^2 ≤ ‖supportOperator (2*(d/4)) n I p.2 v‖^2 := by
  refine ⟨sparseGood_measurable _ _ _, ?_, ?_⟩
  · exact (sparseGood_failure_le _ _ _).trans
      (GaussianEllipsoid.sparse_support_entropy_eventual A hA d n hd hn)
  · intro p hp I hI v
    have hd8192 : 8192 ≤ d := (le_max_left _ _).trans hd
    exact sparseGood_dimension_lower (by omega) hp I hI v

end GaussianEllipsoid.SparseSupport
#print axioms GaussianEllipsoid.SparseSupport.sparseSupportSize_eq
#print axioms GaussianEllipsoid.SparseSupport.sparse_good_event
