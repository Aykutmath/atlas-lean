import SparseNuclearPrefix

noncomputable section
open MeasureTheory
namespace GaussianEllipsoid.SparseSupport

/-- Complete actual-law sparse nuclear-prefix event, with fixed numerical
constants and an explicit dimension cutoff. No Gaussian concentration or
singular-value claim is left as a premise. -/
theorem sparse_nuclear_prefix_event (A : ℝ) (hA : 0 < A) (d n : ℕ)
    (hd : GaussianEllipsoid.sparseEntropyCutoff A ≤ d)
    (hn : (n : ℝ) ≤ A*(d : ℝ)^2) :
    MeasurableSet (sparseGood (2*(d/4)) n (sparseSupportSize d)) ∧
    (matrixPairLaw (2*(d/4)) n).real
      (sparseGood (2*(d/4)) n (sparseSupportSize d))ᶜ ≤ Real.exp (-(d : ℝ)/2048) ∧
    ∀ p ∈ sparseGood (2*(d/4)) n (sparseSupportSize d),
      ∀ I : Finset (Fin n), I.card ≤ sparseSupportSize d →
      ∀ u : Fin I.card → ℝ,
        Real.sqrt (d : ℝ)/12 * (∑ i, |u i|) ≤
          spectralNuclearNorm (operatorFrobenius (sparsePrefixOperator d n I p u)) := by
  have hE := sparse_good_event A hA d n hd hn
  refine ⟨hE.1, hE.2.1, ?_⟩
  intro p hp I hI u
  have hd8192 : 8192 ≤ d := (le_max_left _ _).trans hd
  exact sparseGood_prefix_nuclear_lower (by omega) hp I hI u

end GaussianEllipsoid.SparseSupport
#print axioms GaussianEllipsoid.SparseSupport.sparse_nuclear_prefix_event
