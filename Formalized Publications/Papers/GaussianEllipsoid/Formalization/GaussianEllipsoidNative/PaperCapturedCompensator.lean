import PaperExactCompensator
import ActualCapturedCross

noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Module GaussianEllipsoid GaussianEllipsoidCandidate
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.PaperCanonicalPolar

/-- The none index is precisely Z0: the exact partial polar of the merged
small-support-prefix contribution. It is not an extra retained-group witness. -/
theorem captured_none_exact_polar {N r q : ℕ} (G : ℕ → Finset (Fin N)) (p k : ℕ)
    (u : Fin N → ℝ) (X : Fin N → Euclid q × Euclid r) :
    exactPrefixBlockWitness u X (capturedBlockLo G p k none) (capturedBlockHi G p k none) =
      polarWitness (prefixBilinearSynthesis u X (supportCut G p)) := by
  simp only [capturedBlockLo,capturedBlockHi,exactPrefixBlockWitness,projectedPrefixBlock_zero_left]

/-- The source's fixed captured family: Z0 and exactly the selected groups in
[p,k), with hi<=t restricting it further to the already revealed groups. -/
def capturedExactCross {N r q : ℕ} (G : ℕ → Finset (Fin N)) (p k : ℕ)
    (u v : Fin N → ℝ) (X : Fin N → Euclid q × Euclid r) : ℝ :=
  exactPrefixCross u v (capturedBlockLo G p k) (capturedBlockHi G p k) X

def capturedExactVariance {N r q : ℕ} (G : ℕ → Finset (Fin N)) (p k : ℕ)
    (u v : Fin N → ℝ) (X : Fin N → Euclid q × Euclid r) : ℝ :=
  exactPrefixVariance u v (capturedBlockLo G p k) (capturedBlockHi G p k) X

/-- Random-compensator expectation for precisely the deterministic captured
subset including Z0. All interval order/separation premises are discharged. -/
theorem paper_captured_exact_compensator {N r q : ℕ}
    (G : ℕ → Finset (Fin N)) (p k : ℕ) (u v : Fin N → ℝ)
    (B : ℝ) (hB : 0 < B) (hcoef : ∀ i,|v i| ≤ B)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamB : lam ≤ 1/(Real.sqrt 2*B)) :
    Integrable (fun X : Fin N → Euclid q × Euclid r =>
      Real.exp (-lam*capturedExactCross G p k u v X-lam^2*capturedExactVariance G p k u v X))
        (gaussianBilinearSampleLaw (Fin N) q r) ∧
    (∫ X : Fin N → Euclid q × Euclid r,
      Real.exp (-lam*capturedExactCross G p k u v X-lam^2*capturedExactVariance G p k u v X)
        ∂gaussianBilinearSampleLaw (Fin N) q r) ≤ 1 :=
  paper_exact_polar_compensator u v (capturedBlockLo G p k) (capturedBlockHi G p k)
    (capturedBlock_ordered G p k) (capturedBlock_separated G p k) B hB hcoef lam hlam hlamB

/-- Exact law transport back through any deterministic coefficient-support
ordering; no assumed equality of Gaussian models is used. -/
theorem paper_captured_exact_compensator_permuted {N r q : ℕ}
    (e : Equiv.Perm (Fin N)) (G : ℕ → Finset (Fin N)) (p k : ℕ) (u v : Fin N → ℝ)
    (B : ℝ) (hB : 0 < B) (hcoef : ∀ i,|v i| ≤ B)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlamB : lam ≤ 1/(Real.sqrt 2*B)) :
    Integrable (fun X : Fin N → Euclid q × Euclid r =>
      Real.exp (-lam*capturedExactCross G p k u v (permuteRows e X)-
        lam^2*capturedExactVariance G p k u v (permuteRows e X)))
        (gaussianBilinearSampleLaw (Fin N) q r) ∧
    (∫ X : Fin N → Euclid q × Euclid r,
      Real.exp (-lam*capturedExactCross G p k u v (permuteRows e X)-
        lam^2*capturedExactVariance G p k u v (permuteRows e X))
        ∂gaussianBilinearSampleLaw (Fin N) q r) ≤ 1 := by
  let F : (Fin N → Euclid q × Euclid r) → ℝ := fun X =>
    Real.exp (-lam*capturedExactCross G p k u v X-lam^2*capturedExactVariance G p k u v X)
  have hh := paper_captured_exact_compensator (r:=r) (q:=q) G p k u v B hB hcoef lam hlam hlamB
  have hp := permuteRows_preserving e q r
  have hm : AEStronglyMeasurable F ((gaussianBilinearSampleLaw (Fin N) q r).map (permuteRows e)) := by
    rw [hp.map_eq]
    exact hh.1.aestronglyMeasurable
  constructor
  · exact hp.integrable_comp_of_integrable hh.1
  · have heq := integral_map hp.measurable.aemeasurable hm
    rw [hp.map_eq] at heq
    exact heq.symm.le.trans hh.2
end GaussianEllipsoid.PaperCanonicalPolar
#print axioms GaussianEllipsoid.PaperCanonicalPolar.paper_captured_exact_compensator_permuted
#print axioms GaussianEllipsoid.PaperCanonicalPolar.captured_none_exact_polar
