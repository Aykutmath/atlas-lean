import AHHCovarianceJensen
import AHHGaussianTail

/-! Source-facing Jensen comparison on the literal four-real Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory AHHAlgebraBridges AHHGaussian
open scoped BigOperators Matrix.Norms.L2Operator
namespace AHHRadial

/-- The operator in the radial model is exactly the manuscript's covariance,
including the denominator 2h in each product-state vector. -/
theorem gaussianCovariance_actual_eq (n h : ℕ) (s t : Bool) (x : FourEntries n h) :
    gaussianCovariance n h (actualNormalizedPairs n h s t x) =
      cMatrixCLM (actualComplexCovariance n h s t x) := by
  unfold gaussianCovariance actualComplexCovariance complexCov
  simp only [cMatrixCLM, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold productProjector cMatrixCLM
  congr 1
  congr 1
  funext p
  exact normalizedProductRow_eq_productState h s t (fourRealRows n h x i) p

/-- Fully concrete Haar/Gaussian Jensen bridge. Its only numerical assumption
is h>0; every probability law and all integrability facts are explicit. -/
theorem haar_expected_norm_le_actualGaussian (n h : ℕ) (hh : 0 < h) (s t : Bool) :
    (∫ d, unitCovarianceNorm n h d ∂directionsLaw n h) ≤
      ∫ x, ‖cMatrixCLM (actualComplexCovariance n h s t x)‖ ∂fourGaussianLaw n h := by
  have hc : Continuous (fun z => ‖gaussianCovariance n h z‖) := by
    unfold gaussianCovariance
    apply Continuous.norm
    apply continuous_finset_sum
    intro i hi
    exact (continuous_productProjector h).comp (continuous_apply i)
  have hm := integral_map (μ := fourGaussianLaw n h)
    (φ := actualNormalizedPairs n h s t) (f := fun z => ‖gaussianCovariance n h z‖)
    (actualNormalizedPairs_preserving n h hh s t).measurable.aemeasurable
    hc.aestronglyMeasurable
  rw [(actualNormalizedPairs_preserving n h hh s t).map_eq] at hm
  have he := unitCovariance_expected_norm_le_gaussian n h hh
  rw [hm] at he
  simpa only [gaussianCovariance_actual_eq] using he

/-- Common radial expectation for every fixed sign pair. -/
theorem actualComplexCovariance_expected_norm_eq_radial (n h : ℕ) (hh : 0 < h)
    (s t : Bool) :
    (∫ x, ‖cMatrixCLM (actualComplexCovariance n h s t x)‖ ∂fourGaussianLaw n h) =
      ∫ z, ‖gaussianCovariance n h z‖ ∂gaussianPairsLaw n h := by
  have hm := integral_map (μ := fourGaussianLaw n h)
    (φ := actualNormalizedPairs n h s t) (f := fun z => ‖gaussianCovariance n h z‖)
    (actualNormalizedPairs_preserving n h hh s t).measurable.aemeasurable
    (continuous_gaussianCovariance n h).norm.aestronglyMeasurable
  rw [(actualNormalizedPairs_preserving n h hh s t).map_eq] at hm
  simpa only [gaussianCovariance_actual_eq] using hm.symm

/-- Exact sign invariance, proved by equality with the common actual radial law. -/
theorem actualComplexCovariance_expected_norm_sign_invariant (n h : ℕ) (hh : 0 < h)
    (s t : Bool) :
    (∫ x, ‖cMatrixCLM (actualComplexCovariance n h s t x)‖ ∂fourGaussianLaw n h) =
      ∫ x, ‖cMatrixCLM (actualComplexCovariance n h true true x)‖ ∂fourGaussianLaw n h := by
  rw [actualComplexCovariance_expected_norm_eq_radial n h hh s t,
    actualComplexCovariance_expected_norm_eq_radial n h hh true true]

/-- Finite expected norm on the exact source-facing Gaussian measure. -/
theorem actualComplexCovariance_norm_integrable (n h : ℕ) (hh : 0 < h) (s t : Bool) :
    Integrable (fun x => ‖cMatrixCLM (actualComplexCovariance n h s t x)‖)
      (fourGaussianLaw n h) := by
  have hi := (actualNormalizedPairs_preserving n h hh s t).integrable_comp_of_integrable
    (gaussianCovariance_integrable n h hh).norm
  exact hi.congr (Filter.Eventually.of_forall (fun x => congrArg norm
    (gaussianCovariance_actual_eq n h s t x)))

#print axioms gaussianCovariance_actual_eq
#print axioms haar_expected_norm_le_actualGaussian
#print axioms actualComplexCovariance_norm_integrable
#print axioms actualComplexCovariance_expected_norm_sign_invariant
end AHHRadial
