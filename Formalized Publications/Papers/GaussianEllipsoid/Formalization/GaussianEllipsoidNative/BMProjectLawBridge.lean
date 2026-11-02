import GaussianEllipsoid.GaussianProbability
import BMProjectBasicBridge

/-!
# Unconditional BM on the actual supplied project Gaussian law

The imported GaussianProbabilityLean419 is the complete explicitly documented Lean
4.19 syntax/API port of the supplied GaussianProbability(1).lean. Its actual
law definitions are unchanged, and all original theorems are retained. The
supplied source is not modified. The project's original dependency pin is
still required to claim compilation on its current toolchain.

This module imports no substitute BelowObjects module. The final expression
uses the actual project law, types, residual and dimension ratio, and expands
the exact Loewner-box and real-power infimum definitions inline.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace GaussianEllipsoidBMBridge

/-- The actual supplied Gaussian vector law is precisely the previously
verified independent scalar Gaussian product, including dimension zero. -/
theorem gaussianVectorLaw_eq_bm (d : ℕ) :
    GaussianEllipsoid.gaussianVectorLaw d =
      GaussianTensorMoments.gaussianProductLaw (Fin d) := rfl

/-- The actual supplied joint sample law is exactly the independent-row raw
law used throughout the proved BM theorem. No marginal-to-joint inference. -/
theorem gaussianSampleLaw_eq_bm (d n : ℕ) :
    GaussianEllipsoid.gaussianSampleLaw d n =
      BMBoxRiskAssembly.coordinateSampleLaw d n := rfl

/-- Exact equality of event probabilities under the actual project law. -/
theorem gaussianSample_probability_eq_bm (d n : ℕ)
    (E : Set (GaussianEllipsoid.Sample d n)) :
    ((GaussianEllipsoid.gaussianSampleLaw d n) E).toReal =
      (BMBoxRiskAssembly.coordinateSampleLaw d n).real E := rfl

/-- Full unconditional original BM formula on the user's actual supplied
law, coordinates, residual and dimension ratio. One positive spectral box
works for all real 1 ≤ r < 4/3; there is no additional analytic premise. -/
theorem bm_formula_actual_project :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (GaussianEllipsoid.dimensionRatio n) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
        ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
          Tendsto (fun d => ((GaussianEllipsoid.gaussianSampleLaw d (n d))
            {x : GaussianEllipsoid.Sample d (n d) |
              ε < sInf {t : ℝ | ∃ S : GaussianEllipsoid.Square d,
                (S-lo • (1 : GaussianEllipsoid.Square d)).PosSemidef ∧
                (hi • (1 : GaussianEllipsoid.Square d)-S).PosSemidef ∧
                t=(1/(n d:ℝ))*∑ i, |GaussianEllipsoid.residual x S i|^r}}).toReal)
            atTop (nhds 0) := bm_formula_actual_Basic_rawGaussianLaw

end GaussianEllipsoidBMBridge

namespace GaussianEllipsoid

/-- Production-facing coordinate formula using the actual supplied project
names. This theorem can coexist with the original BelowObjects definitions;
it neither redefines bmApproximateFitting nor replaces missing imports. -/
theorem bmApproximateFitting_coordinate_formula :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      Filter.limsup (dimensionRatio n) Filter.atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
        ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
          Filter.Tendsto (fun d => ((gaussianSampleLaw d (n d))
            {x : Sample d (n d) | ε < sInf {t : ℝ | ∃ S : Square d,
              (S-lo • (1 : Square d)).PosSemidef ∧
              (hi • (1 : Square d)-S).PosSemidef ∧
              t=(1/(n d:ℝ))*∑ i, |residual x S i|^r}}).toReal)
            Filter.atTop (nhds 0) := GaussianEllipsoidBMBridge.bm_formula_actual_project

end GaussianEllipsoid
