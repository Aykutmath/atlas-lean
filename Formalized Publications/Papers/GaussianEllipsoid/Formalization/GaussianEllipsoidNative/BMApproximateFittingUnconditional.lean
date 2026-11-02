import BMGordonDischarged
import BMExpectedGordonAssembly

/-! The original BM approximate-fitting statement, with the former expected-Gordon
premise discharged by an actual finite affine Gaussian interpolation proof. -/
noncomputable section
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open scoped ENNReal BigOperators
namespace BMBoxRiskAssembly

/-- Unconditional actual Gaussian conditioned-cone feasibility on every positive
strictly subcritical proportional sample sequence. -/
theorem proportionalGaussianConeInput : ProportionalGaussianConeInput :=
  proportionalGaussianConeInput_of_expectedGordon BMGordon.expectedGordonPrinciple

/-- Unconditional original BM approximate-fitting assertion with one fixed
positive spectral box before every exponent in the required range. -/
theorem bmApproximateFitting :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMminRiskAllR n lo hi :=
  bmApproximateFitting_of_expectedGordon BMGordon.expectedGordonPrinciple

/-- Fully expanded original-law, arbitrary-positive-count, strict-limsup BM
physical real-power infimum-risk statement. There is no extra analytic premise. -/
theorem bmApproximateFitting_original_formula :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
        ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
          Tendsto (fun d => (coordinateSampleLaw d (n d)).real
            {x | ε < sInf {t : ℝ | ∃ S ∈ BMRescaling.spectralBox d lo hi,
              t = (1/(n d:ℝ))*∑ i,
                |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^r}})
            atTop (nhds 0) :=
  bmApproximateFitting_original_formula_of_expectedGordon BMGordon.expectedGordonPrinciple

#print axioms proportionalGaussianConeInput
#print axioms bmApproximateFitting
#print axioms bmApproximateFitting_original_formula
end BMBoxRiskAssembly
