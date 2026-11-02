import AHHSmoothSphereEntropy
import AHHExactEquation11SmallCases

/-! Unconditional closure of the actual product-sphere entropy inequality and
the exact AHH equation (11), k=2. Every analytic input is proved in the imported
Gaussian, geometric, radial-cutoff and dominated-convergence modules. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges AHHGaussian
namespace AHHRadial

/-- The previously unresolved concrete power-entropy inequality, for every
real exponent and the actual iid product-sphere law. -/
theorem spherePowerEntropyBound_general (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h) :
    SpherePowerEntropyBound n h :=
  spherePowerEntropyBound_of_smooth n h hn hh (smoothSpherePowerEntropyBound n h hh)

/-- Exact family requested by the parameter-complete equation (11) reduction. -/
theorem spherePowerEntropyBound_family :
    ∀ n h : ℕ, 2 ≤ n → 2 ≤ h → SpherePowerEntropyBound n h := by
  intro n h hn hh
  exact spherePowerEntropyBound_general n h (by omega) hh

/-- Unconditional positive and negative real moments of the actual sphere
covariance observable, with the self-bounding constant `h-1`. -/
theorem sphere_moments_unconditional (n h : ℕ) (hn : 0 < n) (hh : 2 ≤ h) :
    (∀ q : ℝ, 1 ≤ q →
      (∫ d, (unitCovarianceNorm n h d)^q ∂directionsLaw n h)^(1/q) ≤
        unitCovarianceMean n h + (q-1)/((h : ℝ)-1)) ∧
    (∀ t : ℝ, 0 ≤ t →
      Real.log (∫ d, (unitCovarianceNorm n h d / unitCovarianceMean n h)^(-t)
        ∂directionsLaw n h) ≤ t*(t+1)/((h : ℝ)-1)) :=
  sphere_moments_of_powerEntropy n h hn hh (spherePowerEntropyBound_general n h hn hh)

/-- Exact equation (11) for the actual independent real Gaussian realization
and either complex sign in each factor. No entropy or analytic hypothesis. -/
theorem actual_equation11 (n h : ℕ) (hh : 0 < h) (s t : Bool)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (actualComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) :=
  actual_equation11_of_large_parameters_powerEntropy n h hh
    (spherePowerEntropyBound_family n h) s t e Δ he he1 hΔ

/-- Complete paper-facing AHH equation (11), k=2: inclusive event, exact
constants 16 and 8, true independent Gaussian law, Haar unit-vector mean,
all sample counts, every positive dimension, and literal real signs ±1. -/
theorem paper_equation11 (n h : ℕ) (hh : 0 < h)
    (s t : ℝ) (hs : s = -1 ∨ s = 1) (ht : t = -1 ∨ t = 1)
    (e Δ : ℝ) (he : 0 < e) (he1 : e ≤ 1) (hΔ : 0 < Δ) :
    (fourGaussianLaw n h).real {x | e*unitCovarianceMean n h+Δ ≤
      |‖cMatrixCLM (paperComplexCovariance n h s t x)‖-unitCovarianceMean n h|} ≤
        4*n*Real.exp (-(h : ℝ)*e^2/16) +
          2*Real.exp (-((h : ℝ)-1)*Δ^2/8) :=
  paper_equation11_of_powerEntropy_family spherePowerEntropyBound_family
    n h hh s t hs ht e Δ he he1 hΔ

#print axioms spherePowerEntropyBound_general
#print axioms spherePowerEntropyBound_family
#print axioms sphere_moments_unconditional
#print axioms actual_equation11
#print axioms paper_equation11
end AHHRadial
