import BMAllRBoxTransfer
import CyclicRiskLimit
import PaddedBMApproximation

/-!
# The full BM approximate-fitting interface under its sole Gaussian feasibility input

The original sample schedule has only positive counts and a strict ENNReal
limsup below 1/4. Positive proportional padding is internal. The actual cyclic
restriction theorem removes the lower aspect assumption, with no deterministic
monotonicity claim for empirical averages and no extra analytic hypothesis.
-/
noncomputable section
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open GaussianEllipsoidFinalPassage BMSpectralBridge BMCyclicRiskRestriction
open scoped ENNReal

namespace BMBoxRiskAssembly

/-- The remaining genuine Gaussian analytic input, stated directly as actual
conditioned-cone feasibility failure along positive proportional schedules.
This proposition is explicit and is not asserted unconditionally here. -/
def ProportionalGaussianConeInput : Prop :=
  ∀ (N : ℕ → ℕ), (∀ d, 0 < N d) → ∀ a : ℝ, 0 < a → a < 1/4 →
    Tendsto (fun d => (N d:ℝ)/(d:ℝ)^2) atTop (nhds a) →
    ∃ κ R : ℝ, 1 ≤ κ ∧
      Tendsto (fun d => (Measure.pi
        (fun _ : Fin (N d) => gaussianProductLaw (Fin (d*d)))).real
        {z | ¬actualConeFeasible (N d) d κ R z}) atTop (nhds 0)

/-- Full supplied-interface quantifier order: arbitrary positive sample
counts, strict ENNReal limsup below 1/4, and one positive spectral box for
all real 1 ≤ r < 4/3. Only actual Gaussian cone feasibility is assumed. -/
theorem bmApproximateFitting_of_gaussian_cone
    (hGaussian : ProportionalGaussianConeInput) :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMminRiskAllR n lo hi := by
  intro n hn haspect
  obtain ⟨a,ha,haq,N,hdom,hN,hlim,hsub,hlower⟩ :=
    exists_dominating_subcritical_sequence n hn haspect
  obtain ⟨κ,R,hκ,hcone⟩ := hGaussian N hN a ha haq hlim
  obtain ⟨A,hA,hupper⟩ :=
    BMCyclicRiskRestriction.exists_global_quadratic_upper_bound_of_ratio_tendsto N hlim
  obtain ⟨lo,hi,hlo,hlohi,hrisk⟩ :=
    exists_fixed_box_BMminRiskAllR_positive_samples N hN hκ ha haq hA
      (fun d _hd => hlower d) hupper hcone
  exact ⟨lo,hi,hlo,hlohi,BMCyclicRiskRestriction.BMminRiskAllR_of_dominating
    n N hn hdom hlohi hrisk⟩

/-- Fully expanded original real-power risk statement, making the Gaussian
law, Loewner box, physical residual and all-r infimum literal in the result. -/
theorem bmApproximateFitting_original_formula_of_gaussian_cone
    (hGaussian : ProportionalGaussianConeInput) :
    ∀ n : ℕ → ℕ, (∀ d, 0 < n d) →
      limsup (fun d => (n d:ℝ≥0∞)/(d:ℝ≥0∞)^2) atTop < (1/4:ℝ≥0∞) →
      ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧
        ∀ r : ℝ, 1 ≤ r → r < 4/3 → ∀ ε > 0,
          Tendsto (fun d => (coordinateSampleLaw d (n d)).real
            {x | ε < sInf {t : ℝ | ∃ S ∈ BMRescaling.spectralBox d lo hi,
              t = (1/(n d:ℝ))*∑ i,
                |(BMRescaling.quadratic S (x i)-(d:ℝ))/Real.sqrt (d:ℝ)|^r}})
            atTop (nhds 0) := by
  intro n hn haspect
  obtain ⟨lo,hi,hlo,hlohi,hfit⟩ := bmApproximateFitting_of_gaussian_cone hGaussian n hn haspect
  exact ⟨lo,hi,hlo,hlohi,hfit⟩

end BMBoxRiskAssembly

#print axioms BMBoxRiskAssembly.bmApproximateFitting_of_gaussian_cone
#print axioms BMBoxRiskAssembly.bmApproximateFitting_original_formula_of_gaussian_cone
