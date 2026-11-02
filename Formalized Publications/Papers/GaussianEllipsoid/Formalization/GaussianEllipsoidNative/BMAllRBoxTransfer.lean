import BMPhysicalAllR
import BMAllRProbability

/-!
# Gaussian conditioned-cone feasibility implies the full BM real-power risk interface

The exponent quantifier is outside the convergence statement and inside one
fixed positive spectral box: all 1 ≤ r < 4/3 share exactly the same endpoints.
The actual Gaussian feasibility premise remains explicit.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open BMUniformMoment BMQuadraticSpectral BMSymmetricFiniteUniversality
open BMGOEUniform BMGaussianFeasibilityTransfer BMAllRTransfer BMSpectralBridge
open scoped BigOperators

namespace BMBoxRiskAssembly

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (coordinateSampleLaw d n) := by
  unfold coordinateSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianProductLaw (Fin d)) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

/-- Physical r-fitting failure is bounded by actual centered rank-one failure
at tolerance ε*lo^r, on the exact same iid source. -/
theorem fittingFailureProbabilityR_le_lrFailureProbability {d n : ℕ}
    (hd : 0 < d) {lo hi r ε : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) (hr : 0 ≤ r) :
    fittingFailureProbabilityR d (n+1) (lo/(hi+1)) (hi/lo) r ε ≤
      lrFailureProbability d n (operatorBox d lo hi) r (ε*lo^r) := by
  let E : Set (Fin (n+1) → Euclid d) :=
    {x | ¬∃ T ∈ operatorBox d lo hi,
      (∑ i, |normalizedQuadratic T.val (x i)-1|^r)/((n+1:ℕ):ℝ) < ε*lo^r}
  change (coordinateSampleLaw d (n+1)).real _ ≤
    (BMUniformMoment.gaussianSampleLaw d (n+1)).real E
  rw [← coordinate_event_probability]
  refine measureReal_mono ?_
  intro x hx hfit
  exact hx (fittingFeasibleR_of_centered hd hlo hlohi hr x hfit)

/-- Concrete Gaussian box feasibility implies every physical r-loss limit,
without any universality or uniform-moment hypothesis remaining. -/
theorem physical_fitting_allR_of_gaussian_box_probability
    (n : ℕ → ℕ) {lo hi a A : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (ha : 0 < a) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
        {z | ¬actualBoxFeasible (n d+1) d lo hi z}) atTop (nhds 0))
    {r : ℝ} (hr : 1 ≤ r) (hrq : r < 4/3) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => fittingFailureProbabilityR d (n d+1)
      (lo/(hi+1)) (hi/lo) r ε) atTop (nhds 0) := by
  have hGaussian' : Tendsto
      (fun d => gaussianFeasibilityFailure d (n d) (operatorBox d lo hi))
      atTop (nhds 0) := by
    simpa only [gaussianFeasibilityFailure_eq_actual] using hGaussian
  have hLr := approximate_Lr_of_gaussian_feasibility_probability n
    (fun d => operatorBox d lo hi) (fun d => operatorBox_nonempty d hlo hlohi)
    ha hA (hlo.trans_le hlohi)
    (fun d T hT => operatorBox_norm_le hlo.le hlohi hT)
    hlow hhigh hGaussian' hr hrq (ε*lo^r) (mul_pos hε (Real.rpow_pos_of_pos hlo r))
  apply squeeze_zero' (Eventually.of_forall fun d => measureReal_nonneg) ?_ hLr
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  exact fittingFailureProbabilityR_le_lrFailureProbability hd hlo hlohi (by linarith)

/-- Exact all-r BM infimum-risk interface, in one fixed rescaled positive box,
conditional only on actual Gaussian box feasibility and sample-window bounds. -/
theorem BMminRiskAllR_of_gaussian_box_probability
    (n : ℕ → ℕ) {lo hi a A : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (ha : 0 < a) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
        {z | ¬actualBoxFeasible (n d+1) d lo hi z}) atTop (nhds 0)) :
    BMminRiskAllR (fun d => n d+1) (lo/(hi+1)) (hi/lo) := by
  intro r hr hrq ε hε
  exact minRiskR_tendsto_zero_of_fitting_failure (fun d => n d+1) _ _ r ε
    (physical_fitting_allR_of_gaussian_box_probability n hlo hlohi ha hA hlow hhigh
      hGaussian hr hrq ε hε)

/-- Explicit exponent-independent endpoints for the full real-power risk
range, from the actual Gaussian conditioned-cone failure premise. -/
theorem BMminRiskAllR_of_gaussian_cone_probability
    (n : ℕ → ℕ) {κ R a A : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a)
    (haquarter : a < 1/4) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d+1) d κ R z}) atTop (nhds 0)) :
    BMminRiskAllR (fun d => n d+1)
      ((Real.sqrt a/(32*κ))/(κ*max R 1+1))
      ((κ*max R 1)/(Real.sqrt a/(32*κ))) := by
  have hp := enlarged_box_parameters (R := R) hκ ha haquarter
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have he : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ (n d+1 : ℕ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    exact hlow d hd
  have hbox := actual_box_failure_tendsto_zero (fun d => n d+1) hκpos
    (le_trans (by norm_num) (le_max_right R 1)) ha he
    (enlarged_cone_failure_tendsto_zero (fun d => n d+1) hcone)
  exact BMminRiskAllR_of_gaussian_box_probability n hp.1 (hp.2.1.trans hp.2.2.1)
    ha hA hlow hhigh hbox

/-- One positive fixed box works for all 1 ≤ r < 4/3 simultaneously in the
original BM quantifier order. Gordon feasibility remains the explicit input. -/
theorem exists_fixed_box_BMminRiskAllR_of_gaussian_cone_probability
    (n : ℕ → ℕ) {κ R a A : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a)
    (haquarter : a < 1/4) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d+1) d κ R z}) atTop (nhds 0)) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMminRiskAllR (fun d => n d+1) lo hi := by
  have hp := enlarged_box_parameters (R := R) hκ ha haquarter
  have hfixed := BMRescaling.fixed_endpoints hp.1 (hp.2.1.trans hp.2.2.1)
  exact ⟨_,_,hfixed.1,hfixed.2,
    BMminRiskAllR_of_gaussian_cone_probability n hκ ha haquarter hA hlow hhigh hcone⟩

/-- Literal positive sample counts, with the transfer's n+1 convention proved
away. The fixed box is still independent of the exponent r. -/
theorem exists_fixed_box_BMminRiskAllR_positive_samples
    (n : ℕ → ℕ) (hn : ∀ d, 0 < n d) {κ R a A : ℝ}
    (hκ : 1 ≤ κ) (ha : 0 < a) (haquarter : a < 1/4) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d : ℝ))
    (hhigh : ∀ d : ℕ, 0 < d → (n d : ℝ) ≤ A*(d:ℝ)^2)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d) d κ R z}) atTop (nhds 0)) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ BMminRiskAllR n lo hi := by
  have hsucc (d : ℕ) : n d-1+1 = n d := Nat.sub_add_cancel (hn d)
  have hcount : (fun d => n d-1+1) = n := funext hsucc
  have hlow' : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d-1+1 : ℕ) := by
    simpa only [hsucc] using hlow
  have hhigh' : ∀ d : ℕ, 0 < d → ((n d-1+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2 := by
    simpa only [hsucc] using hhigh
  have hcone' : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d-1+1) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d-1+1) d κ R z}) atTop (nhds 0) := by
    exact hcount.symm ▸ hcone
  have hout := exists_fixed_box_BMminRiskAllR_of_gaussian_cone_probability
    (fun d => n d-1) hκ ha haquarter hA hlow' hhigh' hcone'
  exact hcount ▸ hout

end BMBoxRiskAssembly
