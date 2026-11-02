import BMLoewnerOperator
import BMCoordinateResidual
import BMBoxParameters

/-!
# Conditional BM spectral-box to physical r=1 fitting theorem

This is an actual model bridge: Loewner constraints, the operator-norm cap,
Gaussian coordinates, residuals, sample counts, and trace rescaling are all
proved here or imported from concrete deterministic theorems.  The only
undischarged probabilistic input is exact Gaussian box/cone feasibility.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
open MeasureTheory Filter GaussianTensorMoments GaussianMixedNormHelpers
open BMUniformMoment BMQuadraticSpectral BMSymmetricFiniteUniversality
open BMGOEUniform BMApproximateL1Transfer BMGaussianFeasibilityTransfer
open BMSpectralBridge
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
local instance {d n : ℕ} : IsProbabilityMeasure (goeSampleLaw d n) := by
  unfold goeSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure
      (gaussianProductLaw (Fin (d*d))) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

/-- Exact equivalence of the literal Gaussian matrix feasibility event and
the symmetric-operator event consumed by the continuum transfer. -/
theorem actualBoxFeasible_iff (n d : ℕ) (lo hi : ℝ)
    (z : Fin n → Fin (d*d) → ℝ) :
    actualBoxFeasible n d lo hi z ↔
      ∃ T ∈ operatorBox d lo hi, ∀ i, goeRow (z i) T = 1 := by
  constructor
  · rintro ⟨S,hS,hrow⟩
    refine ⟨operatorOfBox S hS, operatorOfBox_mem S hS, ?_⟩
    intro i
    simpa only [goeRow_apply, matrixOf_operatorOfBox] using hrow i
  · rintro ⟨T,hT,hrow⟩
    exact ⟨matrixOf T,hT,hrow⟩

/-- The transfer parameter n means precisely n+1 actual iid Gaussian rows. -/
theorem gaussianFeasibilityFailure_eq_actual (d n : ℕ) (lo hi : ℝ) :
    gaussianFeasibilityFailure d n (operatorBox d lo hi) =
      (Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin (d*d)))).real
        {z | ¬actualBoxFeasible (n+1) d lo hi z} := by
  unfold gaussianFeasibilityFailure
  simp only [actualBoxFeasible_iff]

/-- Every successful centered-rank-one fit yields an actual physical fit,
with the exact fixed rescaled box and an explicit loss of 1/lo. -/
theorem fittingFeasible_of_centered {d n : ℕ} (hd : 0 < d) {lo hi ε : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (x : CoordinateSample d n)
    (hfit : ∃ T ∈ operatorBox d lo hi,
      (∑ i, |normalizedQuadratic T.val (sampleEuclideanEquiv d n x i)-1|)/(n:ℝ) < ε*lo) :
    fittingFeasible d n (lo/(hi+1)) (hi/lo) ε x := by
  obtain ⟨T,hT,hrisk⟩ := hfit
  refine ⟨BMRescaling.rescale (matrixOf T),
    BMRescaling.rescale_mem_fixed_box hd hlo hlohi hT, ?_⟩
  have hbound := BMRescaling.empiricalL1_rescale_le hd hlo hlohi hT x
  change fittingL1 (BMRescaling.rescale (matrixOf T)) x ≤ _ at hbound
  exact hbound.trans_lt ((div_lt_iff₀ hlo).mpr (by
    simpa only [centered_empiricalL1_eq] using hrisk))

/-- Exact comparison of actual failure probabilities on the two coordinate
realizations. No measurability or minimizer-selection hypothesis is added. -/
theorem fittingFailureProbability_le_l1FailureProbability {d n : ℕ}
    (hd : 0 < d) {lo hi ε : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi) :
    fittingFailureProbability d (n+1) (lo/(hi+1)) (hi/lo) ε ≤
      l1FailureProbability d n (operatorBox d lo hi) (ε*lo) := by
  let E : Set (Fin (n+1) → Euclid d) :=
    {x | ¬∃ T ∈ operatorBox d lo hi,
      (∑ i, |normalizedQuadratic T.val (x i)-1|)/((n+1:ℕ):ℝ) < ε*lo}
  change (coordinateSampleLaw d (n+1)).real _ ≤
    (BMUniformMoment.gaussianSampleLaw d (n+1)).real E
  rw [← coordinate_event_probability]
  refine measureReal_mono ?_
  intro x hx hfit
  exact hx (fittingFeasible_of_centered hd hlo hlohi x hfit)

/-- The exact Gaussian box failure premise implies physical approximate
fitting in a fixed positive Loewner box. All deterministic interfaces and
universality/L1 steps are discharged. -/
theorem physical_fitting_of_gaussian_box_probability
    (n : ℕ → ℕ) {lo hi a A : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (ha : 0 < a) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
        {z | ¬actualBoxFeasible (n d+1) d lo hi z}) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => fittingFailureProbability d (n d+1)
      (lo/(hi+1)) (hi/lo) ε) atTop (nhds 0) := by
  have hGaussian' : Tendsto
      (fun d => gaussianFeasibilityFailure d (n d) (operatorBox d lo hi))
      atTop (nhds 0) := by
    simpa only [gaussianFeasibilityFailure_eq_actual] using hGaussian
  have hL1 := approximate_L1_of_gaussian_feasibility_probability n
    (fun d => operatorBox d lo hi) (fun d => operatorBox_nonempty d hlo hlohi)
    ha hA (hlo.trans_le hlohi)
    (fun d T hT => operatorBox_norm_le hlo.le hlohi hT)
    hlow hhigh hGaussian' (ε*lo) (mul_pos hε hlo)
  apply squeeze_zero' (Eventually.of_forall fun d => measureReal_nonneg) ?_ hL1
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  exact fittingFailureProbability_le_l1FailureProbability hd hlo hlohi

/-- Literal original r=1 infimum-risk theorem, conditional only on genuine
Gaussian box feasibility and the stated proportional sample window. -/
theorem minRiskOne_of_gaussian_box_probability
    (n : ℕ → ℕ) {lo hi a A : ℝ} (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (ha : 0 < a) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
        {z | ¬actualBoxFeasible (n d+1) d lo hi z}) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => (coordinateSampleLaw d (n d+1)).real
      {x | ε < minFittingRiskOne d (n d+1) x (lo/(hi+1)) (hi/lo)})
      atTop (nhds 0) :=
  minRisk_tendsto_zero_of_fitting_failure (fun d => n d+1) _ _ ε
    (physical_fitting_of_gaussian_box_probability n hlo hlohi ha hA hlow hhigh hGaussian ε hε)

/-- Enlarging the cone radius is deterministic and loses no good samples. -/
theorem enlarged_cone_failure_tendsto_zero (n : ℕ → ℕ) {κ R : ℝ}
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d) d κ R z}) atTop (nhds 0)) :
    Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d) d κ (max R 1) z}) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hcone
  intro d
  refine measureReal_mono ?_
  intro z hz hc
  exact hz (actualConeFeasible_mono_radius (le_max_left R 1) hc)

/-- Full conditional bridge from the concrete Gaussian conditioned-cone event
to the actual physical fitting event.  The remaining Gordon feasibility
premise is intentionally explicit; this is not a proof of full BM. -/
theorem physical_fitting_of_gaussian_cone_probability
    (n : ℕ → ℕ) {κ R a A : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a)
    (haquarter : a < 1/4) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d+1) d κ R z}) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => fittingFailureProbability d (n d+1)
      ((Real.sqrt a/(32*κ))/(κ*max R 1+1))
      ((κ*max R 1)/(Real.sqrt a/(32*κ))) ε) atTop (nhds 0) := by
  have hp := enlarged_box_parameters (R := R) hκ ha haquarter
  have hκpos : 0 < κ := lt_of_lt_of_le (by norm_num) hκ
  have he : ∀ᶠ d : ℕ in atTop, a*(d:ℝ)^2 ≤ (n d+1 : ℕ) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    exact hlow d hd
  have hbox := actual_box_failure_tendsto_zero (fun d => n d+1) hκpos
    (le_trans (by norm_num) (le_max_right R 1)) ha he
    (enlarged_cone_failure_tendsto_zero (fun d => n d+1) hcone)
  exact physical_fitting_of_gaussian_box_probability n hp.1 (hp.2.1.trans hp.2.2.1)
    ha hA hlow hhigh hbox ε hε

/-- Existential positive fixed endpoints and the genuine original r=1
infimum-risk statement. The only Gaussian analytic input is hcone. -/
theorem exists_fixed_box_minRiskOne_of_gaussian_cone_probability
    (n : ℕ → ℕ) {κ R a A : ℝ} (hκ : 1 ≤ κ) (ha : 0 < a)
    (haquarter : a < 1/4) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d+1) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d+1) d κ R z}) atTop (nhds 0)) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ ε > 0,
      Tendsto (fun d => (coordinateSampleLaw d (n d+1)).real
        {x | ε < minFittingRiskOne d (n d+1) x lo hi}) atTop (nhds 0) := by
  have hp := enlarged_box_parameters (R := R) hκ ha haquarter
  have hfixed := BMRescaling.fixed_endpoints hp.1 (hp.2.1.trans hp.2.2.1)
  refine ⟨_,_,hfixed.1,hfixed.2,?_⟩
  intro ε hε
  exact minRisk_tendsto_zero_of_fitting_failure (fun d => n d+1) _ _ ε
    (physical_fitting_of_gaussian_cone_probability n hκ ha haquarter hA hlow hhigh hcone ε hε)

/-- The same concrete r=1 theorem using the literal positive sample count n d,
with the transfer's internal n+1 convention discharged by n d-1. -/
theorem exists_fixed_box_minRiskOne_positive_samples
    (n : ℕ → ℕ) (hn : ∀ d, 0 < n d) {κ R a A : ℝ}
    (hκ : 1 ≤ κ) (ha : 0 < a) (haquarter : a < 1/4) (hA : 1 ≤ A)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d : ℝ))
    (hhigh : ∀ d : ℕ, 0 < d → (n d : ℝ) ≤ A*(d:ℝ)^2)
    (hcone : Tendsto (fun d => (Measure.pi
      (fun _ : Fin (n d) => gaussianProductLaw (Fin (d*d)))).real
      {z | ¬actualConeFeasible (n d) d κ R z}) atTop (nhds 0)) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ ε > 0,
      Tendsto (fun d => (coordinateSampleLaw d (n d)).real
        {x | ε < minFittingRiskOne d (n d) x lo hi}) atTop (nhds 0) := by
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
  have hout := exists_fixed_box_minRiskOne_of_gaussian_cone_probability
    (fun d => n d-1) hκ ha haquarter hA hlow' hhigh' hcone'
  exact hcount ▸ hout

end BMBoxRiskAssembly
