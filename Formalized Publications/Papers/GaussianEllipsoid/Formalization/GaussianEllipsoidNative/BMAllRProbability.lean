import BMAllRBoundedRisk
import BMGaussianFeasibilityTransfer
import GaussianUniformFourThirdResidual

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Filter GaussianMixedNormHelpers BMUniformMoment BMQuadraticSpectral
open BMContinuumExpectations BMNetGroundExtension BMExpectationLimits BMContinuumLimitTools
open scoped BigOperators BoundedContinuousFunction

namespace BMAllRTransfer
local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (gaussianSampleLaw d n) := by
  unfold gaussianSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (euclideanGaussianLaw (Fin d)) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

open BMApproximateL1Transfer BMBoundedRiskToL1 BMGaussianFeasibilityTransfer

/-- The actual probability of failing to find an Lr-accurate state inside the
original constraint set. Strict success <ε is stronger than weak ≤ε. -/
def lrFailureProbability (d n : ℕ) (B : Set (SymOp d)) (r ε : ℝ) : ℝ :=
  (gaussianSampleLaw d (n+1)).real
    {x | ¬∃ T ∈ B, (∑ i, |normalizedQuadratic T.val (x i)-1|^r)/((n+1:ℕ):ℝ) < ε}

/-- BM transfer for every 1 ≤ r < 4/3 from a zero-risk Gaussian model to the original
centered rank-one measurements. The only remaining analytic hypothesis is the
Gaussian-side zero-risk conclusion; universality, uniform integrability and
the bounded-smooth-loss-to-Lr passage are all discharged by actual theorems. -/
theorem approximate_Lr_of_gaussian_ground_mean_zero
    (n : ℕ → ℕ) (B : (d : ℕ) → Set (SymOp d)) (hB : ∀ d, (B d).Nonempty)
    {a A R : ℝ} (ha : 0 < a) (hA : 1 ≤ A) (hR : 0 < R)
    (hbound : ∀ d T, T ∈ B d → ‖T‖ ≤ R)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => goeContinuumExpectation rationalData d (n d) (B d)) atTop (nhds 0))
    {r : ℝ} (hr : 1 ≤ r) (hrq : r < (4:ℝ)/3) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => lrFailureProbability d (n d) (B d) r ε) atTop (nhds 0) := by
  have hφnonneg : ∀ u, 0 ≤ rationalData.potential u :=
    fun u => BMClippedL1Bridge.smoothLoss_nonneg _
  have huniv := BMContinuumUniversality.continuum_ground_expectation_universality
    rationalData hφnonneg n B hB ha hA hR.le hbound hlow hhigh
  have hmean := tendsto_zero_of_abs_expectation_comparison _ _ huniv hGaussian
  obtain ⟨K,hK,hMoment⟩ := BMFourThirdMoment.exists_uniform_fractional_residual_constant a A R ha hA hR
  obtain ⟨τ,hτ,hTransfer⟩ := BMAllRTransfer.exists_Lr_failure_probability_bound hr hrq hK.le hε ha
  have htail := exponential_sample_decay n ha hlow
  apply squeeze_zero' (Eventually.of_forall fun d => ENNReal.toReal_nonneg) ?_
    (by simpa only [zero_div,add_zero] using htail.add (hmean.div_const τ))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  obtain ⟨good,hgood,hmoment,hbad⟩ := hMoment d (n d+1) hd (Nat.succ_pos _) (hlow d hd) (hhigh d hd)
  let y := fun (x : Fin (n d+1) → Euclid d) (T : SymOp d) (i : Fin (n d+1)) => normalizedQuadratic T.val (x i)
  have hm : ∀ x ∈ good, ∀ T ∈ B d, (∑ i, |y x T i-1|^((4:ℝ)/3)) ≤ K*(n d+1 : ℕ) := by
    intro x hx T hT
    exact hmoment x hx T.val T.property (hbound d T hT)
  have hi : Integrable (fun x => BMBoundedRiskToL1.boundedGround (B d) d (n d+1) (y x))
      (gaussianSampleLaw d (n d+1)) := by
    exact integrable_quadratic_energy_ground (gaussianSampleLaw d (n d+1))
      BMRationalLossData.potential BMRationalLossData.potential.continuous
      (fun u => BMRationalLossData.potential.norm_coe_le_norm u) (B d) (hB d)
  have hp := hTransfer (Fin (n d+1) → Euclid d) (SymOp d) (gaussianSampleLaw d (n d+1))
    (B d) (hB d) d (n d+1) hd (Nat.succ_pos _) (hlow d hd) y good hm hi
  change lrFailureProbability d (n d) (B d) r ε ≤
    (gaussianSampleLaw d (n d+1)).real goodᶜ + quadraticContinuumExpectation rationalData d (n d) (B d)/τ at hp
  exact hp.trans (add_le_add_left hbad _)

/-- Exact Gaussian feasibility transfers to arbitrary bounded, nonempty original
constraint sets for every 1 ≤ r < 4/3. The only analytic hypothesis is the
actual Gaussian feasibility-failure probability limit; all moment estimates,
integrability and universality inputs are discharged. -/
theorem approximate_Lr_of_gaussian_feasibility_probability
    (n : ℕ → ℕ) (B : (d : ℕ) → Set (SymOp d)) (hB : ∀ d, (B d).Nonempty)
    {a A R : ℝ} (ha : 0 < a) (hA : 1 ≤ A) (hR : 0 < R)
    (hbound : ∀ d T, T ∈ B d → ‖T‖ ≤ R)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => gaussianFeasibilityFailure d (n d) (B d))
      atTop (nhds 0))
    {r : ℝ} (hr : 1 ≤ r) (hrq : r < (4:ℝ)/3) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => lrFailureProbability d (n d) (B d) r ε) atTop (nhds 0) := by
  apply approximate_Lr_of_gaussian_ground_mean_zero n B hB ha hA hR hbound hlow hhigh
    ?_ hr hrq ε hε
  apply squeeze_zero' (Eventually.of_forall fun d =>
    goe_ground_expectation_nonneg d (n d) (B d) (hB d)) ?_
    (by simpa only [mul_zero] using hGaussian.const_mul A)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  exact goe_ground_expectation_le_feasibility_failure d (n d) hd (B d) (hB d)
    (hhigh d hd)

/-- Strict original-model Lr success is open for every nonnegative exponent,
even on an arbitrary constraint set. Hence failure is closed. -/
theorem isClosed_lr_failure_event (d n : ℕ) (B : Set (SymOp d))
    {r : ℝ} (hr : 0 ≤ r) (ε : ℝ) :
    IsClosed {x : Fin (n+1) → Euclid d |
      ¬∃ T ∈ B, (∑ i, |normalizedQuadratic T.val (x i)-1|^r)/((n+1:ℕ):ℝ) < ε} := by
  have hc (T : SymOp d) : Continuous (fun x : Fin (n+1) → Euclid d =>
      (∑ i, |normalizedQuadratic T.val (x i)-1|^r)/((n+1:ℕ):ℝ)) := by
    exact (continuous_finset_sum _ (fun i _ =>
      (Real.continuous_rpow_const hr).comp
        ((((continuous_normalizedQuadratic T.val).comp (continuous_apply i)).sub
          continuous_const).abs))).div_const _
  have hclosed := isClosed_iInter (fun T : SymOp d =>
    isClosed_iInter (fun _hT : T ∈ B => isClosed_le (continuous_const :
      Continuous (fun _ : Fin (n+1) → Euclid d => ε)) (hc T)))
  convert hclosed using 1
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq, not_exists, not_and, not_lt]

/-- The probability in lrFailureProbability is of an actual measurable event;
no regularity assumption on the constraint set is needed. -/
theorem measurableSet_lr_failure_event (d n : ℕ) (B : Set (SymOp d))
    {r : ℝ} (hr : 0 ≤ r) (ε : ℝ) :
    MeasurableSet {x : Fin (n+1) → Euclid d |
      ¬∃ T ∈ B, (∑ i, |normalizedQuadratic T.val (x i)-1|^r)/((n+1:ℕ):ℝ) < ε} :=
  (isClosed_lr_failure_event d n B hr ε).measurableSet

#print axioms approximate_Lr_of_gaussian_ground_mean_zero
#print axioms approximate_Lr_of_gaussian_feasibility_probability
#print axioms isClosed_lr_failure_event
#print axioms measurableSet_lr_failure_event
end BMAllRTransfer
