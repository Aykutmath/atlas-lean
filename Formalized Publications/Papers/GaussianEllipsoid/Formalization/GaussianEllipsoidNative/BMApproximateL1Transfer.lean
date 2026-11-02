import BMContinuumUniversality
import BMBoundedRiskToL1
import GaussianUniformResidualMoment

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Filter GaussianMixedNormHelpers BMUniformMoment BMQuadraticSpectral
open BMContinuumExpectations BMNetGroundExtension BMExpectationLimits BMContinuumLimitTools
open scoped BigOperators BoundedContinuousFunction

namespace BMApproximateL1Transfer
local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (gaussianSampleLaw d n) := by
  unfold gaussianSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (euclideanGaussianLaw (Fin d)) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

def rationalData := BMRationalLossData.unitData2 1 (by norm_num)

/-- The actual probability of failing to find an L1-accurate state inside the
original constraint set. Strict success <ε is stronger than weak ≤ε. -/
def l1FailureProbability (d n : ℕ) (B : Set (SymOp d)) (ε : ℝ) : ℝ :=
  (gaussianSampleLaw d (n+1)).real
    {x | ¬∃ T ∈ B, (∑ i, |normalizedQuadratic T.val (x i)-1|)/((n+1:ℕ):ℝ) < ε}

/-- Specialized BM r=1 transfer from a zero-risk Gaussian model to the original
centered rank-one measurements. The only remaining analytic hypothesis is the
Gaussian-side zero-risk conclusion; universality, uniform integrability and
the bounded-smooth-loss-to-L1 passage are all discharged by actual theorems. -/
theorem approximate_L1_of_gaussian_ground_mean_zero
    (n : ℕ → ℕ) (B : (d : ℕ) → Set (SymOp d)) (hB : ∀ d, (B d).Nonempty)
    {a A R : ℝ} (ha : 0 < a) (hA : 1 ≤ A) (hR : 0 < R)
    (hbound : ∀ d T, T ∈ B d → ‖T‖ ≤ R)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => goeContinuumExpectation rationalData d (n d) (B d)) atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => l1FailureProbability d (n d) (B d) ε) atTop (nhds 0) := by
  have hφnonneg : ∀ u, 0 ≤ rationalData.potential u :=
    fun u => BMClippedL1Bridge.smoothLoss_nonneg _
  have huniv := BMContinuumUniversality.continuum_ground_expectation_universality
    rationalData hφnonneg n B hB ha hA hR.le hbound hlow hhigh
  have hmean := tendsto_zero_of_abs_expectation_comparison _ _ huniv hGaussian
  obtain ⟨K,hK,hMoment⟩ := exists_uniform_fractional_residual_constant a A R ha hA hR
  obtain ⟨τ,hτ,hTransfer⟩ := BMBoundedRiskToL1.exists_L1_failure_probability_bound hK.le hε ha
  have htail := exponential_sample_decay n ha hlow
  apply squeeze_zero' (Eventually.of_forall fun d => ENNReal.toReal_nonneg) ?_
    (by simpa only [zero_div,add_zero] using htail.add (hmean.div_const τ))
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  obtain ⟨good,hgood,hmoment,hbad⟩ := hMoment d (n d+1) hd (Nat.succ_pos _) (hlow d hd) (hhigh d hd)
  let y := fun (x : Fin (n d+1) → Euclid d) (T : SymOp d) (i : Fin (n d+1)) => normalizedQuadratic T.val (x i)
  have hm : ∀ x ∈ good, ∀ T ∈ B d, (∑ i, |y x T i-1|^((6:ℝ)/5)) ≤ K*(n d+1 : ℕ) := by
    intro x hx T hT
    exact hmoment x hx T.val T.property (hbound d T hT)
  have hi : Integrable (fun x => BMBoundedRiskToL1.boundedGround (B d) d (n d+1) (y x))
      (gaussianSampleLaw d (n d+1)) := by
    exact integrable_quadratic_energy_ground (gaussianSampleLaw d (n d+1))
      BMRationalLossData.potential BMRationalLossData.potential.continuous
      (fun u => BMRationalLossData.potential.norm_coe_le_norm u) (B d) (hB d)
  have hp := hTransfer (Fin (n d+1) → Euclid d) (SymOp d) (gaussianSampleLaw d (n d+1))
    (B d) (hB d) d (n d+1) hd (Nat.succ_pos _) (hlow d hd) y good hm hi
  change l1FailureProbability d (n d) (B d) ε ≤
    (gaussianSampleLaw d (n d+1)).real goodᶜ + quadraticContinuumExpectation rationalData d (n d) (B d)/τ at hp
  exact hp.trans (add_le_add_left hbad _)

#print axioms approximate_L1_of_gaussian_ground_mean_zero
end BMApproximateL1Transfer
