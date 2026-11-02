import BMApproximateL1Transfer
import BMGOENetGroundExtension

/-!
# Exact Gaussian feasibility implies original-model approximate L1 feasibility

The Gaussian hypothesis is the actual outer probability of failure of the
finite system of GOE row equations on the original constraint set.  No
measurability of that existential feasibility event is assumed.  The measurable
positive-ground event is contained in the failure event and suffices to control
the bounded loss expectation.

The exact Gaussian feasibility limit remains an explicit analytic hypothesis;
this module proves only its deterministic and probabilistic transfer.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Filter GaussianMixedNormHelpers BMUniformMoment BMQuadraticSpectral
open BMContinuumExpectations BMNetGroundExtension BMApproximateL1Transfer BMGOEUniform
open BMGOENetGroundExtension
open scoped BigOperators BoundedContinuousFunction

namespace BMGaussianFeasibilityTransfer

local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (goeSampleLaw d n) := by
  unfold goeSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure
      (GaussianTensorMoments.gaussianProductLaw (Fin (d*d))) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

/-- Actual outer probability of failure of exact Gaussian feasibility on B. -/
def gaussianFeasibilityFailure (d n : ℕ) (B : Set (SymOp d)) : ℝ :=
  (goeSampleLaw d (n+1)).real
    {z | ¬∃ T ∈ B, ∀ i : Fin (n+1), goeRow (z i) T = 1}

/-- The actual rational-loss continuum ground expectation is nonnegative. -/
theorem goe_ground_expectation_nonneg (d n : ℕ) (B : Set (SymOp d))
    (hB : B.Nonempty) :
    0 ≤ goeContinuumExpectation rationalData d n B := by
  apply integral_nonneg
  intro z
  apply le_csInf (hB.image _)
  rintro _ ⟨T, hT, rfl⟩
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => BMClippedL1Bridge.smoothLoss_nonneg _)
    (sq_nonneg _)

/-- Exact Gaussian feasibility makes the ground loss zero.  Since the rational
loss is bounded by one, failure probability controls the actual expectation by
the sample-to-dimension-squared ratio.  B need not be measurable or compact. -/
theorem goe_ground_expectation_le_feasibility_failure
    (d n : ℕ) (hd : 0 < d) (B : Set (SymOp d)) (hB : B.Nonempty)
    {A : ℝ} (hhigh : ((n+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2) :
    goeContinuumExpectation rationalData d n B ≤
      A * gaussianFeasibilityFailure d n B := by
  classical
  let E := fun (z : Fin (n+1) → (Fin (d*d) → ℝ)) =>
    energy d (fun i => goeRow (z i)) rationalData.potential
  let g := fun z => ground B (E z)
  let μ := goeSampleLaw d (n+1)
  have hd2 : 0 < (d:ℝ)^2 := by positivity
  have hA : 0 ≤ A := by
    have hn : 0 < ((n+1 : ℕ):ℝ) := by positivity
    nlinarith
  have hφnonneg : ∀ u, 0 ≤ rationalData.potential u :=
    fun u => BMClippedL1Bridge.smoothLoss_nonneg _
  have hφbound : ∀ u, |rationalData.potential u| ≤ 1 :=
    BMRationalLossData.shifted_abs_le_one
  have hφone : rationalData.potential 1 = 0 := by
    change (1 - 1 : ℝ)^2 / (1 + (1 - 1 : ℝ)^2) = 0
    norm_num
  have hEnonneg (z) (T : SymOp d) : 0 ≤ E z T :=
    div_nonneg (Finset.sum_nonneg fun i _ => hφnonneg _) (sq_nonneg _)
  have hbelow (z) : BddBelow ((E z) '' B) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    exact hEnonneg z T
  have hcont (T : SymOp d) : Continuous
      (fun z : Fin (n+1) → (Fin (d*d) → ℝ) => E z T) := by
    exact continuous_energy_in_rows (V := SymOp d) (ι := Fin (n+1))
      (Ω := Fin (n+1) → (Fin (d*d) → ℝ)) d (fun z i => goeRow (z i))
      rationalData.potential rationalData.potential.continuous
      (fun i T => continuous_goeRow_sample i T) T
  have hmeas : Measurable g :=
    measurable_ground_of_continuous (V := SymOp d)
      (Ω := Fin (n+1) → (Fin (d*d) → ℝ)) B E (fun T _ => hcont T) hbelow
  have hi : Integrable g μ :=
    integrable_goe_energy_ground μ rationalData.potential
      rationalData.potential.continuous hφbound B hB
  have hbound (z) : g z ≤ A := by
    obtain ⟨T, hT⟩ := hB
    have hg : g z ≤ E z T := csInf_le (hbelow z) ⟨T, hT, rfl⟩
    have he := abs_energy_le d (fun i => goeRow (z i))
      rationalData.potential hφbound T
    simp only [Fintype.card_fin, mul_one] at he
    exact hg.trans ((le_abs_self _).trans
      (he.trans ((div_le_iff₀ hd2).2 hhigh)))
  let positiveGround : Set (Fin (n+1) → (Fin (d*d) → ℝ)) := {z | 0 < g z}
  have hpositive : MeasurableSet positiveGround :=
    measurableSet_lt measurable_const hmeas
  have hsub : positiveGround ⊆
      {z | ¬∃ T ∈ B, ∀ i : Fin (n+1), goeRow (z i) T = 1} := by
    intro z hz hfeasible
    obtain ⟨T, hT, hrow⟩ := hfeasible
    have hg : g z ≤ E z T := csInf_le (hbelow z) ⟨T, hT, rfl⟩
    have he : E z T = 0 := by
      simp only [E, energy, hrow, hφone, Finset.sum_const_zero, zero_div]
    have hp : 0 < g z := hz
    linarith
  have hpoint (z) : g z ≤ positiveGround.indicator (fun _ => A) z := by
    by_cases hz : z ∈ positiveGround
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · have hn : ¬ 0 < g z := hz
      simpa only [Set.indicator_of_notMem hz] using le_of_not_gt hn
  have hint := integral_mono hi ((integrable_const A).indicator hpositive) hpoint
  rw [integral_indicator_const _ hpositive, smul_eq_mul] at hint
  change (∫ z, g z ∂μ) ≤ A * μ.real
    {z | ¬∃ T ∈ B, ∀ i : Fin (n+1), goeRow (z i) T = 1}
  calc
    (∫ z, g z ∂μ) ≤ μ.real positiveGround * A := hint
    _ ≤ μ.real {z | ¬∃ T ∈ B, ∀ i : Fin (n+1), goeRow (z i) T = 1} * A :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsub) hA
    _ = _ := mul_comm _ _

/-- Gaussian exact-feasibility probabilities discharge the zero-ground-mean
hypothesis in the already proved universality and bounded-loss/L1 transfer.
The conclusion concerns the same arbitrary nonempty bounded constraint sets. -/
theorem approximate_L1_of_gaussian_feasibility_probability
    (n : ℕ → ℕ) (B : (d : ℕ) → Set (SymOp d)) (hB : ∀ d, (B d).Nonempty)
    {a A R : ℝ} (ha : 0 < a) (hA : 1 ≤ A) (hR : 0 < R)
    (hbound : ∀ d T, T ∈ B d → ‖T‖ ≤ R)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2)
    (hGaussian : Tendsto (fun d => gaussianFeasibilityFailure d (n d) (B d))
      atTop (nhds 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => l1FailureProbability d (n d) (B d) ε) atTop (nhds 0) := by
  apply approximate_L1_of_gaussian_ground_mean_zero n B hB ha hA hR hbound hlow hhigh
    ?_ ε hε
  apply squeeze_zero' (Eventually.of_forall fun d =>
    goe_ground_expectation_nonneg d (n d) (B d) (hB d)) ?_
    (by simpa only [mul_zero] using hGaussian.const_mul A)
  filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
  exact goe_ground_expectation_le_feasibility_failure d (n d) hd (B d) (hB d)
    (hhigh d hd)

/-- Strict original-model L1 success is open in the Gaussian sample, even for
an arbitrary constraint set.  Consequently its failure event is closed. -/
theorem isClosed_l1_failure_event (d n : ℕ) (B : Set (SymOp d)) (ε : ℝ) :
    IsClosed {x : Fin (n+1) → Euclid d |
      ¬∃ T ∈ B, (∑ i, |normalizedQuadratic T.val (x i)-1|)/((n+1:ℕ):ℝ) < ε} := by
  have hc (T : SymOp d) : Continuous (fun x : Fin (n+1) → Euclid d =>
      (∑ i, |normalizedQuadratic T.val (x i)-1|)/((n+1:ℕ):ℝ)) := by
    exact (continuous_finset_sum _ (fun i _ =>
      (((continuous_normalizedQuadratic T.val).comp (continuous_apply i)).sub
        continuous_const).abs)).div_const _
  have hclosed := isClosed_iInter (fun T : SymOp d =>
    isClosed_iInter (fun _hT : T ∈ B => isClosed_le (continuous_const :
      Continuous (fun _ : Fin (n+1) → Euclid d => ε)) (hc T)))
  convert hclosed using 1
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq, not_exists, not_and, not_lt]

/-- The probability in `l1FailureProbability` is the probability of an actual
measurable event, without any regularity assumption on the constraint set. -/
theorem measurableSet_l1_failure_event (d n : ℕ) (B : Set (SymOp d)) (ε : ℝ) :
    MeasurableSet {x : Fin (n+1) → Euclid d |
      ¬∃ T ∈ B, (∑ i, |normalizedQuadratic T.val (x i)-1|)/((n+1:ℕ):ℝ) < ε} :=
  (isClosed_l1_failure_event d n B ε).measurableSet

#print axioms goe_ground_expectation_nonneg
#print axioms goe_ground_expectation_le_feasibility_failure
#print axioms approximate_L1_of_gaussian_feasibility_probability
#print axioms isClosed_l1_failure_event
#print axioms measurableSet_l1_failure_event
end BMGaussianFeasibilityTransfer
