import BMContinuumExpectations
import BMContinuumLimitTools
import BMGOENetGroundExtension

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMFiniteGibbsTest BMFiniteGibbsHessian
open BMFiniteUniversality BMUniformMoment BMGOEUniform BMSymmetricFiniteUniversality
open BMNetGroundExtension BMGOENetGroundExtension BMContinuumExpectations BMContinuumLimitTools
open GaussianMixedNormHelpers Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMContinuumUniversality
local instance {d : ℕ} : DecidableEq (SymOp d) := Classical.decEq _
local instance {d : ℕ} : NormedAddCommGroup (SymOp d) :=
  Submodule.normedAddCommGroup (symmetricOperators d)
local instance {d : ℕ} : NormedSpace ℝ (SymOp d) :=
  Submodule.normedSpace (symmetricOperators d)
local instance {d n : ℕ} : IsProbabilityMeasure (gaussianSampleLaw d n) := by
  unfold gaussianSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (euclideanGaussianLaw (Fin d)) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _
local instance {d n : ℕ} : IsProbabilityMeasure (goeSampleLaw d n) := by
  unfold goeSampleLaw
  letI : ∀ _i : Fin n, IsProbabilityMeasure (gaussianProductLaw (Fin (d*d))) := fun _ => inferInstance
  letI : ∀ _i : Fin n, SigmaFinite (gaussianProductLaw (Fin (d*d))) := fun _ => inferInstance
  exact Measure.pi.instIsProbabilityMeasure _

/-- Expectation-only ground-state universality on arbitrary nonempty
operator-bounded constraint sets. Every one-row comparison, product-law
replacement, finite soft minimum, internal net, uniform empirical bound, and
integrability obligation is discharged by a proved theorem. No abstract
universality or empirical-process assumption appears in this statement. -/
theorem continuum_ground_expectation_universality
    (P : Data2 Unit) (hφnonneg : ∀ u, 0 ≤ P.potential u)
    (n : ℕ → ℕ) (B : (d : ℕ) → Set (SymOp d))
    (hB : ∀ d, (B d).Nonempty)
    {a A R : ℝ} (ha : 0 < a) (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hbound : ∀ d T, T ∈ B d → ‖T‖ ≤ R)
    (hlow : ∀ d : ℕ, 0 < d → a*(d:ℝ)^2 ≤ (n d+1 : ℕ))
    (hhigh : ∀ d : ℕ, 0 < d → ((n d+1 : ℕ):ℝ) ≤ A*(d:ℝ)^2) :
    Tendsto (fun d => |quadraticContinuumExpectation P d (n d) (B d)-
      goeContinuumExpectation P d (n d) (B d)|) atTop (nhds 0) := by
  classical
  obtain ⟨CW,hCW,hW⟩ := exists_gaussian_expected_net_ground_bound a A ha hA
  obtain ⟨CG,hCG,hG⟩ := exists_goe_expected_net_ground_bound a A ha hA
  have hφbound : ∀ u, |P.potential u| ≤ ‖P.potential‖ :=
    fun u => P.potential.norm_coe_le_norm u
  apply tendsto_zero_of_resolution _ (C := ‖P.potentialDeriv‖*(CW+CG))
    (fun _ => abs_nonneg _) (by positivity)
  intro η hη
  choose t ht hsub hnet hcard using
    (fun d => exists_operator_net (B d) (hB d) hR hη (hbound d))
  have hlog : 0 ≤ Real.log (1+2*R/η) := Real.log_nonneg (by
    have : 0 ≤ 2*R/η := by positivity
    linarith)
  have hfinite := net_expectation_universality P n t ht hR hlog
    (fun d T hT => hbound d T (hsub d T hT)) hhigh
    (fun d _ => by simpa only [mul_comm] using hcard d)
  have htail := exponential_sample_decay n ha hlow
  let e : ℕ → ℝ := fun d =>
    |quadraticNetExpectation P d (n d) (t d) (ht d)-goeNetExpectation P d (n d) (t d) (ht d)| +
      (4*A*‖P.potential‖)*Real.exp (-((n d+1 : ℕ):ℝ))
  refine ⟨e,?_,?_⟩
  · simpa only [e,mul_zero,add_zero] using hfinite.add (htail.const_mul (4*A*‖P.potential‖))
  · filter_upwards [eventually_gt_atTop (0:ℕ)] with d hd
    have hw := hW d (n d+1) hd (Nat.succ_pos _) (hlow d hd) (hhigh d hd)
      P.potential ‖P.potentialDeriv‖ ‖P.potential‖ (norm_nonneg _) (norm_nonneg _)
      P.potential.continuous (potential_lipschitz P) hφnonneg hφbound
      (B d) (hB d) (t d) (ht d) (hsub d) η hη.le (hnet d)
    have hg := hG d (n d+1) hd (Nat.succ_pos _) (hlow d hd) (hhigh d hd)
      P.potential ‖P.potentialDeriv‖ ‖P.potential‖ (norm_nonneg _) (norm_nonneg _)
      P.potential.continuous (potential_lipschitz P) hφnonneg hφbound
      (B d) (hB d) (t d) (ht d) (hsub d) η hη.le (hnet d)
    have hwmean := abs_expected_net_sub_ground_le_integral_abs
      (V := SymOp d) (ι := Fin (n d+1)) (gaussianSampleLaw d (n d+1)) d
      (fun x i => quadraticRow (x i)) P.potential P.potential.continuous hφbound
      continuous_quadraticRow_sample (B d) (hB d) (t d) (ht d)
    have hgmean := abs_expected_net_sub_ground_le_integral_abs
      (V := SymOp d) (ι := Fin (n d+1)) (goeSampleLaw d (n d+1)) d
      (fun z i => goeRow (z i)) P.potential P.potential.continuous hφbound
      continuous_goeRow_sample (B d) (hB d) (t d) (ht d)
    have hw' : |quadraticNetExpectation P d (n d) (t d) (ht d)-
        quadraticContinuumExpectation P d (n d) (B d)| ≤
        ‖P.potentialDeriv‖*CW*η+2*A*‖P.potential‖*Real.exp (-((n d+1 : ℕ):ℝ)) := hwmean.trans hw
    have hg' : |goeNetExpectation P d (n d) (t d) (ht d)-
        goeContinuumExpectation P d (n d) (B d)| ≤
        ‖P.potentialDeriv‖*CG*η+2*A*‖P.potential‖*Real.exp (-((n d+1 : ℕ):ℝ)) := hgmean.trans hg
    have htri := continuum_gap_le_net_gaps
      (quadraticContinuumExpectation P d (n d) (B d)) (goeContinuumExpectation P d (n d) (B d))
      (quadraticNetExpectation P d (n d) (t d) (ht d)) (goeNetExpectation P d (n d) (t d) (ht d))
    dsimp only [e]
    linarith

#print axioms continuum_ground_expectation_universality
end BMContinuumUniversality
