import UCDiffuseFrameReduction
import UCPeelingSourceReduction
import UCFinalScalarAudit

/-! The source project's full uniform conic lower bound, with every analytic,
Gaussian-comparison, concentration, discretization and spectral hypothesis
proved. Constants are uniform on each fixed aspect interval above 1/4. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GaussianEllipsoid
open UCFrameGeometry UCFrameProbability UCRotatedConicMargin UCFrameUnion
open UCContinuityGeometry UCUniformContinuity UCPeelingSmallTail UCDiffuseFrameReduction

/-- The complete quantitative conic lower bound of the actual source project.
There are no Gaussian representation, comparison, entropy, concentration or
geometric premises. -/
theorem uniformConicBound_unconditional : UniformConicBound := by
  classical
  intro αm αp hαm hαp
  have ha : 0 < αm := by linarith
  obtain ⟨τ,c,C,hτ,hτ1,hc,hC,hSplit⟩ := exists_uniform_fixed_split_tail αm αp hαm hαp
  obtain ⟨K,hBudget,hReduction⟩ := exists_source_probability_reduction ha hτ
  let t := rotationTolerance αm c
  have ht : 0 < t := rotationTolerance_pos ha hc
  obtain ⟨q,hq,hAbsorb⟩ := UCFinalScalarAudit.three_exponentials_absorption ha
    exceptionRate_pos (show 0 < C/2 by positivity)
  refine ⟨finalMargin αm c,q,finalMargin_pos ha hc,hq,?_⟩
  filter_upwards [hReduction,hSplit K,frame_entropy_absorption K t C hC,hAbsorb,
    eventually_ge_atTop 1] with d hReductionD hSplitD hEntropy hAbsorbD hd1
  intro n hnlo hnhi
  have hd : 0 < d := by omega
  have hn : 0 < n := by
    have hp : (0:ℝ) < αm*(d:ℝ)^2 := mul_pos ha (sq_pos_of_pos (by exact_mod_cast hd))
    exact_mod_cast hp.trans_le hnlo
  choose N hFrames hCard hCover using
    fun j : Fin (K+1) => exists_aligned_frame_net d j.val ht
  have hCover' : ∀ j : Fin (K+1), ∀ U : FrobeniusMatrix d j.val, IsFrame U →
      ∃ V ∈ N j, ∃ O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d),
        (∀ i, O (U i) = V i) ∧
          ‖(O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))-1‖ < rotationTolerance αm c := by
    intro j U hU
    obtain ⟨V,hVN,O,hO,hNear⟩ := hCover j U hU
    exact ⟨V,hVN,O,hO,hNear⟩
  have hCenter : ∀ j : Fin (K+1), ∀ V ∈ N j,
      (gaussianSampleLaw d n).real (frameBad V τ c) ≤ Real.exp (-C*(d:ℝ)^2) := by
    intro j V hVN
    rw [frameBad_of_isFrame V (hFrames j V hVN)]
    exact hSplitD n hnlo hnhi j.val (by omega) _
  have hUnion : (gaussianSampleLaw d n).real (⋃ j, ⋃ V ∈ N j, frameBad V τ c) ≤
      Real.exp (-(C/2)*(d:ℝ)^2) := by
    exact (finite_frame_union_bound (gaussianSampleLaw d n) d K t C ht N
      (by intro j; exact hCard j) (fun _ V => frameBad V τ c) hCenter).trans hEntropy
  have hDiffuse : (gaussianSampleLaw d n).real
      (diffuseBadEvent αm τ d n K (finalMargin αm c)) ≤
        Real.exp (-(n:ℝ))+Real.exp (-(C/2)*(d:ℝ)^2) := by
    calc
      _ ≤ (gaussianSampleLaw d n).real
          (continuityException αm d n ∪ ⋃ j, ⋃ V ∈ N j, frameBad V τ c) :=
        measureReal_mono (diffuseBad_subset_frame_union ha hc hn N hFrames hCover')
      _ ≤ (gaussianSampleLaw d n).real (continuityException αm d n)+
          (gaussianSampleLaw d n).real (⋃ j, ⋃ V ∈ N j, frameBad V τ c) :=
        measureReal_union_le _ _
      _ ≤ _ := add_le_add (empiricalOperator_tail ha hd hn hnlo) hUnion
  exact (hReductionD n hnlo (finalMargin αm c) (finalMargin_le_peeledMargin αm c)).trans
    ((add_le_add le_rfl hDiffuse).trans (hAbsorbD n hnlo))

#print axioms uniformConicBound_unconditional
end GaussianEllipsoid
