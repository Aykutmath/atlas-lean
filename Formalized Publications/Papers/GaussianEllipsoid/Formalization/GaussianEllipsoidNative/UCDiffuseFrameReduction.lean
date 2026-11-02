import UCFrameSourceTransport
import UCFixedFrameWitness
import UCRotatedConicMargin
import UCFrameProbability
import UCFrameUnion

/-! Pathwise reduction of the entire peeled diffuse event to an actual
continuity exception and a finite family of fixed-frame measurable events. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory Filter
open scoped Classical
open scoped BigOperators Topology
namespace GaussianEllipsoid.UCDiffuseFrameReduction
open UCFrameGeometry UCFrameProbability UCRotatedConicMargin UCMatrixRotation
open UCContinuityGeometry UCUniformContinuity UCPeelingSmallTail

 def frameBad {d j n : ℕ} (V : FrobeniusMatrix d j) (τ c : ℝ) : Set (Sample d n) := by
  classical
  exact if hV : IsFrame V then fixedSplitBad (UCEscape.frameCompletion (frameLinearIsometry V hV)) τ c
  else ∅

 theorem frameBad_of_isFrame {d j n : ℕ} (V : FrobeniusMatrix d j) (hV : IsFrame V) (τ c : ℝ) :
    frameBad (n := n) V τ c = fixedSplitBad (UCEscape.frameCompletion (frameLinearIsometry V hV)) τ c := by
  simp only [frameBad,dif_pos hV]

/-- Each normalized diffuse witness is rotated into a fixed net head space.
The extra empirical-continuity exception is retained explicitly. -/
theorem diffuseBad_subset_frame_union {a τ c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {d n K : ℕ} (hn : 0 < n)
    (N : (j : Fin (K+1)) → Finset (FrobeniusMatrix d j.val))
    (hFrames : ∀ j, ∀ V ∈ N j, IsFrame V)
    (hCover : ∀ j, ∀ U : FrobeniusMatrix d j.val, IsFrame U →
      ∃ V ∈ N j, ∃ O : (EuclideanSpace ℝ (Fin d)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin d)),
        (∀ i, O (U i) = V i) ∧
          ‖(O : (EuclideanSpace ℝ (Fin d)) →L[ℝ] (EuclideanSpace ℝ (Fin d)))-1‖ < rotationTolerance a c) :
    diffuseBadEvent a τ d n K (finalMargin a c) ⊆
      continuityException a d n ∪ ⋃ j, ⋃ V ∈ N j, frameBad V τ c := by
  classical
  intro x hx
  by_cases hCont : x ∈ continuityException a d n
  · exact Or.inl hCont
  right
  have hC : ‖empiricalOperator x‖ ≤ continuityConstant a := le_of_not_gt hCont
  obtain ⟨H,D,ρ,hH,hRank,hD,hHD,hDF,hDop,hρ,hρ1,henergy,hAF,hbad⟩ := hx
  let j : Fin (K+1) := ⟨Module.finrank ℝ (UCEscape.headSpace H),
    Nat.lt_succ_of_le (source_head_frame_dimension_le H hRank)⟩
  obtain ⟨V,hVN,O,hO,hNear⟩ := hCover j (headFrameColumns H) (headFrameColumns_isFrame H)
  have hV := hFrames j V hVN
  have hρpos : 0 < ρ := (tailCutoff_pos ha).trans hρ
  have hA : (H+ρ • D).PosSemidef := hH.add (hD.smul hρpos.le)
  have hRot := rotated_conic_lt_scaled ha hc hn x (H+ρ • D) hA hAF O hNear hC ρ hρ hbad
  rw [conjugate_add,conjugate_smul] at hRot
  obtain ⟨hHead,hTail⟩ := aligned_source_head_tail_support H D hH hHD V hV O hO
  have hFixed := UCEscape.fixed_frame_witness_mem_bad (frameLinearIsometry V hV) x
    (conjugate O H) (conjugate O D) (conjugate_posSemidef O hH) (conjugate_posSemidef O hD)
    hHead hTail (by simpa only [conjugate_frobeniusNorm] using hDF)
    (by simpa only [conjugate_matrixOpNorm] using hDop) hρpos hRot
  refine Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨hVN, ?_⟩⟩⟩
  rw [frameBad_of_isFrame V hV]
  exact hFixed

#print axioms diffuseBad_subset_frame_union
end GaussianEllipsoid.UCDiffuseFrameReduction
