import PaperFullHalfRetained
import PaperBilinearOriginalBlocks

noncomputable section
open Finset MeasureTheory Filter GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoid
open GaussianEllipsoid.ProjectedClusters GaussianEllipsoid.SparseSupport
open scoped BigOperators Topology
namespace GaussianEllipsoidCandidate.PaperLogarithmicDepth

def paperOriginalRows (d n : ℕ) (X : Fin n → Euclid d) :=
  extractedRows (paperBlockLeft d) (paperBlockRight d) X

theorem paperOriginalRows_coordinates (d n : ℕ) (X : Fin n → Euclid d)
    (i : Fin n) (j : Fin (d/2)) :
    (paperOriginalRows d n X i).1 j = X i (paperBlockRight d j) ∧
    (paperOriginalRows d n X i).2 j = X i (paperBlockLeft d j) := by
  exact ⟨extractedRows_fst _ _ _ _ _,extractedRows_snd _ _ _ _ _⟩

theorem paperOriginalRows_preserving (d n : ℕ) :
    MeasurePreserving (paperOriginalRows d n)
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d)))
      (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)) :=
  extractedRows_preserving _ _ (paperBlock_disjoint d)

theorem paper_original_nuclear_eq (d n : ℕ) (u : Fin n → ℝ) (X : Fin n → Euclid d) :
    scaledBilinearNuclear d u (paperOriginalRows d n X) =
      spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) := by
  unfold scaledBilinearNuclear paperOriginalRows
  rw [extractedRows_eq_tensorToCanonicalRows,scaled_bilinearSynthesis_tensorToCanonicalRows]
  rfl

/-- Exact event transport keeps the literal sparse singular-value event on the
actual first/last coordinate rows; no compressed sparse event is substituted. -/
theorem paper_original_retained_event_probability (d n : ℕ) (v : Fin n → ℝ) (c : ℝ) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
      {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) v)) < c ∧
        paperOriginalRows d n X ∈ paperSparseSingularGood d n (d/2)} =
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      ({Y | scaledBilinearNuclear d v Y < c} ∩ paperSparseSingularGood d n (d/2)) := by
  have hE : MeasurableSet ({Y | scaledBilinearNuclear d v Y < c} ∩ paperSparseSingularGood d n (d/2)) :=
    (isOpen_lt (continuous_scaledBilinearNuclear d v) continuous_const).measurableSet.inter
      (paperSparseSingularGood_isClosed d n (d/2)).measurableSet
  have he : {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) v)) < c ∧
      paperOriginalRows d n X ∈ paperSparseSingularGood d n (d/2)} =
      paperOriginalRows d n ⁻¹' ({Y | scaledBilinearNuclear d v Y < c} ∩ paperSparseSingularGood d n (d/2)) := by
    ext X
    simp only [Set.mem_setOf_eq,Set.mem_preimage,Set.mem_inter_iff,paper_original_nuclear_eq]
  rw [he]
  exact (paperOriginalRows_preserving d n).measureReal_preimage hE.nullMeasurableSet

theorem paper_original_full_event_probability (d n : ℕ) (u : Fin n → ℝ) (c : ℝ) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
      {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) < c ∧
        paperOriginalRows d n X ∈ paperSparseSingularGood d n (d/2) ∧
        paperOriginalRows d n X ∈ atomRowsGood d n (d/2)} =
    (gaussianBilinearSampleLaw (Fin n) (d/2) (d/2)).real
      ({Y | scaledBilinearNuclear d u Y < c} ∩ paperSparseSingularGood d n (d/2) ∩ atomRowsGood d n (d/2)) := by
  have hE : MeasurableSet ({Y | scaledBilinearNuclear d u Y < c} ∩ paperSparseSingularGood d n (d/2) ∩ atomRowsGood d n (d/2)) :=
    ((isOpen_lt (continuous_scaledBilinearNuclear d u) continuous_const).measurableSet.inter
      (paperSparseSingularGood_isClosed d n (d/2)).measurableSet).inter (atomRowsGood_measurable d n (d/2))
  have he : {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) < c ∧
        paperOriginalRows d n X ∈ paperSparseSingularGood d n (d/2) ∧
        paperOriginalRows d n X ∈ atomRowsGood d n (d/2)} =
      paperOriginalRows d n ⁻¹' ({Y | scaledBilinearNuclear d u Y < c} ∩ paperSparseSingularGood d n (d/2) ∩ atomRowsGood d n (d/2)) := by
    ext X
    simp only [Set.mem_setOf_eq,Set.mem_preimage,Set.mem_inter_iff,paper_original_nuclear_eq,and_assoc]
  rw [he]
  exact (paperOriginalRows_preserving d n).measureReal_preimage hE.nullMeasurableSet

theorem paper_original_fixed_vector_logarithmic_tail (A K : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
        {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ)) u)) <
          multiscaleFixedConstant K*Real.sqrt d ∧
          paperOriginalRows d n X ∈ paperSparseSingularGood d n (d/2) ∧
          paperOriginalRows d n X ∈ atomRowsGood d n (d/2)} ≤
        Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  obtain ⟨c,hc,d₀,hd₀⟩ := paper_full_half_fixed_vector_logarithmic_tail A K hA
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n hn u hu hs
  rw [paper_original_full_event_probability]
  exact hd₀ d hd n hn u hu hs

theorem paper_original_retained_logarithmic_tail (A K : ℝ) (hA : 0 < A) (hK : 1 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ n : ℕ, (n:ℝ) ≤ A*(d:ℝ)^2 → ∀ u : Fin n → ℝ,
      coefficientMass u=1 → ((Finset.univ.filter (fun i => u i ≠ 0)).card:ℝ) ≤ K*d →
      ∃ (N : ℕ) (groups : List (List ℕ)),
        0 < N ∧
        (∀ i, u i ≠ 0 ↔ ∃ t ∈ range N, i ∈ dyadicBin u ‖u‖ t) ∧
        (∀ t, N ≤ t → dyadicBin u ‖u‖ t=∅) ∧
        groups.flatten=dyadicRecordLevels u ‖u‖ N ∧
        (∀ g ∈ groups, RegularRetainedGroup u ‖u‖ (depth K) g) ∧
        groups.IsChain (RecordSuccessor fun t => (dyadicBin u ‖u‖ t).card) ∧
        coefficientMass (u-retainedGroupVector u ‖u‖ groups (depth K)) ≤ 8*(1/2:ℝ)^(depth K) ∧
        (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
          {X | spectralNuclearNorm (paperBilinearOperator d n X ((MeasurableEquiv.toLp 2 (Fin n → ℝ))
              (retainedGroupVector u ‖u‖ groups (depth K)))) <
            (1/2:ℝ)^24/(Real.sqrt K*(17*(1+Real.log K)))*Real.sqrt d*
              coefficientMass (retainedGroupVector u ‖u‖ groups (depth K)) ∧
            paperOriginalRows d n X ∈ paperSparseSingularGood d n (d/2)} ≤
          Real.log d*Real.exp (-c*(d:ℝ)^2/Real.log d) := by
  obtain ⟨c,hc,d₀,hd₀⟩ := paper_source_retained_logarithmic_tail A K hA hK
  refine ⟨c,hc,d₀,?_⟩
  intro d hd n hn u hu hs
  obtain ⟨N,groups,hN,hcover,hempty,hflat,hreg,hchain,herr,hprob⟩ := hd₀ d hd n hn u hu hs
  refine ⟨N,groups,hN,hcover,hempty,hflat,hreg,hchain,herr,?_⟩
  rw [paper_original_retained_event_probability]
  exact hprob

end GaussianEllipsoidCandidate.PaperLogarithmicDepth
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_original_retained_event_probability
#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_original_fixed_vector_logarithmic_tail

#print axioms GaussianEllipsoidCandidate.PaperLogarithmicDepth.paper_original_retained_logarithmic_tail
