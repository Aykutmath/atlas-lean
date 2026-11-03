import Section_2_Preliminaries.MomentConverse

/-!
The supplied `reference/pasted-paper.txt`, lines 158–171, has damaged summation
bounds in the constructive moment-converse proof. Its first displayed bound is
literally `F ⊆ F ⊆ e`, where the mathematically necessary bound is `O ⊆ F ⊆ e`.
Its later sums likewise repeat `O ⊆ O` and `F ⊆ F`, losing the lower bound `A`.

If the repeated bound `F ⊆ F ⊆ e` is parsed literally, `F ⊆ F` is vacuous,
so the displayed cell formula sums over every `F ⊆ e`. The results below
kernel-check its smallest counterexample: one coordinate, with moments
`z_empty = 1` and `z_singleton = 0`. Both purported atoms become one, for total
two. The empty coordinate set has no defect, so one coordinate is minimal.

This diagnoses the provided transcription, not an intended mathematical
counterexample to moment inversion. `inverseCell` implements the repaired
bound. Its equivalence to `O ⊆ F ⊆ e` is proved below and its general
normalization is proved in `MomentConverse`. No false transcription is imported
as a premise.
-/
namespace AlphaCycle.PaperTranscription
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The correct `W ⊆ e \ O` formula is exactly the repaired interval bound `O ⊆ F ⊆ e`. -/
theorem inverseCell_eq_interval_sum (e O : Finset V) (hO : O ⊆ e) (z : Finset V → ℝ) :
    inverseCell e z O = ∑ F ∈ e.powerset,
      if O ⊆ F then (-1 : ℝ) ^ (F \ O).card * z F else 0 := by
  rw [← Finset.sum_filter]
  unfold inverseCell
  have hdiff (W : Finset V) (hW : W ∈ (e \ O).powerset) : (O ∪ W) \ O = W := by
    ext v
    have hn : v ∈ W → v ∉ O := fun hv => (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hW) hv)).2
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  apply Finset.sum_bij (fun W _ => O ∪ W)
  · intro W hW
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.union_subset hO
      ((Finset.mem_powerset.mp hW).trans Finset.sdiff_subset)), Finset.subset_union_left⟩
  · intro W hW U hU heq
    have h := congrArg (fun F => F \ O) heq
    simpa only [hdiff W hW, hdiff U hU] using h
  · intro F hF
    obtain ⟨hFe, hOF⟩ := Finset.mem_filter.mp hF
    refine ⟨F \ O, Finset.mem_powerset.mpr
      (by
        intro v hv
        exact Finset.mem_sdiff.mpr
          ⟨(Finset.mem_powerset.mp hFe) (Finset.mem_sdiff.mp hv).1, (Finset.mem_sdiff.mp hv).2⟩), ?_⟩
    exact Finset.union_sdiff_of_subset hOF
  · intro W hW
    rw [hdiff W hW]

/-- Literal interpretation after dropping the tautological first repeated bound. -/
noncomputable def malformedInverseCell (e : Finset V) (z : Finset V → ℝ) (O : Finset V) : ℝ :=
  ∑ F ∈ e.powerset, (-1 : ℝ) ^ (F \ O).card * z F

/-- Valid moment data of the deterministic all-zero assignment. -/
noncomputable def zeroAssignmentMoments (F : Finset V) : ℝ := if F = ∅ then 1 else 0

@[simp] theorem zeroAssignmentMoments_empty : zeroAssignmentMoments (∅ : Finset V) = 1 := by
  simp [zeroAssignmentMoments]

 theorem zeroAssignmentMoments_eq_moment (F : Finset V) :
    zeroAssignmentMoments F = moment (Law.dirac (∅ : Finset V)) F := by
  simp [zeroAssignmentMoments, moment]

/-- Under the damaged bounds, every alleged cell gets mass one. -/
theorem malformedInverseCell_zeroAssignmentMoments (e O : Finset V) :
    malformedInverseCell e zeroAssignmentMoments O = 1 := by
  simp [malformedInverseCell, zeroAssignmentMoments, mul_ite]

/-- The empty coordinate set is unaffected; a one-coordinate counterexample is minimal. -/
theorem malformed_empty_total :
    (∑ O ∈ (∅ : Finset Unit).powerset,
      malformedInverseCell ∅ zeroAssignmentMoments O) = 1 := by
  simp [malformedInverseCell_zeroAssignmentMoments]

/-- Both atoms of the smallest nonempty coordinate set receive mass one. -/
theorem malformed_singleton_cells :
    malformedInverseCell ({()} : Finset Unit) zeroAssignmentMoments ∅ = 1 ∧
    malformedInverseCell ({()} : Finset Unit) zeroAssignmentMoments {()} = 1 := by
  simp [malformedInverseCell_zeroAssignmentMoments]

/-- The literal malformed formula has total mass two, not one. -/
theorem malformed_singleton_total :
    (∑ O ∈ ({()} : Finset Unit).powerset,
      malformedInverseCell {()} zeroAssignmentMoments O) = 2 := by
  simp [malformedInverseCell_zeroAssignmentMoments, Finset.card_powerset]

/-- This is a failure of probability normalization. -/
theorem malformed_singleton_not_normalized :
    (∑ O ∈ ({()} : Finset Unit).powerset,
      malformedInverseCell {()} zeroAssignmentMoments O) ≠ 1 := by
  rw [malformed_singleton_total]
  norm_num

/-- The corrected formula returns the expected atom masses one and zero. -/
theorem repaired_singleton_cells :
    inverseCell ({()} : Finset Unit) zeroAssignmentMoments ∅ = 1 ∧
    inverseCell ({()} : Finset Unit) zeroAssignmentMoments {()} = 0 := by
  simp [inverseCell, zeroAssignmentMoments, Finset.powerset_insert]

/-- Correct inverse cells have total one for the identical input data. -/
theorem repaired_singleton_total :
    (∑ O ∈ ({()} : Finset Unit).powerset,
      inverseCell {()} zeroAssignmentMoments O) = 1 := by
  rw [sum_inverseCell]
  exact zeroAssignmentMoments_empty

end AlphaCycle.PaperTranscription
