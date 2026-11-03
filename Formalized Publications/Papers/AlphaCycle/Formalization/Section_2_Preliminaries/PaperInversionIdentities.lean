import Section_2_Preliminaries.PaperTranscription

/-! Exact interval-indexed identities displayed in the constructive moment
inversion proof, after repairing the damaged lower summation bounds. -/
namespace AlphaCycle
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's inner alternating interval sum, with its exact `F \ O` exponent. -/
theorem interval_alternating_sum (A F : Finset V) (hAF : A ⊆ F) :
    (∑ O ∈ F.powerset, if A ⊆ O then (-1 : ℝ) ^ (F \ O).card else 0) =
      if A = F then 1 else 0 := by
  classical
  rw [← Finset.sum_filter, ← alternating_interval_sum A F hAF]
  have hdouble (W : Finset V) (hWF : W ⊆ F) : F \ (F \ W) = W := by
    ext v
    have hv := @hWF v
    simp only [Finset.mem_sdiff] at hv ⊢
    tauto
  symm
  apply Finset.sum_bij (fun W _ => F \ W)
  · intro W hW
    have hWA := Finset.mem_powerset.mp hW
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
    intro v hv
    refine Finset.mem_sdiff.mpr ⟨hAF hv, ?_⟩
    intro hvW
    exact (Finset.mem_sdiff.mp (hWA hvW)).2 hv
  · intro W hW U hU heq
    have hh := congrArg (fun O => F \ O) heq
    simpa only [hdouble W ((Finset.mem_powerset.mp hW).trans Finset.sdiff_subset),
      hdouble U ((Finset.mem_powerset.mp hU).trans Finset.sdiff_subset)] using hh
  · intro O hO
    obtain ⟨hOF, hAO⟩ := Finset.mem_filter.mp hO
    refine ⟨F \ O, Finset.mem_powerset.mpr ?_, hdouble O (Finset.mem_powerset.mp hOF)⟩
    intro v hv
    obtain ⟨hvF, hvO⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨hvF, fun hvA => hvO (hAO hvA)⟩
  · intro W hW
    rw [hdouble W ((Finset.mem_powerset.mp hW).trans Finset.sdiff_subset)]

/-- The weighted outer interval sum reduces to the moment `z_A`, because every
inner interval cancels except the interval with endpoint `F=A`. -/
theorem weighted_interval_alternating_sum (e A : Finset V) (hA : A ⊆ e)
    (z : Finset V → ℝ) :
    (∑ F ∈ e.powerset, if A ⊆ F then z F *
      (∑ O ∈ F.powerset, if A ⊆ O then (-1 : ℝ) ^ (F \ O).card else 0) else 0) = z A := by
  classical
  rw [Finset.sum_eq_single A]
  · simp [interval_alternating_sum A A (Finset.Subset.refl A)]
  · intro F _ hFA
    by_cases hAF : A ⊆ F
    · simp [hAF, interval_alternating_sum A F hAF, Ne.symm hFA]
    · simp [hAF]
  · simp [Finset.mem_powerset.mpr hA]

/-- The exact rearranged double-sum identity displayed in the constructive
converse, written with finite sums and repaired interval bounds. -/
theorem inverseCell_sum_reordered (e A : Finset V) (hA : A ⊆ e)
    (z : Finset V → ℝ) :
    (∑ O ∈ e.powerset, if A ⊆ O then inverseCell e z O else 0) =
      ∑ F ∈ e.powerset, if A ⊆ F then z F *
        (∑ O ∈ F.powerset, if A ⊆ O then (-1 : ℝ) ^ (F \ O).card else 0) else 0 := by
  rw [sum_inverseCell_eq e z A hA, weighted_interval_alternating_sum e A hA z]

end AlphaCycle
