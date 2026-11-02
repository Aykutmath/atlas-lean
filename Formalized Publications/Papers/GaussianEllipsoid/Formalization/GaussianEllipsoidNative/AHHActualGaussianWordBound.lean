import AHHNormalizedWordStein
import AHHPositionMomentBound

/-! The sharp finite word-moment estimate for the actual normalized complex
Gaussian measure. All analytic and combinatorial hypotheses are discharged. -/
noncomputable section
open scoped BigOperators
namespace AHHGaussian
set_option backward.isDefEq.respectTransparency false

/-- No abstract moment, word law, or recurrence is an input to this theorem. -/
theorem normalizedGaussian_word_moment_bound (n h m : ℕ) (hh : 1 ≤ h) :
    AHH.wordSum (fun w : List (Fin n) => normalizedWordMean n h w ^ 2) m ≤
      (h : ℝ) ^ 2 * AHH.edgeR (1 + 1 / Real.sqrt (h : ℝ))
        ((n : ℝ) / (h : ℝ) ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt (h : ℝ)) *
      AHH.edgeL (1 + 1 / Real.sqrt (h : ℝ))
        ((n : ℝ) / (h : ℝ) ^ 2 + 4 * (m : ℝ) ^ 5 / Real.sqrt (h : ℝ)) ^ m := by
  have h := AHH.moment_bound_of_position_loop
    (normalizedWordMean n h) (normalizedWordPairMean n h)
    (H := (h : ℝ)) (by exact_mod_cast hh) (normalizedWordMean_nil n h) m
    (normalizedWordMean_cyclic n h)
    (normalizedWordPairMean_glue n h)
    (fun d hd => normalizedWordPairMean_disjoint n h d.L d.R
      (List.disjoint_left.mpr (fun a ha hb => hd ⟨a, ha, hb⟩)))
    (by
      intro s w
      refine (normalizedWordMean_position_loop n h (by omega) s w).trans ?_
      apply congrArg (fun y : ℝ => (normalizedWordMean n h w + y) / (h : ℝ))
      apply Finset.sum_congr rfl
      intro k _
      by_cases he : s = w.get k <;> simp [he])
  simpa only [Fintype.card_fin] using h

#print axioms normalizedGaussian_word_moment_bound

end AHHGaussian
