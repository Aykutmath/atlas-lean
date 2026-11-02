import BilinearGroupWitness

open MeasureTheory
open scoped InnerProductSpace

namespace GaussianEllipsoid

theorem prefixSpanProjector_zero {n q : ℕ} (f : Fin n → Euclid q) :
    prefixSpanProjector f 0 = 0 := by
  rw [prefixSpanProjector_eq]
  have hz : {i : Fin n | i.val < 0} = ∅ := by ext i; simp
  rw [hz, Set.image_empty, Submodule.span_empty]
  apply ContinuousLinearMap.ext
  intro x
  exact ((⊥ : Submodule ℝ (Euclid q)).orthogonalProjection x).property

theorem prefixBilinearSynthesis_zero {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) : prefixBilinearSynthesis u X 0 = 0 := by
  unfold prefixBilinearSynthesis bilinearSynthesis
  apply Finset.sum_eq_zero
  intro i _
  dsimp only
  rw [if_neg (Nat.not_lt_zero i.val)]
  exact zero_smul ℝ (bilinearRowOperator (X i))

/-- The first projected block is literally the sparse prefix synthesis. -/
theorem projectedPrefixBlock_zero_left {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) (L : ℕ) :
    projectedPrefixBlock u X 0 L = prefixBilinearSynthesis u X L := by
  unfold projectedPrefixBlock leftIncrement rightIncrement leftPrefixProjector rightPrefixProjector
  rw [prefixSpanProjector_zero, prefixSpanProjector_zero, sub_zero, sub_zero]
  change leftPrefixProjector X L ∘L prefixBilinearSynthesis u X L ∘L rightPrefixProjector X L = _
  rw [← ContinuousLinearMap.comp_assoc, leftPrefixProjector_synthesis u X (le_refl L),
    rightPrefixProjector_synthesis u X (le_refl L)]

/-- Literal interval coefficient mask for an actual prefix difference. -/
theorem prefixBilinearSynthesis_sub {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L) :
    prefixBilinearSynthesis u X L - prefixBilinearSynthesis u X K =
      bilinearSynthesis (fun i => if K ≤ i.val ∧ i.val < L then u i else 0) X := by
  unfold prefixBilinearSynthesis bilinearSynthesis
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  by_cases hK : i.val < K
  · have hL := hK.trans_le hKL
    simp only [hK, hL, if_true, Nat.not_le.mpr hK, false_and, if_false, sub_self]
    exact (zero_smul ℝ (bilinearRowOperator (X i))).symm
  · by_cases hL : i.val < L
    · simp only [hK, hL, if_false, if_true, Nat.le_of_not_gt hK, true_and]
      rw [zero_smul ℝ (bilinearRowOperator (X i)), sub_zero]
    · simp only [hK, hL, if_false, and_false, sub_self]
      exact (zero_smul ℝ (bilinearRowOperator (X i))).symm

theorem projectedPrefixBlock_eq_residual {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L) :
    projectedPrefixBlock u X K L =
      (ContinuousLinearMap.id ℝ (Euclid r) - leftPrefixProjector X K) ∘L
        bilinearSynthesis (fun i => if K ≤ i.val ∧ i.val < L then u i else 0) X ∘L
        (ContinuousLinearMap.id ℝ (Euclid q) - rightPrefixProjector X K) := by
  rw [← prefixBilinearSynthesis_sub u X hKL]
  exact projected_prefix_increment_eq u X hKL

/-- Prefix projectors equal the projector formed from the selected independent
head sample, without adding zero columns or full-rank assumptions. -/
theorem prefixSpanProjector_eq_selected {n q K : ℕ} (f : Fin n → Euclid q) (hK : K ≤ n) :
    prefixSpanProjector f K = finiteSpanProjector (fun i : Fin K => f (i.castLE hK)) := by
  rw [prefixSpanProjector_eq]
  unfold finiteSpanProjector
  have heq : f '' {i : Fin n | i.val < K} = Set.range (fun i : Fin K => f (i.castLE hK)) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.val,hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castLE hK, i.isLt, rfl⟩
  rw [heq]

theorem measurable_nuclear_projectedPrefixBlock {n r q : ℕ}
    (u : Fin n → ℝ) (K L : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r =>
      spectralNuclearNorm (operatorFrobenius (projectedPrefixBlock u X K L))) :=
  (continuous_spectralNuclear r q).measurable.comp
    ((continuous_operatorFrobenius r q).measurable.comp (measurable_projectedPrefixBlock u K L))

#print axioms prefixSpanProjector_zero
#print axioms prefixBilinearSynthesis_zero
#print axioms projectedPrefixBlock_zero_left
#print axioms prefixBilinearSynthesis_sub
#print axioms projectedPrefixBlock_eq_residual
#print axioms prefixSpanProjector_eq_selected
#print axioms measurable_nuclear_projectedPrefixBlock
end GaussianEllipsoid
