import BilinearSynthesis
import FiniteSpanProjector
import OrthogonalPinching
import MeasurableSupportedWitness

open MeasureTheory Module
open scoped InnerProductSpace

namespace GaussianEllipsoid

/-- A prefix projector fixes every vector in that prefix. -/
theorem prefixSpanProjector_input {n q : ℕ} (f : Fin n → Euclid q) (K : ℕ)
    (i : Fin n) (hi : i.val < K) : prefixSpanProjector f K (f i) = f i := by
  rw [prefixSpanProjector_eq]
  let S := Submodule.span ℝ (f '' {j : Fin n | j.val < K})
  have hmem : f i ∈ S := Submodule.subset_span ⟨i, hi, rfl⟩
  exact congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨f i,hmem⟩ : S))

/-- Prefix projections depend only on their indicated sample coordinates. -/
theorem prefixSpanProjector_local {n q : ℕ} (f g : Fin n → Euclid q) (K : ℕ)
    (hfg : ∀ i, i.val < K → f i = g i) : prefixSpanProjector f K = prefixSpanProjector g K := by
  unfold prefixSpanProjector
  congr 1
  funext i
  split_ifs with hi
  · exact hfg i hi
  · rfl

noncomputable def leftPrefixProjector {n r q : ℕ} (X : Fin n → Euclid q × Euclid r)
    (K : ℕ) : Euclid r →L[ℝ] Euclid r := prefixSpanProjector (fun i => (X i).2) K

noncomputable def rightPrefixProjector {n r q : ℕ} (X : Fin n → Euclid q × Euclid r)
    (K : ℕ) : Euclid q →L[ℝ] Euclid q := prefixSpanProjector (fun i => (X i).1) K

noncomputable def prefixBilinearSynthesis {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) (K : ℕ) : Euclid q →L[ℝ] Euclid r :=
  bilinearSynthesis (fun i => if i.val < K then u i else 0) X

theorem measurable_leftPrefixProjector (n r q K : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => leftPrefixProjector X K) := by
  apply (measurable_prefixSpanProjector n K).comp
  exact measurable_pi_lambda _ fun i => measurable_snd.comp (measurable_pi_apply i)

theorem measurable_rightPrefixProjector (n r q K : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => rightPrefixProjector X K) := by
  apply (measurable_prefixSpanProjector n K).comp
  exact measurable_pi_lambda _ fun i => measurable_fst.comp (measurable_pi_apply i)

theorem measurable_prefixBilinearSynthesis {n r q : ℕ} (u : Fin n → ℝ) (K : ℕ) :
    Measurable (fun X : Fin n → Euclid q × Euclid r => prefixBilinearSynthesis u X K) :=
  measurable_bilinearSynthesis _

theorem prefixBilinearSynthesis_local {n r q : ℕ} (u : Fin n → ℝ)
    (X Y : Fin n → Euclid q × Euclid r) (K : ℕ)
    (hXY : ∀ i, i.val < K → X i = Y i) :
    prefixBilinearSynthesis u X K = prefixBilinearSynthesis u Y K := by
  unfold prefixBilinearSynthesis bilinearSynthesis
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < K
  · simp only [hi, if_true, hXY i hi]
  · dsimp only
    rw [if_neg hi]
    exact (zero_smul ℝ (bilinearRowOperator (X i))).trans (zero_smul ℝ (bilinearRowOperator (Y i))).symm

/-- Every prefix synthesis has its left range in the corresponding prefix span. -/
theorem leftPrefixProjector_synthesis {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L) :
    leftPrefixProjector X L ∘L prefixBilinearSynthesis u X K = prefixBilinearSynthesis u X K := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [prefixBilinearSynthesis, bilinearSynthesis, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < K
  · simp only [hi, if_true, bilinearRowOperator_apply, map_smul]
    rw [show leftPrefixProjector X L (X i).2 = (X i).2 from
      prefixSpanProjector_input _ L i (hi.trans_le hKL)]
  · simp [hi]

/-- Every prefix synthesis is right-supported on its right sample span. -/
theorem rightPrefixProjector_synthesis {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L) :
    prefixBilinearSynthesis u X K ∘L rightPrefixProjector X L = prefixBilinearSynthesis u X K := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [prefixBilinearSynthesis, bilinearSynthesis, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < K
  · simp only [hi, if_true, bilinearRowOperator_apply]
    congr 2
    rw [← ContinuousLinearMap.adjoint_inner_left,
      show ContinuousLinearMap.adjoint (rightPrefixProjector X L) = rightPrefixProjector X L from
        prefixSpanProjector_selfAdjoint _ L]
    rw [show rightPrefixProjector X L (X i).1 = (X i).1 from
      prefixSpanProjector_input _ L i (hi.trans_le hKL)]
  · simp [hi]

/-- The projected increment form equals removal of the earlier span from the
actual current coefficient block. This is the interface to projected small balls. -/
theorem projected_prefix_increment_eq {n r q : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) {K L : ℕ} (hKL : K ≤ L) :
    (leftPrefixProjector X L - leftPrefixProjector X K) ∘L prefixBilinearSynthesis u X L ∘L
        (rightPrefixProjector X L - rightPrefixProjector X K) =
      (ContinuousLinearMap.id ℝ (Euclid r) - leftPrefixProjector X K) ∘L
        (prefixBilinearSynthesis u X L - prefixBilinearSynthesis u X K) ∘L
        (ContinuousLinearMap.id ℝ (Euclid q) - rightPrefixProjector X K) := by
  let B := prefixBilinearSynthesis u X L
  let A := prefixBilinearSynthesis u X K
  let P := leftPrefixProjector X K
  let U := leftPrefixProjector X L
  let Q := rightPrefixProjector X K
  let V := rightPrefixProjector X L
  have hUB : U ∘L B = B := leftPrefixProjector_synthesis u X (le_refl L)
  have hBV : B ∘L V = B := rightPrefixProjector_synthesis u X (le_refl L)
  have hPA : P ∘L A = A := leftPrefixProjector_synthesis u X (le_refl K)
  have hleft : (U-P) ∘L B = B-P ∘L B := by rw [ContinuousLinearMap.sub_comp, hUB]
  have hright : (ContinuousLinearMap.id ℝ (Euclid r)-P) ∘L (B-A) = B-P ∘L B := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_sub, hPA]
    abel
  have hfix : (B-P ∘L B) ∘L V = B-P ∘L B := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc, hBV]
  change (U-P) ∘L B ∘L (V-Q) = (ContinuousLinearMap.id ℝ (Euclid r)-P) ∘L (B-A) ∘L
      (ContinuousLinearMap.id ℝ (Euclid q)-Q)
  rw [← ContinuousLinearMap.comp_assoc, hleft, ← ContinuousLinearMap.comp_assoc, hright,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_sub, hfix, ContinuousLinearMap.comp_id]

#print axioms prefixSpanProjector_input
#print axioms prefixSpanProjector_local
#print axioms measurable_leftPrefixProjector
#print axioms measurable_rightPrefixProjector
#print axioms measurable_prefixBilinearSynthesis
#print axioms prefixBilinearSynthesis_local
#print axioms leftPrefixProjector_synthesis
#print axioms rightPrefixProjector_synthesis
#print axioms projected_prefix_increment_eq

end GaussianEllipsoid
