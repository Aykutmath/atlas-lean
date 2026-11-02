import PaperExactPrefixPolar
import CanonicalProjectedPrefix

noncomputable section
open MeasureTheory
open GaussianMixedNormHelpers GaussianTensorMoments GaussianEllipsoidCandidate
open scoped InnerProductSpace
namespace GaussianEllipsoid.PaperCanonicalPolar
open ProjectedClusters

/-- The paper witness uses the literal d^(-1/2) coefficient normalization. -/
theorem exactPrefixBlockWitness_source {n h d K L : ℕ}
    (hKL : K ≤ L) (hL : L ≤ n) (u : Fin n → ℝ)
    (z : GaussianEntries n h × GaussianEntries n h) :
    exactPrefixBlockWitness (fun i => u i / Real.sqrt d)
      (tensorToCanonicalRows n h z) K L =
    canonicalOperator (frobeniusOperator (ProjectedClusters.projectedBilinear
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector
        (entriesToRows K h (selectSample (Fin.castLEEmb (hKL.trans hL)) z).1))
      (ContinuousLinearMap.id ℝ _ - finiteSpanProjector
        (entriesToRows K h (selectSample (Fin.castLEEmb (hKL.trans hL)) z).2))
      n d z ((MeasurableEquiv.toLp 2 ((Fin n) → ℝ))
        (ProjectedClusters.intervalCoefficients u K L)))) := by
  rw [← ProjectedClusters.projectedPrefixBlock_tensor_identity hKL hL,
    frobeniusOperator_operatorFrobenius, canonicalOperator_eq_polarWitness]
  rfl

/-- The first block is the sparse-prefix polar, including its normalization. -/
theorem exactPrefixBlockWitness_sparse {n r q d : ℕ} (u : Fin n → ℝ)
    (X : Fin n → Euclid q × Euclid r) (L : ℕ) :
    exactPrefixBlockWitness (fun i => u i / Real.sqrt d) X 0 L =
      canonicalOperator (prefixBilinearSynthesis (fun i => u i / Real.sqrt d) X L) := by
  rw [canonicalOperator_eq_polarWitness]
  unfold exactPrefixBlockWitness
  rw [projectedPrefixBlock_zero_left]

/-- Measurable history realization of the exactly scaled accumulated witness. -/
theorem paper_exact_prefix_predictable {ι : Type*} [Fintype ι] {N r q d : ℕ}
    (u : Fin N → ℝ) (lo hi : ι → ℕ)
    (hlo : ∀ j, lo j ≤ hi j)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) (i : Fin N) :
    ∃ W : (Fin i.val → Euclid q × Euclid r) → (Euclid q →L[ℝ] Euclid r),
      Measurable W ∧ (∀ Y, ‖W Y‖ ≤ 1) ∧
      ∀ X : Fin N → Euclid q × Euclid r,
        W (fun j => X ⟨j.val, j.isLt.trans i.isLt⟩) =
          exactCompletedPrefix (fun k => u k / Real.sqrt d) lo hi X i.val := by
  refine ⟨exactAdaptedPrefix (fun k => u k / Real.sqrt d) lo hi i.val,
    measurable_exactAdaptedPrefix _ _ _ _, ?_, ?_⟩
  · intro Y
    exact (exactAdaptedPrefix_norm_energy _ _ _ hlo hsep _ Y).1
  · intro X
    exact exactAdaptedPrefix_on_history _ _ _ hlo X i

#print axioms exactPrefixBlockWitness_source
#print axioms paper_exact_prefix_predictable
end GaussianEllipsoid.PaperCanonicalPolar
