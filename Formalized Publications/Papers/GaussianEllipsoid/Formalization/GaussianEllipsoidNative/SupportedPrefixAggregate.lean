/- Newly reconstructed source, 2026-10-03. Not recovered original bytes.
   Native verification pending. -/
import PrefixWitnessRankEnergy

noncomputable section
open MeasureTheory Module
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid

def completedSupportedPrefix {ι : Type*} [Fintype ι] {r q : ℕ}
    (W : ι → Euclid q →L[ℝ] Euclid r) (hi : ι → ℕ) (t : ℕ) :=
  ∑ j, if hi j ≤ t then W j else 0

theorem measurable_completedSupportedPrefix {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] {r q : ℕ} (W : ι → Ω → Euclid q →L[ℝ] Euclid r)
    (hW : ∀ j, Measurable (W j)) (hi : ι → ℕ) (t : ℕ) :
    Measurable (fun X => completedSupportedPrefix (fun j => W j X) hi t) := by
  apply Finset.measurable_sum
  intro j _
  by_cases hj : hi j ≤ t
  · simpa only [hj, if_true] using hW j
  · simp only [hj, if_false]; exact measurable_const

theorem completedSupportedPrefix_norm_le_one {ι : Type*} [Fintype ι] {n r q : ℕ}
    (X : Fin n → Euclid q × Euclid r) (W : ι → Euclid q →L[ℝ] Euclid r)
    (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hn : ∀ j, ‖W j‖ ≤ 1)
    (hs : ∀ j, leftIncrement X (lo j) (hi j) ∘L W j ∘L rightIncrement X (lo j) (hi j) = W j)
    (t : ℕ) : ‖completedSupportedPrefix W hi t‖ ≤ 1 := by
  apply norm_sum_supported_le_one (fun j => leftIncrement X (lo j) (hi j))
    (fun j => rightIncrement X (lo j) (hi j)) _
  · intro j; exact prefixSpanProjector_increment_selfAdjoint _ _ _
  · intro j; exact prefixSpanProjector_increment_selfAdjoint _ _ _
  · intro j; exact prefixSpanProjector_increment_idempotent _ (hlo j)
  · intro j; exact prefixSpanProjector_increment_idempotent _ (hlo j)
  · intro i j hij; exact prefix_increments_orthogonal _ (hlo i) (hlo j) (hsep i j hij)
  · intro i j hij; exact prefix_increments_orthogonal _ (hlo i) (hlo j) (hsep i j hij)
  · intro j; split_ifs
    · exact hn j
    · simp
  · intro j; split_ifs
    · exact hs j
    · simp

theorem completedSupportedPrefix_right_prefix {ι : Type*} [Fintype ι] {n r q : ℕ}
    (X : Fin n → Euclid q × Euclid r) (W : ι → Euclid q →L[ℝ] Euclid r)
    (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (hs : ∀ j, leftIncrement X (lo j) (hi j) ∘L W j ∘L rightIncrement X (lo j) (hi j) = W j)
    (t : ℕ) : completedSupportedPrefix W hi t ∘L rightPrefixProjector X t =
      completedSupportedPrefix W hi t := by
  have hw (j : ι) (hj : hi j ≤ t) : W j ∘L rightPrefixProjector X t = W j := by
    have he : rightIncrement X (lo j) (hi j) ∘L rightPrefixProjector X t =
        rightIncrement X (lo j) (hi j) := by
      change (prefixSpanProjector (fun i => (X i).1) (hi j) -
        prefixSpanProjector (fun i => (X i).1) (lo j)) ∘L
        prefixSpanProjector (fun i => (X i).1) t = _
      rw [ContinuousLinearMap.sub_comp, prefixSpanProjector_comp_of_le _ hj,
        prefixSpanProjector_comp_of_le _ ((hlo j).trans hj)]
      rfl
    calc
      _ = (leftIncrement X (lo j) (hi j) ∘L W j ∘L rightIncrement X (lo j) (hi j))
          ∘L rightPrefixProjector X t := by rw [hs]
      _ = leftIncrement X (lo j) (hi j) ∘L W j ∘L
          (rightIncrement X (lo j) (hi j) ∘L rightPrefixProjector X t) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = W j := by rw [he, hs]
  apply ContinuousLinearMap.ext
  intro z
  simp only [completedSupportedPrefix, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : hi j ≤ t
  · simp only [if_pos hj]
    exact congrArg (fun V : Euclid q →L[ℝ] Euclid r => V z) (hw j hj)
  · simp only [if_neg hj, ContinuousLinearMap.zero_apply]

theorem completedSupportedPrefix_energy_le_prefix_length {ι : Type*} [Fintype ι] {n r q : ℕ}
    (X : Fin n → Euclid q × Euclid r) (W : ι → Euclid q →L[ℝ] Euclid r)
    (lo hi : ι → ℕ) (hlo : ∀ j, lo j ≤ hi j)
    (hsep : ∀ i j, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hn : ∀ j, ‖W j‖ ≤ 1)
    (hs : ∀ j, leftIncrement X (lo j) (hi j) ∘L W j ∘L rightIncrement X (lo j) (hi j) = W j)
    (t : ℕ) : ‖operatorFrobenius (completedSupportedPrefix W hi t)‖^2 ≤ (t : ℝ) := by
  have h := frobenius_supported_contraction_sq_le_rank
    (completedSupportedPrefix W hi t) (rightPrefixProjector X t)
    (completedSupportedPrefix_norm_le_one X W lo hi hlo hsep hn hs t)
    (prefixSpanProjector_selfAdjoint _ t)
    (prefixSpanProjector_comp_of_le _ (le_refl t))
    (completedSupportedPrefix_right_prefix X W lo hi hlo hs t)
  have hr : LinearMap.range (rightPrefixProjector X t).toLinearMap =
      Submodule.span ℝ ((fun i => (X i).1) '' {i : Fin n | i.val < t}) := by
    unfold rightPrefixProjector
    rw [prefixSpanProjector_eq]
    exact Submodule.range_starProjection _
  rw [hr] at h
  exact h.trans (by exact_mod_cast prefix_span_finrank_le (fun i => (X i).1) t)

end GaussianEllipsoid
