import GaussianSampleRestriction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators
namespace BMCyclicRiskRestriction

/-- A cyclic window avoids factorially many permutations while sampling every
coordinate exactly n times across its N possible starting positions. -/
theorem sum_cyclic_windows {n N : ℕ} [NeZero N] (e : Fin n → Fin N)
    (v : Fin N → ℝ) :
    (∑ j : Fin N, ∑ i : Fin n, v (e i + j)) = (n : ℝ) * ∑ j, v j := by
  rw [Finset.sum_comm]
  have h (i : Fin n) : (∑ j : Fin N, v (e i + j)) = ∑ j, v j := by
    exact Fintype.sum_equiv (Equiv.addLeft (e i)) _ _ (fun _ => rfl)
  simp_rw [h]
  simp

/-- Exact average preservation for overlapping cyclic windows. -/
theorem average_cyclic_windows {n N : ℕ} [NeZero N] (hn : 0 < n)
    (e : Fin n → Fin N) (v : Fin N → ℝ) :
    (∑ j : Fin N, (∑ i : Fin n, v (e i + j)) / n) / N =
      (∑ j, v j) / N := by
  rw [← Finset.sum_div, sum_cyclic_windows]
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

/-- Deterministic fraction-of-bad-windows bound. The predicate may assert
that *every* constrained candidate has large window loss; using any one
full-sample candidate bounds the fraction without choosing a selector. -/
theorem bad_cyclic_fraction_le {n N : ℕ} [NeZero N] (hn : 0 < n)
    (e : Fin n → Fin N) (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (bad : Fin N → Prop) [DecidablePred bad] (ε δ : ℝ) (hε : 0 < ε)
    (hbad : ∀ j, bad j → ε < (∑ i : Fin n, v (e i + j)) / n)
    (hfull : (∑ j, v j) / N ≤ δ) :
    (∑ j : Fin N, if bad j then (1:ℝ) else 0) / N ≤ δ / ε := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hNpos : (0:ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hs : ε * (∑ j : Fin N, if bad j then (1:ℝ) else 0) ≤
      ∑ j : Fin N, (∑ i : Fin n, v (e i + j)) / n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : bad j
    · simpa [hj] using (hbad j hj).le
    · simp only [hj, ↓reduceIte, mul_zero]
      exact div_nonneg (Finset.sum_nonneg (fun i _ => hv _)) hnpos.le
  have hs' := div_le_div_of_nonneg_right hs hNpos.le
  rw [average_cyclic_windows hn] at hs'
  apply (le_div_iff₀ hε).2
  have he : ε * (∑ j : Fin N, if bad j then (1:ℝ) else 0) / N =
      ((∑ j : Fin N, if bad j then (1:ℝ) else 0) / N) * ε := by ring
  rw [he] at hs'
  exact hs'.trans hfull

end BMCyclicRiskRestriction

namespace BMCyclicRiskRestriction
open GaussianEllipsoidFinalPassage

/-- The shifted prefix is injective, so every cyclic window has the exact
smaller iid Gaussian law, despite the windows being dependent. -/
def cyclicEmbedding {n N : ℕ} [NeZero N] (h : n ≤ N) (j : Fin N) :
    Fin n ↪ Fin N :=
  (prefixEmbedding h).trans (Equiv.addRight j).toEmbedding

theorem cyclicRows_preserving {n N d : ℕ} [NeZero N] (h : n ≤ N) (j : Fin N) :
    MeasureTheory.MeasurePreserving
      (restrictRows (d:=d) (cyclicEmbedding h j))
      (MeasureTheory.Measure.pi (fun _ : Fin N => GaussianMixedNormHelpers.euclideanGaussianLaw (Fin d)))
      (MeasureTheory.Measure.pi (fun _ : Fin n => GaussianMixedNormHelpers.euclideanGaussianLaw (Fin d))) :=
  restrictRows_preserving _

#print axioms sum_cyclic_windows
#print axioms average_cyclic_windows
#print axioms bad_cyclic_fraction_le
#print axioms cyclicRows_preserving
end BMCyclicRiskRestriction
