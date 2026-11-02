import AHHCanonicalMoves
import Mathlib.Algebra.Order.Chebyshev

/-! Weighted finite Cauchy--Schwarz turns an exact one-subsystem local loop
identity into the two-subsystem per-word inequality. No trace positivity premise
is needed for this scalar squaring step. -/
noncomputable section
open scoped BigOperators
namespace AHH

theorem weighted_square_bound (b d : ℝ) {s : ℝ} (hs : 0 < s) :
    (b + d) ^ 2 ≤ (1 + 1 / s) * b ^ 2 + (1 + s) * d ^ 2 := by
  have hid : (1 + 1 / s) * b ^ 2 + (1 + s) * d ^ 2 - (b + d) ^ 2 =
      (b - s * d) ^ 2 / s := by field_simp; ring
  have hp := div_nonneg (sq_nonneg (b - s * d)) hs.le
  linarith

/-- The local bound for any finite move family of at most `N` terms. -/
theorem local_square_elimination {ι : Type*} (D : Finset ι) (f : ι → ℝ)
    (a b : ℝ) {H N : ℝ} (hH : 0 < H) (hN : (D.card : ℝ) ≤ N)
    (hloop : a = (b + ∑ i ∈ D, f i) / H) :
    a ^ 2 ≤ ((1 + 1 / Real.sqrt H) / H ^ 2) * b ^ 2 +
      (((1 + Real.sqrt H) * N) / H ^ 2) * ∑ i ∈ D, f i ^ 2 := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hsq : (∑ i ∈ D, f i) ^ 2 ≤ N * ∑ i ∈ D, f i ^ 2 := by
    exact (sq_sum_le_card_mul_sum_sq).trans
      (mul_le_mul_of_nonneg_right hN (Finset.sum_nonneg (fun i _ => sq_nonneg (f i))))
  rw [hloop, div_pow]
  calc
    _ ≤ ((1 + 1 / Real.sqrt H) * b ^ 2 +
        (1 + Real.sqrt H) * (∑ i ∈ D, f i) ^ 2) / H ^ 2 :=
      (div_le_div_iff_of_pos_right (pow_pos hH 2)).mpr (weighted_square_bound b _ hs)
    _ ≤ ((1 + 1 / Real.sqrt H) * b ^ 2 +
        (1 + Real.sqrt H) * (N * ∑ i ∈ D, f i ^ 2)) / H ^ 2 := by
      gcongr
    _ = _ := by ring

/-- Canonical moves have the required `j-1` cardinal bound, already kernel checked. -/
theorem word_square_elimination {α : Type*} (d : WordSplit α)
    (f : Rearrangement α → ℝ) (a b : ℝ) {H : ℝ} (hH : 0 < H)
    (hloop : a = (b + ∑ r ∈ d.moves, f r) / H) :
    a ^ 2 ≤ ((1 + 1 / Real.sqrt H) / H ^ 2) * b ^ 2 +
      (((1 + Real.sqrt H) * (d.original.length - 1 : ℕ)) / H ^ 2) *
        ∑ r ∈ d.moves, f r ^ 2 := by
  exact local_square_elimination d.moves f a b hH (Nat.cast_le.mpr d.card_moves_le) hloop

end AHH
