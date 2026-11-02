import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.Basic

namespace GaussianEllipsoidCandidate

open Finset

/-- Geometrically growing records absorb every earlier record. -/
theorem geometric_prefix_mul_le (q : ℝ) (S : ℕ → ℝ)
    (hq : 1 < q) (hS : ∀ k, 0 ≤ S k)
    (hstep : ∀ k, q * S k ≤ S (k + 1)) (r : ℕ) :
    (q - 1) * (∑ i ∈ Finset.range r, S i) ≤ S r := by
  induction r with
  | zero => simpa using hS 0
  | succ r ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep r
      nlinarith

/-- The division form used for cumulative support estimates. -/
theorem geometric_prefix_le (q : ℝ) (S : ℕ → ℝ)
    (hq : 1 < q) (hS : ∀ k, 0 ≤ S k)
    (hstep : ∀ k, q * S k ≤ S (k + 1)) (r : ℕ) :
    (∑ i ∈ Finset.range r, S i) ≤ S r / (q - 1) := by
  apply (le_div_iff₀ (by linarith : 0 < q - 1)).2
  simpa [mul_comm] using geometric_prefix_mul_le q S hq hS hstep r

/-- Adding the current record gives the cutoff estimate. -/
theorem geometric_through_le (q : ℝ) (S : ℕ → ℝ)
    (hq : 1 < q) (hS : ∀ k, 0 ≤ S k)
    (hstep : ∀ k, q * S k ≤ S (k + 1)) (r : ℕ) :
    (q - 1) * (∑ i ∈ Finset.range (r + 1), S i) ≤ q * S r := by
  rw [Finset.sum_range_succ]
  have h := geometric_prefix_mul_le q S hq hS hstep r
  nlinarith

/-- A lower bound survives addition of a controlled error. -/
theorem norm_add_ge_sub {E : Type*} [NormedAddCommGroup E]
    (x y : E) (a b : ℝ) (hx : a ≤ ‖x‖) (hy : ‖y‖ ≤ b) :
    a - b ≤ ‖x + y‖ := by
  have ht := norm_sub_le (x + y) y
  simp only [add_sub_cancel_right] at ht
  linarith

/-- Net extension in any normed vector space; nuclear norm is an instance. -/
theorem norm_ge_from_approximation {E : Type*} [NormedAddCommGroup E]
    (x z : E) (c ε : ℝ) (hz : c ≤ ‖z‖)
    (hdist : ‖x - z‖ ≤ ε) : c - ε ≤ ‖x‖ := by
  have ht := norm_sub_le x (x - z)
  have heq : x - (x - z) = z := by abel
  rw [heq] at ht
  linarith

/-- Deterministic cross-term scale used by the exponential estimate. -/
theorem sum_sq_le_sq_sum {ι : Type*} [Fintype ι] (m : ι → ℝ)
    (hm : ∀ i, 0 ≤ m i) :
    ∑ i, (m i)^2 ≤ (∑ i, m i)^2 := by
  classical
  have hcoord : ∀ i, m i ≤ ∑ j, m j := by
    intro i
    exact Finset.single_le_sum (fun j _ => hm j) (Finset.mem_univ i)
  calc
    ∑ i, (m i)^2 ≤ ∑ i, m i * (∑ j, m j) := by
      apply Finset.sum_le_sum
      intro i _
      simpa [pow_two] using mul_le_mul_of_nonneg_left (hcoord i) (hm i)
    _ = (∑ i, m i)^2 := by rw [← Finset.sum_mul]; ring

/-- Scalar final absorption; no normalization or positivity hidden in a division. -/
theorem retained_tail_absorption (c C ε : ℝ)
    (hc : 0 ≤ c) (heps : ε ≤ 1 / 2) (herr : C * ε ≤ c / 4) :
    c / 4 ≤ c * (1 - ε) - C * ε := by
  nlinarith

end GaussianEllipsoidCandidate
