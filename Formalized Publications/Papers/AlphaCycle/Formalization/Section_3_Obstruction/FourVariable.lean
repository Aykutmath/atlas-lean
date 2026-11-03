import Mathlib

/-! The four-variable obstruction, expressed directly in finite atom masses. -/
noncomputable section

namespace AlphaCycle.FourVariable

/-- Uniform law on `111, 100, 010, 001`. -/
def odd (a b c : Bool) : ℝ := if c = (a == b) then 1 / 4 else 0

/-- Independent fair bits. -/
def independent (_a _b : Bool) : ℝ := 1 / 4

theorem odd_nonneg (a b c : Bool) : 0 ≤ odd a b c := by
  unfold odd
  split <;> norm_num

theorem odd_pair (a b : Bool) : (∑ c : Bool, odd a b c) = 1 / 4 := by
  cases a <;> cases b <;> norm_num [odd, Fintype.sum_bool]

theorem odd_single (c : Bool) : (∑ a : Bool, ∑ b : Bool, odd a b c) = 1 / 2 := by
  cases c <;> norm_num [odd, Fintype.sum_bool]

theorem odd_total : (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, odd a b c) = 1 := by
  norm_num [odd, Fintype.sum_bool]

theorem independent_total : (∑ c : Bool, ∑ d : Bool, independent c d) = 1 := by
  norm_num [independent, Fintype.sum_bool]

/-- All three overlaps have identical distributions: `(1,2)`, `3`, and `4`. -/
theorem pairwise_consistent :
    (∀ a b : Bool, (∑ c : Bool, odd a b c) = ∑ d : Bool, odd a b d) ∧
    (∀ c : Bool, (∑ a : Bool, ∑ b : Bool, odd a b c) =
      ∑ d : Bool, independent c d) ∧
    (∀ d : Bool, (∑ a : Bool, ∑ b : Bool, odd a b d) =
      ∑ c : Bool, independent c d) := by
  constructor
  · intro a b; rfl
  constructor <;> intro x <;> rw [odd_single] <;> norm_num [independent, Fintype.sum_bool]

/-- Exact marginal conditions for a proposed joint law on all four bits. -/
def Realizes (q : Bool → Bool → Bool → Bool → ℝ) : Prop :=
    (∀ a b c, (∑ d : Bool, q a b c d) = odd a b c) ∧
    (∀ a b d, (∑ c : Bool, q a b c d) = odd a b d) ∧
    (∀ c d, (∑ a : Bool, ∑ b : Bool, q a b c d) = independent c d)

/-- There is no nonnegative joint mass with these three marginals.
No normalization hypothesis is needed: the marginal equations already imply it. -/
theorem no_global (q : Bool → Bool → Bool → Bool → ℝ)
    (hq : ∀ a b c d, 0 ≤ q a b c d) : ¬ Realizes q := by
  rintro ⟨h123, h124, h34⟩
  have e1 := h123 false false false
  have e2 := h124 false true true
  have e3 := h124 true false true
  have e4 := h123 true true false
  have e5 := h34 false true
  norm_num [odd, independent, Fintype.sum_bool] at e1 e2 e3 e4 e5
  linarith [hq false false false false, hq false true true true,
    hq true false true true, hq true true false false]

/-- The paper's first decisive checkpoint: normalized, pairwise-consistent local
laws on `123`, `124`, and `34` with no global probability law. -/
theorem obstruction :
    (∀ a b c, 0 ≤ odd a b c) ∧
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, odd a b c) = 1 ∧
    (∀ c d, 0 ≤ independent c d) ∧
    (∑ c : Bool, ∑ d : Bool, independent c d) = 1 ∧
    (∀ c : Bool, (∑ a : Bool, ∑ b : Bool, odd a b c) =
      ∑ d : Bool, independent c d) ∧
    (∀ d : Bool, (∑ a : Bool, ∑ b : Bool, odd a b d) =
      ∑ c : Bool, independent c d) ∧
    ¬ ∃ q : Bool → Bool → Bool → Bool → ℝ,
      (∀ a b c d, 0 ≤ q a b c d) ∧ Realizes q := by
  refine ⟨odd_nonneg, odd_total, ?_, independent_total,
    pairwise_consistent.2.1, pairwise_consistent.2.2, ?_⟩
  · intro c d; norm_num [independent]
  · rintro ⟨q, hq, hr⟩; exact no_global q hq hr

end AlphaCycle.FourVariable
