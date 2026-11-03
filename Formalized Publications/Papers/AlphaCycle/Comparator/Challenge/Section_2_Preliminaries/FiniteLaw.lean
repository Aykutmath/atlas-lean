import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

/-! Finite probability laws, with real cell masses. All probability identities in this
file are finite sums; no measure-theoretic completion is involved. -/
namespace AlphaCycle

open Classical
@[ext] structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Law
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
/-- The probability of a finite event. -/
noncomputable def prob (μ : Law α) (p : α → Prop) : ℝ :=
  ∑ a, if p a then μ.mass a else 0

end Law
end AlphaCycle
