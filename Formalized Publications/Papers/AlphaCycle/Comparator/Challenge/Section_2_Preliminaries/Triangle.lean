import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/
namespace AlphaCycle.Triangle
noncomputable section

/-- The four generalized triangle inequalities in common/pair-only coordinates.
Here `m` is the common-block mass; `p`, `q`, `r` are the three intersection
moments; and `pq`, `pr`, `qr` are the three edge moments. -/
def GT (m p q r pq pr qr : ℝ) : Prop :=
  pq + pr ≤ p + qr ∧ pq + qr ≤ q + pr ∧ pr + qr ≤ r + pq ∧
    p + q + r ≤ m + pq + pr + qr
variable {V : Type*} [DecidableEq V]
/-- A triple has no vertex occurring in just one of its edges. -/
def NoPrivate (f₁ f₂ f₃ : Finset V) : Prop :=
  f₁ ⊆ f₂ ∪ f₃ ∧ f₂ ⊆ f₁ ∪ f₃ ∧ f₃ ⊆ f₁ ∪ f₂

end
end AlphaCycle.Triangle
