import Challenge.Section_2_Preliminaries.FiniteLaw
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

namespace AlphaCycle
open Classical

abbrev BooleanLaw (α : Type*) [Fintype α] := Law (Finset α)
/-- The squarefree moment indexed by `s`: all coordinates of `s` equal one. -/
noncomputable def moment {α : Type*} [Fintype α]
    (μ : BooleanLaw α) (s : Finset α) : ℝ := μ.prob (fun t => s ⊆ t)

end AlphaCycle
