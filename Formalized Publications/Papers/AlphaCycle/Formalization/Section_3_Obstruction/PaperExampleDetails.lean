import Section_2_Preliminaries.PaperGeometry
import Section_3_Obstruction.Examples

/-! Exact Venn data for the two concrete examples in the paper. -/
namespace AlphaCycle.Examples

/-- The graph triangle has singleton pair-only blocks and no common or private vertices. -/
theorem graphTriangle_venn :
    Geometry.common graphTriangle = ∅ ∧
    (∀ i, Geometry.privateBlock graphTriangle i = ∅) ∧
    Geometry.blockA graphTriangle = {0} ∧
    Geometry.blockB graphTriangle = {1} ∧
    Geometry.blockC graphTriangle = {2} := by decide

/-- The graph triangle already equals its no-private reduction. -/
theorem graphTriangle_reduced (i : Fin 3) :
    Geometry.reduced graphTriangle i = graphTriangle i := by
  fin_cases i <;> decide

/-- Every vertex of the concrete graph triangle is covered by its generating edges. -/
theorem graphTriangle_covers : ∀ v : Fin 3, ∃ i, v ∈ graphTriangle i := by decide

/-- The four-variable example has exactly two vertices in `A`, one in each of
`B,C`, and no common or private vertices. -/
theorem parityFour_venn :
    Geometry.common parityFour = ∅ ∧
    (∀ i, Geometry.privateBlock parityFour i = ∅) ∧
    Geometry.blockA parityFour = {0, 1} ∧
    Geometry.blockB parityFour = {3} ∧
    Geometry.blockC parityFour = {2} := by decide

/-- Every vertex of the four-variable example is covered by the generating edges. -/
theorem parityFour_covers : ∀ v : Fin 4, ∃ i, v ∈ parityFour i := by decide

end AlphaCycle.Examples
