import Challenge.Section_2_Preliminaries.PaperCoordinates
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

/-! The complete-edge/local-law dictionary for arbitrary completed finite hypergraphs. -/
namespace AlphaCycle.PaperHypergraph
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : PaperHypergraph V)
/-- A total extension of the paper's monomial coordinates; only supported subsets are used. -/
noncomputable def momentCoordinate (z : H.Vector) (s : Finset V) : ℝ :=
  if hs : s ∈ H.coordinateSupport then H.fromPaper z ⟨s, hs⟩ else 0
/-- The literal paper vector in the existing development's completed-support coordinates. -/
noncomputable def cycleCoordinates (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : (ofThree e hc hv).completion.Vector) :
    MomentVector (completedSupport e) := fun s =>
  (ofThree e hc hv).completion.momentCoordinate z s.val

end AlphaCycle.PaperHypergraph
