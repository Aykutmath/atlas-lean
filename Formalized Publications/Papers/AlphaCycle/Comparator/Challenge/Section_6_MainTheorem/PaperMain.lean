import Challenge.Section_2_Preliminaries.PaperHypergraph
import Challenge.Section_2_Preliminaries.GeometryCycle
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

noncomputable section
namespace AlphaCycle.PaperHypergraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distinguished relaxation in the actual paper coordinate space. -/
def cycleDistinguishedRelaxation (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) : Set (ofThree e hc hv).completion.Vector :=
  cycleCoordinates e hc hv ⁻¹'
    AlphaCycle.distinguishedRelaxation e (Geometry.distinguishedCycle e hc)

/-- The all-cycle relaxation in the actual paper coordinate space. -/
def cycleAllRelaxation (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) : Set (ofThree e hc hv).completion.Vector :=
  cycleCoordinates e hc hv ⁻¹' AlphaCycle.allCycleRelaxation e


/-- The final three-way equivalence, in exactly the paper's vertex and edge coordinates. -/
theorem paper_sharp_classification (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    ((Geometry.blockA e).card = 1 ∧ (Geometry.blockB e).card = 1 ∧
      (Geometry.blockC e).card = 1 ↔
      cycleDistinguishedRelaxation e hc hv = (ofThree e hc hv).completion.polytope) ∧
    ((Geometry.blockA e).card = 1 ∧ (Geometry.blockB e).card = 1 ∧
      (Geometry.blockC e).card = 1 ↔
      cycleAllRelaxation e hc hv = (ofThree e hc hv).completion.polytope) := by sorry

end AlphaCycle.PaperHypergraph
