import Challenge.Section_2_Preliminaries.Polytope
import Challenge.Section_2_Preliminaries.Triangle
import Mathlib.Data.Finset.SymmDiff
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

namespace AlphaCycle
open Classical
open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
 theorem completedSupport_downward (e : Fin 3 → Finset V)
    {s t : Finset V} (ht : t ∈ completedSupport e) (hst : s ⊆ t) :
    s ∈ completedSupport e := by
  obtain ⟨i, hi⟩ := (mem_completedSupport e t).mp ht
  exact (mem_completedSupport e s).mpr ⟨i, hst.trans hi⟩
/-- A monomial occurring in the signed switching expansion remains supported. -/
 theorem switch_term_supported (e : Fin 3 → Finset V) (u : Finset V)
    (s : {s // s ∈ completedSupport e})
    (w : {w // w ∈ (s.val ∩ u).powerset}) :
    (s.val \ u) ∪ w.val ∈ completedSupport e := by
  apply completedSupport_downward e s.property
  apply Finset.union_subset
  · exact Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp w.property).trans Finset.inter_subset_left
/-- The paper's signed subset formula for switching moment coordinates. -/
noncomputable def switchVector (e : Fin 3 → Finset V) (u : Finset V)
    (z : MomentVector (completedSupport e)) : MomentVector (completedSupport e) :=
  fun s => ∑ w : {w // w ∈ (s.val ∩ u).powerset},
    (-1 : ℝ) ^ w.val.card * z ⟨(s.val \ u) ∪ w.val, switch_term_supported e u s w⟩
/-- Supported no-private triples, with the paper's global alpha-cycle condition. -/
structure SupportedCycle (e : Fin 3 → Finset V) where
  edge : Fin 3 → Finset V
  supported : ∀ i, edge i ∈ completedSupport e
  noPrivate : Triangle.NoPrivate (edge 0) (edge 1) (edge 2)
  incomparable : ∀ i j, i ≠ j → ¬ edge i ⊆ edge j
  alpha : ∀ i, ¬ ((edge 0 ∩ edge 1) ∪ (edge 1 ∩ edge 2) ∪
    (edge 0 ∩ edge 2) ⊆ e i)
/-- The generalized triangle inequalities for a supported triple. -/
def generalizedTriangle (e : Fin 3 → Finset V)
    (f : Fin 3 → Finset V) (hf : ∀ i, f i ∈ completedSupport e)
    (z : MomentVector (completedSupport e)) : Prop :=
  Triangle.GT
    (z ⟨f 0 ∩ f 1 ∩ f 2, completedSupport_downward e (hf 0)
      (Finset.inter_subset_left.trans Finset.inter_subset_left)⟩)
    (z ⟨f 0 ∩ f 1, completedSupport_downward e (hf 0) Finset.inter_subset_left⟩)
    (z ⟨f 1 ∩ f 2, completedSupport_downward e (hf 1) Finset.inter_subset_left⟩)
    (z ⟨f 0 ∩ f 2, completedSupport_downward e (hf 0) Finset.inter_subset_left⟩)
    (z ⟨f 1, hf 1⟩) (z ⟨f 0, hf 0⟩) (z ⟨f 2, hf 2⟩)
/-- The all-cycle relaxation, including every switching of every relevant
supported no-private alpha-cycle inequality. -/
def allCycleRelaxation (e : Fin 3 → Finset V) :
    Set (MomentVector (completedSupport e)) :=
  {z | z ∈ completeEdgeRelaxation e ∧ ∀ f : SupportedCycle e, ∀ u : Finset V,
    generalizedTriangle e f.edge f.supported (switchVector e u z)}
/-- The relaxation for one distinguished reduced cycle. -/
def distinguishedRelaxation (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    Set (MomentVector (completedSupport e)) :=
  {z | z ∈ completeEdgeRelaxation e ∧ ∀ u : Finset V,
    generalizedTriangle e f.edge f.supported (switchVector e u z)}

end AlphaCycle
