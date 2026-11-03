import Challenge.Section_2_Preliminaries.Polytope
import Challenge.Section_2_Preliminaries.DefinitionAudit
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

/-! Exact coordinate interfaces for the finite hypergraphs used in the paper. -/
namespace AlphaCycle
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The paper's squarefree monomial, including the empty monomial. -/
def paperMonomial (s : Finset V) (x : V → ℝ) : ℝ := ∏ v ∈ s, x v
/-- Finite hypergraphs in the paper have no isolated vertices and no edges of size below two. -/
@[ext] structure PaperHypergraph (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Finset V)
  edge_card : ∀ e ∈ edges, 2 ≤ e.card
  covers : ∀ v : V, ∃ e ∈ edges, v ∈ e
namespace PaperHypergraph
variable (H : PaperHypergraph V)
/-- Completion as hyperedges, excluding the empty set and singletons. -/
def completionEdges : Finset (Finset V) :=
  H.edges.biUnion (fun e => e.powerset.filter (fun f => 2 ≤ f.card))
@[simp] theorem mem_completionEdges (f : Finset V) :
    f ∈ H.completionEdges ↔ 2 ≤ f.card ∧ ∃ e ∈ H.edges, f ⊆ e := by
  simp only [completionEdges, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  aesop
 theorem edges_subset_completionEdges : H.edges ⊆ H.completionEdges := by
  intro e he
  exact (H.mem_completionEdges e).mpr ⟨H.edge_card e he, e, he, Finset.Subset.refl _⟩
/-- Completion is itself a hypergraph under precisely the paper's conventions. -/
def completion : PaperHypergraph V where
  edges := H.completionEdges
  edge_card e he := ((H.mem_completionEdges e).mp he).1
  covers v := by
    obtain ⟨e, he, hv⟩ := H.covers v
    exact ⟨e, H.edges_subset_completionEdges he, hv⟩
/-- Literal vertex-plus-edge indexing avoids identifying vertices with sets. -/
abbrev Coordinate := V ⊕ {e // e ∈ H.edges}
abbrev Vector := H.Coordinate → ℝ
/-- The paper's binary monomial set `MS(H)`. -/
def multilinearSet : Set H.Vector :=
  {z | (∀ c, z c = 0 ∨ z c = 1) ∧
    ∀ e, z (Sum.inr e) = paperMonomial e.val (fun v => z (Sum.inl v))}
/-- The paper's `MP(H)`, in its literal vertex-plus-edge coordinates. -/
def polytope : Set H.Vector := convexHull ℝ H.multilinearSet
/-- Coordinate support used by the existing development, including bookkeeping `∅`. -/
def coordinateSupport : Finset (Finset V) :=
  insert ∅ ((Finset.univ.image (fun v : V => {v})) ∪ H.edges)
@[simp] theorem mem_coordinateSupport (s : Finset V) :
    s ∈ H.coordinateSupport ↔ s = ∅ ∨ (∃ v : V, s = {v}) ∨ s ∈ H.edges := by
  simp [coordinateSupport, eq_comm]
/-- Restore the empty coordinate to one and relabel the vertex coordinates. -/
noncomputable def fromPaper (z : H.Vector) : MomentVector H.coordinateSupport := fun s =>
  if h0 : s.val = ∅ then 1
  else if he : s.val ∈ H.edges then z (Sum.inr ⟨s.val, he⟩)
  else z (Sum.inl (Classical.choose
    ((((H.mem_coordinateSupport s.val).mp s.property).resolve_left h0).resolve_right he)))
/-- A three-edge generating hypergraph with exactly its covered vertices. -/
def ofThree (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) : PaperHypergraph V where
  edges := Finset.univ.image e
  edge_card s hs := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hc.two_le_card i
  covers v := by
    obtain ⟨i, hi⟩ := hv v
    exact ⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩

end PaperHypergraph
end AlphaCycle
