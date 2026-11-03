import Section_2_Preliminaries.PaperHypergraph
import Section_2_Preliminaries.PaperTriangles
import Section_6_MainTheorem.Main

/-! The classification transported to the paper's literal vertex-plus-edge
coordinate space. The coordinate equivalence fixes the empty moment to one. -/
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

/-- Pullback notation is exactly the paper's CER intersected with the
distinguished switched inequalities. -/
theorem cycleDistinguishedRelaxation_eq_inter (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    cycleDistinguishedRelaxation e hc hv =
      (ofThree e hc hv).completion.completeEdgeRelaxation ∩
      {z | ∀ U : Finset V, generalizedTriangle e (Geometry.reduced e)
        (Geometry.distinguishedCycle e hc).supported
        (switchVector e U (cycleCoordinates e hc hv z))} := by
  ext z
  exact and_congr (ofThree_mem_completeEdgeRelaxation_iff e hc hv z).symm Iff.rfl

/-- The all-cycle pullback is exactly CER plus every applicable switched inequality. -/
theorem cycleAllRelaxation_eq_inter (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    cycleAllRelaxation e hc hv =
      (ofThree e hc hv).completion.completeEdgeRelaxation ∩
      {z | ∀ f : SupportedCycle e, ∀ U : Finset V,
        generalizedTriangle e f.edge f.supported
          (switchVector e U (cycleCoordinates e hc hv z))} := by
  ext z
  exact and_congr (ofThree_mem_completeEdgeRelaxation_iff e hc hv z).symm Iff.rfl

theorem cycle_relaxation_inclusions (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    (ofThree e hc hv).completion.polytope ⊆ cycleAllRelaxation e hc hv ∧
    cycleAllRelaxation e hc hv ⊆ cycleDistinguishedRelaxation e hc hv ∧
    cycleDistinguishedRelaxation e hc hv ⊆
      (ofThree e hc hv).completion.completeEdgeRelaxation := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact multilinearPolytope_subset_allCycleRelaxation e
      ((ofThree_mem_polytope_iff e hc hv z).mp hz)
  · intro z hz
    exact allCycleRelaxation_subset_distinguishedRelaxation e
      (Geometry.distinguishedCycle e hc) hz
  · intro z hz
    exact (ofThree_mem_completeEdgeRelaxation_iff e hc hv z).mpr hz.1

/-- The explicit strict gap also exists in `ℝ^(V ⊕ E)`, with no bookkeeping coordinate. -/
theorem cycle_all_gap_nonempty (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i)
    (hlarge : 2 ≤ (Geometry.blockA e).card ∨ 2 ≤ (Geometry.blockB e).card ∨
      2 ≤ (Geometry.blockC e).card) :
    (cycleAllRelaxation e hc hv \ (ofThree e hc hv).completion.polytope).Nonempty := by
  obtain ⟨z, hz, hn⟩ := AlphaCycle.allCycle_gap_nonempty e hc hlarge
  obtain ⟨μ, hμ⟩ := hz.1 0
  have h0 : z ⟨∅, mem_completedSupport_of_subset e 0 ∅ (Finset.empty_subset _)⟩ = 1 := by
    rw [← hμ ∅ (Finset.empty_subset _), moment_empty]
  have hcoord := cycleCoordinates_cycleFromMoment e hc hv z h0
  refine ⟨cycleFromMoment e hc hv z, ?_, ?_⟩
  · change cycleCoordinates e hc hv (cycleFromMoment e hc hv z) ∈
      AlphaCycle.allCycleRelaxation e
    rwa [hcoord]
  · intro hp
    apply hn
    have hh := (ofThree_mem_polytope_iff e hc hv _).mp hp
    rwa [hcoord] at hh

/-- The final three-way equivalence, in exactly the paper's vertex and edge coordinates. -/
theorem paper_sharp_classification (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    ((Geometry.blockA e).card = 1 ∧ (Geometry.blockB e).card = 1 ∧
      (Geometry.blockC e).card = 1 ↔
      cycleDistinguishedRelaxation e hc hv = (ofThree e hc hv).completion.polytope) ∧
    ((Geometry.blockA e).card = 1 ∧ (Geometry.blockB e).card = 1 ∧
      (Geometry.blockC e).card = 1 ↔
      cycleAllRelaxation e hc hv = (ofThree e hc hv).completion.polytope) := by
  have hpos (hs : Geometry.Singletons e) :
      cycleDistinguishedRelaxation e hc hv = (ofThree e hc hv).completion.polytope ∧
      cycleAllRelaxation e hc hv = (ofThree e hc hv).completion.polytope := by
    constructor
    · ext z
      change cycleCoordinates e hc hv z ∈ AlphaCycle.distinguishedRelaxation e
        (Geometry.distinguishedCycle e hc) ↔ _
      rw [(AlphaCycle.distinguished_exact_iff e hc).mpr hs]
      exact (ofThree_mem_polytope_iff e hc hv z).symm
    · ext z
      change cycleCoordinates e hc hv z ∈ AlphaCycle.allCycleRelaxation e ↔ _
      rw [(AlphaCycle.allCycle_exact_iff e hc).mpr hs]
      exact (ofThree_mem_polytope_iff e hc hv z).symm
  have hneg (hn : ¬ Geometry.Singletons e) :
      cycleDistinguishedRelaxation e hc hv ≠ (ofThree e hc hv).completion.polytope ∧
      cycleAllRelaxation e hc hv ≠ (ofThree e hc hv).completion.polytope := by
    obtain ⟨z, hz, hmp⟩ := cycle_all_gap_nonempty e hc hv
      (Geometry.not_singletons_has_large e hc hn)
    constructor
    · intro heq
      apply hmp
      rw [← heq]
      exact (cycle_relaxation_inclusions e hc hv).2.1 hz
    · intro heq
      exact hmp (heq ▸ hz)
  constructor <;> constructor
  · intro hs; exact (hpos hs).1
  · intro heq
    by_contra hn
    exact (hneg hn).1 heq
  · intro hs; exact (hpos hs).2
  · intro heq
    by_contra hn
    exact (hneg hn).2 heq

end AlphaCycle.PaperHypergraph
