import Section_2_Preliminaries.Polytope

/-! Constructing the common coordinate vector from compatible local laws. -/
noncomputable section
namespace AlphaCycle
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A canonical choice of containing edge defines every supported coordinate. -/
def localMomentVector (e : Fin 3 → Finset V) (μ : Fin 3 → BooleanLaw V) :
    MomentVector (completedSupport e) := fun s =>
  moment (μ (Classical.choose ((mem_completedSupport e s.val).mp s.property))) s.val

/-- Consistency makes the choice of containing edge immaterial. -/
theorem localMomentVector_eq (e : Fin 3 → Finset V) (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i j, restrictLaw (μ i) (e i ∩ e j) = restrictLaw (μ j) (e i ∩ e j))
    (i : Fin 3) (s : Finset V) (hs : s ⊆ e i) :
    moment (μ i) s = localMomentVector e μ ⟨s, mem_completedSupport_of_subset e i s hs⟩ := by
  classical
  let j := Classical.choose ((mem_completedSupport e s).mp
    (mem_completedSupport_of_subset e i s hs))
  have hj : s ⊆ e j := Classical.choose_spec ((mem_completedSupport e s).mp
    (mem_completedSupport_of_subset e i s hs))
  have hsij : s ⊆ e i ∩ e j := Finset.subset_inter hs hj
  have hm := congrArg (fun ν => moment ν s) (hμ i j)
  change moment (μ i) s = moment (μ j) s
  simpa only [moment_restrict _ _ _ hsij] using hm

theorem localMomentVector_mem_completeEdgeRelaxation (e : Fin 3 → Finset V)
    (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i j, restrictLaw (μ i) (e i ∩ e j) = restrictLaw (μ j) (e i ∩ e j)) :
    localMomentVector e μ ∈ completeEdgeRelaxation e := by
  intro i
  exact ⟨μ i, localMomentVector_eq e μ hμ i⟩

theorem localMomentVector_not_mem_multilinearPolytope (e : Fin 3 → Finset V)
    (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i j, restrictLaw (μ i) (e i ∩ e j) = restrictLaw (μ j) (e i ∩ e j))
    (hn : ¬ ∃ ν : BooleanLaw V, ∀ i, restrictLaw ν (e i) = restrictLaw (μ i) (e i)) :
    localMomentVector e μ ∉ multilinearPolytope (completedSupport e) := by
  exact fun hz => hn ((mem_multilinearPolytope_iff_realizes e _ μ
    (localMomentVector_eq e μ hμ)).mp hz)

end AlphaCycle
