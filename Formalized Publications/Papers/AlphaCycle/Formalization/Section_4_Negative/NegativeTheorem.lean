import Section_4_Negative.NegativeSwitched
import Section_2_Preliminaries.Reindex

/-! A concrete point in the all-cycle relaxation outside the actual multilinear
polytope whenever one pair-only block has at least two vertices. -/
noncomputable section
namespace AlphaCycle
open NegativeVertex
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The explicit parity witness proves nonexactness when the first pair-only
block has at least two vertices. Extra common and private vertices are fixed to one. -/
theorem counterexample_of_large_A (e : Fin 3 → Finset V) (he : Geometry.IsCycle e)
    (hA : 2 ≤ (Geometry.blockA e).card) :
    ∃ z : MomentVector (completedSupport e),
      z ∈ allCycleRelaxation e ∧ z ∉ multilinearPolytope (completedSupport e) := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hA
  obtain ⟨b, hb⟩ := he.2.1
  obtain ⟨c, hc⟩ := he.2.2
  simp only [Geometry.blockA, Geometry.blockB, Geometry.blockC,
    Finset.mem_sdiff, Finset.mem_inter] at hu hv hb hc
  have hub : u ≠ b := fun h => hb.2 (h ▸ hu.1.1)
  have huc : u ≠ c := fun h => hc.2 (h ▸ hu.1.2)
  have hvb : v ≠ b := fun h => hb.2 (h ▸ hv.1.1)
  have hvc : v ≠ c := fun h => hc.2 (h ▸ hv.1.2)
  have hbc : b ≠ c := fun h => hc.2 (h ▸ hb.1.1)
  refine ⟨witness e u v b c,
    witness_in_allCycleRelaxation e u v b c huv hu.2 hv.2 hb.2 hc.2, ?_⟩
  exact localMomentVector_not_mem_multilinearPolytope e (locals u v b c)
    (locals_consistent e u v b c hu.2 hv.2 hb.2 hc.2)
    (locals_not_realizable e u v b c huv hub huc hvb hvc hbc
      hu.1.1 hv.1.1 hc.1.1 hu.1.2 hv.1.2 hb.1.1 hb.1.2 hc.1.2)

/-- The same obstruction works in any of the three pair-only blocks. -/
theorem counterexample_of_large_block (e : Fin 3 → Finset V) (he : Geometry.IsCycle e)
    (hlarge : 2 ≤ (Geometry.blockA e).card ∨ 2 ≤ (Geometry.blockB e).card ∨
      2 ≤ (Geometry.blockC e).card) :
    ∃ z : MomentVector (completedSupport e),
      z ∈ allCycleRelaxation e ∧ z ∉ multilinearPolytope (completedSupport e) := by
  rcases hlarge with hA | hB | hC
  · exact counterexample_of_large_A e he hA
  · apply Reindex.counterexample e (Equiv.swap 0 2)
    apply counterexample_of_large_A _ (Reindex.cycle_swap02 e he)
    rwa [Reindex.blockA_swap02]
  · apply Reindex.counterexample e (Equiv.swap 1 2)
    apply counterexample_of_large_A _ (Reindex.cycle_swap12 e he)
    rwa [Reindex.blockA_swap12]

/-- Failure of the singleton condition gives a witness, not just failure of equality. -/
theorem counterexample_of_not_singletons (e : Fin 3 → Finset V) (he : Geometry.IsCycle e)
    (hn : ¬ Geometry.Singletons e) :
    ∃ z : MomentVector (completedSupport e),
      z ∈ allCycleRelaxation e ∧ z ∉ multilinearPolytope (completedSupport e) :=
  counterexample_of_large_block e he (Geometry.not_singletons_has_large e he hn)

end AlphaCycle
