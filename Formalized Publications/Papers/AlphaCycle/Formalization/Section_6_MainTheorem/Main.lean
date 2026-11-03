import Section_5_Positive.PositiveTheorem
import Section_4_Negative.NegativeTheorem

/-!
# Sharp classification for completed length-three alpha-cycles

`Geometry.IsCycle` says that the three pair-only blocks are nonempty.
`Geometry.Singletons` says that all three have cardinality exactly one.
The ambient moment space is the completed support (including the fixed empty
coordinate), and `multilinearPolytope` is the actual convex hull of Boolean
monomial vectors. Both relaxations use the paper's signed switching formula.
-/
namespace AlphaCycle
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distinguished-cycle relaxation is exact if and only if all three
pair-only blocks have cardinality one. -/
theorem distinguished_exact_iff (e : Fin 3 → Finset V) (he : Geometry.IsCycle e) :
    distinguishedRelaxation e (Geometry.distinguishedCycle e he) =
      multilinearPolytope (completedSupport e) ↔ Geometry.Singletons e := by
  constructor
  · intro hexact
    by_contra hn
    obtain ⟨z, hz, hnz⟩ := counterexample_of_not_singletons e he hn
    apply hnz
    rw [← hexact]
    exact allCycleRelaxation_subset_distinguishedRelaxation e (Geometry.distinguishedCycle e he) hz
  · exact distinguished_exact_of_singletons e he

/-- Even imposing every switched no-private subcycle inequality is exact if and
only if all three pair-only blocks have cardinality one. -/
theorem allCycle_exact_iff (e : Fin 3 → Finset V) (he : Geometry.IsCycle e) :
    allCycleRelaxation e = multilinearPolytope (completedSupport e) ↔ Geometry.Singletons e := by
  constructor
  · intro hexact
    by_contra hn
    obtain ⟨z, hz, hnz⟩ := counterexample_of_not_singletons e he hn
    exact hnz (hexact ▸ hz)
  · exact allCycle_exact_of_singletons e he

/-- The main sharp classification theorem, with the cardinalities exposed. -/
theorem sharp_classification (e : Fin 3 → Finset V) (he : Geometry.IsCycle e) :
    (((Geometry.blockA e).card = 1 ∧ (Geometry.blockB e).card = 1 ∧
      (Geometry.blockC e).card = 1) ↔
      distinguishedRelaxation e (Geometry.distinguishedCycle e he) =
        multilinearPolytope (completedSupport e)) ∧
    (((Geometry.blockA e).card = 1 ∧ (Geometry.blockB e).card = 1 ∧
      (Geometry.blockC e).card = 1) ↔
      allCycleRelaxation e = multilinearPolytope (completedSupport e)) :=
  ⟨(distinguished_exact_iff e he).symm, (allCycle_exact_iff e he).symm⟩

/-- The explicit strict-gap conclusion in the paper. -/
theorem allCycle_gap_nonempty (e : Fin 3 → Finset V) (he : Geometry.IsCycle e)
    (hlarge : 2 ≤ (Geometry.blockA e).card ∨ 2 ≤ (Geometry.blockB e).card ∨
      2 ≤ (Geometry.blockC e).card) :
    (allCycleRelaxation e \ multilinearPolytope (completedSupport e)).Nonempty := by
  obtain ⟨z,hz,hn⟩ := counterexample_of_large_block e he hlarge
  exact ⟨z,hz,hn⟩

end AlphaCycle
