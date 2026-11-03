import Section_6_MainTheorem.Main

/-! Concrete checks of the sharp classification.  The graph triangle is exact;
the completed four-variable parity example has a strict all-cycle gap. -/

namespace AlphaCycle.Examples

/-- The ordinary graph triangle on three vertices. -/
def graphTriangle : Fin 3 → Finset (Fin 3) := ![{0, 2}, {0, 1}, {1, 2}]

theorem graphTriangle_isCycle : Geometry.IsCycle graphTriangle := by
  unfold Geometry.IsCycle
  decide

theorem graphTriangle_singletons : Geometry.Singletons graphTriangle := by
  unfold Geometry.Singletons
  decide

/-- The familiar three-variable triangle inequalities give the full convex hull. -/
theorem graphTriangle_distinguished_exact :
    distinguishedRelaxation graphTriangle
      (Geometry.distinguishedCycle graphTriangle graphTriangle_isCycle) =
      multilinearPolytope (completedSupport graphTriangle) :=
  (distinguished_exact_iff graphTriangle graphTriangle_isCycle).2 graphTriangle_singletons

theorem graphTriangle_allCycle_exact :
    allCycleRelaxation graphTriangle = multilinearPolytope (completedSupport graphTriangle) :=
  (allCycle_exact_iff graphTriangle graphTriangle_isCycle).2 graphTriangle_singletons

/-- The smallest obstruction: completed edges `012`, `013`, and `23`. -/
def parityFour : Fin 3 → Finset (Fin 4) := ![{0, 1, 2}, {0, 1, 3}, {2, 3}]

theorem parityFour_isCycle : Geometry.IsCycle parityFour := by
  unfold Geometry.IsCycle
  decide

theorem parityFour_blockA : Geometry.blockA parityFour = {0, 1} := by decide

theorem parityFour_large : 2 ≤ (Geometry.blockA parityFour).card := by decide

/-- All switchings of all supported no-private alpha-cycles leave a strict gap
already on the four-variable example. -/
theorem parityFour_gap :
    (allCycleRelaxation parityFour \ multilinearPolytope (completedSupport parityFour)).Nonempty :=
  allCycle_gap_nonempty parityFour parityFour_isCycle (Or.inl parityFour_large)

/-- The larger relaxation for the distinguished cycle also has a strict gap. -/
theorem parityFour_distinguished_gap :
    (distinguishedRelaxation parityFour
      (Geometry.distinguishedCycle parityFour parityFour_isCycle) \
      multilinearPolytope (completedSupport parityFour)).Nonempty := by
  obtain ⟨z, hz, hn⟩ := parityFour_gap
  exact ⟨z, allCycleRelaxation_subset_distinguishedRelaxation parityFour
    (Geometry.distinguishedCycle parityFour parityFour_isCycle) hz, hn⟩

end AlphaCycle.Examples
