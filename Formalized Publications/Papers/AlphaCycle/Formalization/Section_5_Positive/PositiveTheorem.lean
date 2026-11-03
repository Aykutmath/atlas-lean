import Section_5_Positive.Singleton
import Section_1_Introduction.Geometry
import Section_2_Preliminaries.SetGluing
import Section_2_Preliminaries.Polytope
import Section_2_Preliminaries.GeometryCycle
import Section_5_Positive.SliceBridge

/-! Geometric integration of the singleton slice theorem and private-block gluing. -/
noncomputable section

namespace AlphaCycle

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Full consistency of the three maximal-edge witnesses gives the core family
required by the singleton slice construction. -/
theorem singleton_core_consistent (e : Fin 3 → Finset V) (a b c : V)
    (hA : Geometry.blockA e = {a}) (hB : Geometry.blockB e = {b})
    (hC : Geometry.blockC e = {c}) (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i j, restrictLaw (μ i) (e i ∩ e j) = restrictLaw (μ j) (e i ∩ e j)) :
    (Singleton.coreFamily (Geometry.common e) a b c (μ 1) (μ 0) (μ 2)).Consistent := by
  apply Singleton.core_consistent
  · have h := (hμ 0 1).symm
    simpa only [Geometry.overlap01, hA] using h
  · have h := hμ 1 2
    simpa only [Geometry.overlap12, hB] using h
  · have h := hμ 0 2
    simpa only [Geometry.overlap02, hC] using h

/-- Slice feasibility on the common block suffices to realize the full three
maximal-edge laws, regardless of the private blocks. -/
theorem singleton_realization_of_slices (e : Fin 3 → Finset V) (a b c : V)
    (hA : Geometry.blockA e = {a}) (hB : Geometry.blockB e = {b})
    (hC : Geometry.blockC e = {c})
    (ha : a ∉ Geometry.common e) (hb : b ∉ Geometry.common e)
    (hc : c ∉ Geometry.common e) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i j, restrictLaw (μ i) (e i ∩ e j) = restrictLaw (μ j) (e i ∩ e j))
    (htri : Positive.TriangleConditions (Positive.ofCoreFamily
      (Singleton.coreFamily (Geometry.common e) a b c (μ 1) (μ 0) (μ 2))
      (singleton_core_consistent e a b c hA hB hC μ hμ))) :
    ∃ ν : BooleanLaw V, ∀ i, restrictLaw ν (e i) = restrictLaw (μ i) (e i) := by
  have hoa : restrictLaw (μ 1) (Geometry.common e ∪ {a}) =
      restrictLaw (μ 0) (Geometry.common e ∪ {a}) := by
    simpa only [Geometry.overlap01, hA] using (hμ 0 1).symm
  have hob : restrictLaw (μ 1) (Geometry.common e ∪ {b}) =
      restrictLaw (μ 2) (Geometry.common e ∪ {b}) := by
    simpa only [Geometry.overlap12, hB] using hμ 1 2
  have hoc : restrictLaw (μ 0) (Geometry.common e ∪ {c}) =
      restrictLaw (μ 2) (Geometry.common e ∪ {c}) := by
    simpa only [Geometry.overlap02, hC] using hμ 0 2
  obtain ⟨ν, hνab, hνac, hνbc⟩ := Singleton.extension (Geometry.common e) a b c
    ha hb hc hab hac hbc (μ 1) (μ 0) (μ 2) hoa hob hoc htri
  have hred₀ : restrictLaw ν (Geometry.core e ∩ e 0) =
      restrictLaw (μ 0) (Geometry.core e ∩ e 0) := by
    simpa only [Geometry.reduced0, hA, hC, Finset.union_assoc, Finset.singleton_union] using hνac
  have hred₁ : restrictLaw ν (Geometry.core e ∩ e 1) =
      restrictLaw (μ 1) (Geometry.core e ∩ e 1) := by
    simpa only [Geometry.reduced1, hA, hB, Finset.union_assoc, Finset.singleton_union] using hνab
  have hred₂ : restrictLaw ν (Geometry.core e ∩ e 2) =
      restrictLaw (μ 2) (Geometry.core e ∩ e 2) := by
    simpa only [Geometry.reduced2, hB, hC, Finset.union_assoc, Finset.singleton_union] using hνbc
  obtain ⟨ρ, hρ₀, hρ₁, hρ₂⟩ := restore_private_on_sets (Geometry.core e) (e 0) (e 1) (e 2)
    ν (μ 0) (μ 1) (μ 2) (Geometry.overlaps_subset_core e).1
    (Geometry.overlaps_subset_core e).2.1 (Geometry.overlaps_subset_core e).2.2 hred₀ hred₁ hred₂
  refine ⟨ρ, ?_⟩
  intro i
  fin_cases i
  · exact hρ₀
  · exact hρ₁
  · exact hρ₂

/-- The distinguished cycle relaxation is exact when every pair-only block is
a singleton.  This is an equality with the actual convex hull of monomial lifts. -/
theorem distinguished_exact_of_singletons (e : Fin 3 → Finset V)
    (hcycle : Geometry.IsCycle e) (hs : Geometry.Singletons e) :
    distinguishedRelaxation e (Geometry.distinguishedCycle e hcycle) =
      multilinearPolytope (completedSupport e) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨μ, hμ, hcons⟩ := (mem_completeEdgeRelaxation_iff_consistent e z).1 hz.1
    obtain ⟨a, b, c, hA, hB, hC, hab, hac, hbc, ha, hb, hc⟩ :=
      Geometry.singleton_vertices e hs
    have h₀ : (Geometry.distinguishedCycle e hcycle).edge 0 =
        Geometry.common e ∪ {a, c} := by
      simp only [Geometry.distinguishedCycle, Geometry.reduced, Geometry.reduced0,
        hA, hC, Finset.union_assoc, Finset.singleton_union]
    have h₁ : (Geometry.distinguishedCycle e hcycle).edge 1 =
        Geometry.common e ∪ {a, b} := by
      simp only [Geometry.distinguishedCycle, Geometry.reduced, Geometry.reduced1,
        hA, hB, Finset.union_assoc, Finset.singleton_union]
    have h₂ : (Geometry.distinguishedCycle e hcycle).edge 2 =
        Geometry.common e ∪ {b, c} := by
      simp only [Geometry.distinguishedCycle, Geometry.reduced, Geometry.reduced2,
        hB, hC, Finset.union_assoc, Finset.singleton_union]
    have hparent : ∀ i, (Geometry.distinguishedCycle e hcycle).edge i ⊆ e i :=
      fun _ => Finset.inter_subset_right
    have hcore := singleton_core_consistent e a b c hA hB hC μ hcons
    have htri := SliceBridge.triangleConditions_of_distinguished e
      (Geometry.distinguishedCycle e hcycle) z hz μ hμ (Geometry.common e) a b c
      ha hb hc hab hac hbc h₀ h₁ h₂ hparent hcore
    apply (mem_multilinearPolytope_iff_realizes e z μ hμ).2
    exact singleton_realization_of_slices e a b c hA hB hC ha hb hc hab hac hbc μ hcons htri
  · exact (multilinearPolytope_subset_allCycleRelaxation e).trans
      (allCycleRelaxation_subset_distinguishedRelaxation e (Geometry.distinguishedCycle e hcycle))

/-- Exactness also holds for the stronger all-cycle relaxation. -/
theorem allCycle_exact_of_singletons (e : Fin 3 → Finset V)
    (hcycle : Geometry.IsCycle e) (hs : Geometry.Singletons e) :
    allCycleRelaxation e = multilinearPolytope (completedSupport e) := by
  apply Set.Subset.antisymm
  · intro z hz
    have hd := allCycleRelaxation_subset_distinguishedRelaxation e
      (Geometry.distinguishedCycle e hcycle) hz
    rwa [distinguished_exact_of_singletons e hcycle hs] at hd
  · exact multilinearPolytope_subset_allCycleRelaxation e

end AlphaCycle
