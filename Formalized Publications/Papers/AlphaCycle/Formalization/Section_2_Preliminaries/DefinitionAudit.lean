import Section_1_Introduction.Geometry
import Section_2_Preliminaries.CyclePermutation

/-! Kernel-checked comparison of the finite definitions with the paper's
length-three alpha-cycle definition. -/
namespace AlphaCycle
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Geometry

lemma core_sdiff0 (e : Fin 3 → Finset V) : core e \ e 0 = blockB e := by
  ext v
  simp only [core, blockB, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

lemma core_sdiff1 (e : Fin 3 → Finset V) : core e \ e 1 = blockC e := by
  ext v
  simp only [core, blockC, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

lemma core_sdiff2 (e : Fin 3 → Finset V) : core e \ e 2 = blockA e := by
  ext v
  simp only [core, blockA, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto

/-- Nonempty pair-only blocks are exactly the length-three global condition. -/
theorem isCycle_iff_core_not_subset (e : Fin 3 → Finset V) :
    IsCycle e ↔ ∀ i, ¬ core e ⊆ e i := by
  constructor
  · intro h i
    fin_cases i
    · change ¬ core e ⊆ e 0
      exact Finset.sdiff_nonempty.mp (by rw [core_sdiff0 e]; exact h.2.1)
    · change ¬ core e ⊆ e 1
      exact Finset.sdiff_nonempty.mp (by rw [core_sdiff1 e]; exact h.2.2)
    · change ¬ core e ⊆ e 2
      exact Finset.sdiff_nonempty.mp (by rw [core_sdiff2 e]; exact h.1)
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa only [← Finset.sdiff_nonempty, core_sdiff2] using h 2
    · simpa only [← Finset.sdiff_nonempty, core_sdiff0] using h 0
    · simpa only [← Finset.sdiff_nonempty, core_sdiff1] using h 1

/-- The global alpha condition already forces the three generators to be
pairwise incomparable. Hence they are exactly the maximal completed edges. -/
theorem IsCycle.incomparable {e : Fin 3 → Finset V} (h : IsCycle e)
    (i j : Fin 3) (hij : i ≠ j) : ¬ e i ⊆ e j := by
  intro he
  apply isCycle_iff_core_not_subset e |>.mp h j
  exact (intersections_subset_two e i j hij).trans
    (Finset.union_subset he (Finset.Subset.refl _))

/-- Exact agreement with the two defining conditions quoted in the paper. -/
theorem isCycle_iff_alpha (e : Fin 3 → Finset V) :
    IsCycle e ↔
      (∀ i j, i ≠ j → ¬ e i ⊆ e j) ∧ (∀ i, ¬ core e ⊆ e i) := by
  constructor
  · intro h
    exact ⟨h.incomparable, (isCycle_iff_core_not_subset e).mp h⟩
  · intro h
    exact (isCycle_iff_core_not_subset e).mpr h.2

/-- The parent-edge test is equivalent to testing every completed subset. -/
theorem core_not_subset_completed_iff (e : Fin 3 → Finset V) :
    (∀ i, ¬ core e ⊆ e i) ↔
      ∀ s ∈ completedSupport e, ¬ core e ⊆ s := by
  constructor
  · intro h s hs hsub
    obtain ⟨i, hi⟩ := (mem_completedSupport e s).mp hs
    exact h i (hsub.trans hi)
  · intro h i
    exact h (e i) (mem_completedSupport_of_subset e i (e i) (Finset.Subset.refl _))

/-- Each edge of a length-three alpha-cycle has at least two vertices. -/
theorem IsCycle.two_le_card {e : Fin 3 → Finset V} (h : IsCycle e) (i : Fin 3) :
    2 ≤ (e i).card := by
  obtain ⟨a, ha⟩ := h.1
  obtain ⟨b, hb⟩ := h.2.1
  obtain ⟨c, hc⟩ := h.2.2
  simp only [blockA, blockB, blockC, Finset.mem_sdiff, Finset.mem_inter] at ha hb hc
  have hab : a ≠ b := by intro he; subst b; exact hb.2 ha.1.1
  have hac : a ≠ c := by intro he; subst c; exact hc.2 ha.1.2
  have hbc : b ≠ c := by intro he; subst c; exact hb.2 hc.1.1
  fin_cases i
  · exact Finset.one_lt_card.mpr ⟨a, ha.1.1, c, hc.1.1, hac⟩
  · exact Finset.one_lt_card.mpr ⟨a, ha.1.2, b, hb.1.1, hab⟩
  · exact Finset.one_lt_card.mpr ⟨b, hb.1.2, c, hc.1.2, hbc⟩

end Geometry

/-- SupportedCycle's inclusion of all monomial coordinates does not introduce
empty or singleton hyperedges into its alpha-cycles. -/
theorem SupportedCycle.isCycle {e : Fin 3 → Finset V} (f : SupportedCycle e) :
    Geometry.IsCycle f.edge := by
  apply (Geometry.isCycle_iff_core_not_subset f.edge).mpr
  intro i hi
  obtain ⟨j, hj⟩ := (mem_completedSupport e (f.edge i)).mp (f.supported i)
  exact f.alpha j (hi.trans hj)

 theorem SupportedCycle.two_le_card {e : Fin 3 → Finset V} (f : SupportedCycle e)
    (i : Fin 3) : 2 ≤ (f.edge i).card :=
  f.isCycle.two_le_card i

end AlphaCycle
