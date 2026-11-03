import Challenge.Section_1_Introduction.Geometry
import Challenge.Section_2_Preliminaries.Relaxation
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

/-! The canonical no-private alpha-cycle obtained by deleting private vertices. -/

namespace AlphaCycle.Geometry

variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The three private-free maximal edges. -/
def reduced (e : Fin 3 → Finset V) (i : Fin 3) : Finset V := core e ∩ e i
/-- Deleting private vertices preserves every pairwise intersection. -/
theorem reduced_overlap01 (e : Fin 3 → Finset V) :
    reduced e 0 ∩ reduced e 1 = e 0 ∩ e 1 := by
  ext v
  simp only [reduced, core, Finset.mem_inter, Finset.mem_union]
  tauto
theorem reduced_overlap12 (e : Fin 3 → Finset V) :
    reduced e 1 ∩ reduced e 2 = e 1 ∩ e 2 := by
  ext v
  simp only [reduced, core, Finset.mem_inter, Finset.mem_union]
  tauto
theorem reduced_overlap02 (e : Fin 3 → Finset V) :
    reduced e 0 ∩ reduced e 2 = e 0 ∩ e 2 := by
  ext v
  simp only [reduced, core, Finset.mem_inter, Finset.mem_union]
  tauto
theorem reduced_noPrivate (e : Fin 3 → Finset V) :
    Triangle.NoPrivate (reduced e 0) (reduced e 1) (reduced e 2) := by
  repeat' apply And.intro
  all_goals
    intro v hv
    simp only [reduced, core, Finset.mem_inter, Finset.mem_union] at hv ⊢
    tauto
theorem reduced_incomparable (e : Fin 3 → Finset V) (h : IsCycle e) :
    ∀ i j, i ≠ j → ¬ reduced e i ⊆ reduced e j := by
  obtain ⟨a, ha⟩ := h.1
  obtain ⟨b, hb⟩ := h.2.1
  obtain ⟨c, hc⟩ := h.2.2
  simp only [blockA, blockB, blockC, Finset.mem_sdiff, Finset.mem_inter] at ha hb hc
  have ham0 : a ∈ reduced e 0 := by simp [reduced, core, ha.1.1, ha.1.2]
  have ham1 : a ∈ reduced e 1 := by simp [reduced, core, ha.1.1, ha.1.2]
  have hbm1 : b ∈ reduced e 1 := by simp [reduced, core, hb.1.1, hb.1.2]
  have hbm2 : b ∈ reduced e 2 := by simp [reduced, core, hb.1.1, hb.1.2]
  have hcm0 : c ∈ reduced e 0 := by simp [reduced, core, hc.1.1, hc.1.2]
  have hcm2 : c ∈ reduced e 2 := by simp [reduced, core, hc.1.1, hc.1.2]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij
  · intro hh
    exact hc.2 (Finset.mem_inter.mp (hh hcm0)).2
  · intro hh
    exact ha.2 (Finset.mem_inter.mp (hh ham0)).2
  · intro hh
    exact hb.2 (Finset.mem_inter.mp (hh hbm1)).2
  · intro hh
    exact ha.2 (Finset.mem_inter.mp (hh ham1)).2
  · intro hh
    exact hb.2 (Finset.mem_inter.mp (hh hbm2)).2
  · intro hh
    exact hc.2 (Finset.mem_inter.mp (hh hcm2)).2
/-- Nonempty pair-only blocks prevent the entire core from lying in one parent edge. -/
theorem core_not_subset (e : Fin 3 → Finset V) (h : IsCycle e) :
    ∀ i, ¬ core e ⊆ e i := by
  obtain ⟨a, ha⟩ := h.1
  obtain ⟨b, hb⟩ := h.2.1
  obtain ⟨c, hc⟩ := h.2.2
  simp only [blockA, blockB, blockC, Finset.mem_sdiff, Finset.mem_inter] at ha hb hc
  intro i
  fin_cases i
  · intro hh
    exact hb.2 (hh (by simp [core, hb.1.1, hb.1.2]))
  · intro hh
    exact hc.2 (hh (by simp [core, hc.1.1, hc.1.2]))
  · intro hh
    exact ha.2 (hh (by simp [core, ha.1.1, ha.1.2]))
/-- The distinguished private-free reduction is a supported no-private alpha-cycle. -/
def distinguishedCycle (e : Fin 3 → Finset V) (h : IsCycle e) : SupportedCycle e where
  edge := reduced e
  supported i := mem_completedSupport_of_subset e i _ Finset.inter_subset_right
  noPrivate := reduced_noPrivate e
  incomparable := reduced_incomparable e h
  alpha := by
    intro i
    rw [reduced_overlap01, reduced_overlap12, reduced_overlap02]
    exact core_not_subset e h i

end AlphaCycle.Geometry
