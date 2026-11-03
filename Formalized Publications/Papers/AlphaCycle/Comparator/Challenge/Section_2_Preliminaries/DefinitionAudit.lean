import Challenge.Section_1_Introduction.Geometry
import Challenge.Section_2_Preliminaries.Relaxation
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

namespace AlphaCycle
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Geometry
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
end AlphaCycle
