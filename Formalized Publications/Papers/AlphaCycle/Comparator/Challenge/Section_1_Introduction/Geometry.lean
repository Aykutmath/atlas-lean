import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Tauto
/- Challenge excerpt file: byte-identical source excerpts of the listed solution definitions. See Comparator/alpha_cycle_comparator.lean for the independence record. -/

/-! The finite Venn decomposition of a length-three cycle. -/
namespace AlphaCycle.Geometry
variable {V : Type*} [DecidableEq V]

def common (e : Fin 3 → Finset V) : Finset V := e 0 ∩ e 1 ∩ e 2

def blockA (e : Fin 3 → Finset V) : Finset V := (e 0 ∩ e 1) \ e 2

def blockB (e : Fin 3 → Finset V) : Finset V := (e 1 ∩ e 2) \ e 0

def blockC (e : Fin 3 → Finset V) : Finset V := (e 0 ∩ e 2) \ e 1

def core (e : Fin 3 → Finset V) : Finset V :=
  (e 0 ∩ e 1) ∪ (e 1 ∩ e 2) ∪ (e 0 ∩ e 2)

/-- On the completed support this is equivalent to the alpha-cycle condition. -/
def IsCycle (e : Fin 3 → Finset V) : Prop :=
  (blockA e).Nonempty ∧ (blockB e).Nonempty ∧ (blockC e).Nonempty

def Singletons (e : Fin 3 → Finset V) : Prop :=
  (blockA e).card = 1 ∧ (blockB e).card = 1 ∧ (blockC e).card = 1

theorem overlap01 (e : Fin 3 → Finset V) : e 0 ∩ e 1 = common e ∪ blockA e := by
  ext v; simp only [common, blockA, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto

theorem overlap12 (e : Fin 3 → Finset V) : e 1 ∩ e 2 = common e ∪ blockB e := by
  ext v; simp only [common, blockB, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto

theorem overlap02 (e : Fin 3 → Finset V) : e 0 ∩ e 2 = common e ∪ blockC e := by
  ext v; simp only [common, blockC, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto

theorem reduced0 (e : Fin 3 → Finset V) : core e ∩ e 0 = common e ∪ blockA e ∪ blockC e := by
  ext v
  simp only [common, core, blockA, blockC, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem reduced1 (e : Fin 3 → Finset V) : core e ∩ e 1 = common e ∪ blockA e ∪ blockB e := by
  ext v
  simp only [common, core, blockA, blockB, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem reduced2 (e : Fin 3 → Finset V) : core e ∩ e 2 = common e ∪ blockB e ∪ blockC e := by
  ext v
  simp only [common, core, blockB, blockC, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem overlaps_subset_core (e : Fin 3 → Finset V) :
    e 0 ∩ e 1 ⊆ core e ∧ e 0 ∩ e 2 ⊆ core e ∧ e 1 ∩ e 2 ⊆ core e := by
  constructor
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  constructor
  · exact Finset.subset_union_right
  · exact Finset.subset_union_right.trans Finset.subset_union_left

theorem singleton_vertices (e : Fin 3 → Finset V) (h : Singletons e) :
    ∃ a b c, blockA e = {a} ∧ blockB e = {b} ∧ blockC e = {c} ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      a ∉ common e ∧ b ∉ common e ∧ c ∉ common e := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h.1
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp h.2.1
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h.2.2
  have hma : a ∈ blockA e := by rw [ha]; exact Finset.mem_singleton_self _
  have hmb : b ∈ blockB e := by rw [hb]; exact Finset.mem_singleton_self _
  have hmc : c ∈ blockC e := by rw [hc]; exact Finset.mem_singleton_self _
  simp only [blockA, blockB, blockC, Finset.mem_sdiff, Finset.mem_inter] at hma hmb hmc
  refine ⟨a,b,c,ha,hb,hc,?_,?_,?_,?_,?_,?_⟩
  · intro he; subst b; exact hmb.2 hma.1.1
  · intro he; subst c; exact hmc.2 hma.1.2
  · intro he; subst c; exact hmb.2 hmc.1.1
  · simpa only [common, Finset.mem_inter, not_and] using
      (fun (_ : a ∈ e 0 ∩ e 1) => hma.2)
  · simp only [common, Finset.mem_inter]; tauto
  · simp only [common, Finset.mem_inter]; tauto

theorem not_singletons_has_large (e : Fin 3 → Finset V) (h : IsCycle e)
    (hn : ¬ Singletons e) :
    2 ≤ (blockA e).card ∨ 2 ≤ (blockB e).card ∨ 2 ≤ (blockC e).card := by
  have ha := Finset.card_pos.mpr h.1
  have hb := Finset.card_pos.mpr h.2.1
  have hc := Finset.card_pos.mpr h.2.2
  simp only [Singletons] at hn
  omega

end AlphaCycle.Geometry


