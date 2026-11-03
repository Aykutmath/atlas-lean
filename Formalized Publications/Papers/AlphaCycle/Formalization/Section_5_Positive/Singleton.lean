import Section_5_Positive.Positive
import Section_2_Preliminaries.MomentInversion

/-! The positive slice theorem translated back to Boolean vertex assignments. -/
noncomputable section

namespace AlphaCycle.Singleton

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common state together with the values at two distinguished vertices. -/
def project (T : Finset V) (a b : V) (x : Finset V) : Finset V × Bool × Bool :=
  (x ∩ T, decide (a ∈ x), decide (b ∈ x))

/-- Projection onto an intersection consisting of the common block and one vertex. -/
def projectOne (T : Finset V) (a : V) (x : Finset V) : Finset V × Bool :=
  (x ∩ T, decide (a ∈ x))

/-- The local laws viewed in the abstract common-state/pair-state coordinates. -/
def coreFamily (T : Finset V) (a b c : V)
    (μab μac μbc : BooleanLaw V) : CoreFamily (Finset V) Bool Bool Bool where
  ab := μab.map (project T a b)
  ac := μac.map (project T a c)
  bc := μbc.map (project T b c)

theorem projectOne_restrict (T : Finset V) (a : V) (x : Finset V) :
    projectOne T a (x ∩ (T ∪ {a})) = projectOne T a x := by
  apply Prod.ext
  · ext v
    simp only [projectOne, Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    tauto
  · simp [projectOne]

/-- Consistency of the full overlap laws gives consistency of all slice tables. -/
theorem core_consistent (T : Finset V) (a b c : V)
    (μab μac μbc : BooleanLaw V)
    (ha : restrictLaw μab (T ∪ {a}) = restrictLaw μac (T ∪ {a}))
    (hb : restrictLaw μab (T ∪ {b}) = restrictLaw μbc (T ∪ {b}))
    (hc : restrictLaw μac (T ∪ {c}) = restrictLaw μbc (T ∪ {c})) :
    (coreFamily T a b c μab μac μbc).Consistent := by
  refine ⟨?_, ?_, ?_⟩
  · have hh := congrArg (Law.map (projectOne T a)) ha
    simp only [restrictLaw, Law.map_map, Function.comp_def, projectOne_restrict] at hh
    simpa only [Law.map_map, Function.comp_def, coreFamily, project, projectOne] using hh
  · have hh := congrArg (Law.map (projectOne T b)) hb
    simp only [restrictLaw, Law.map_map, Function.comp_def, projectOne_restrict] at hh
    simpa only [Law.map_map, Function.comp_def, coreFamily, project, projectOne] using hh
  · have hh := congrArg (Law.map (projectOne T c)) hc
    simp only [restrictLaw, Law.map_map, Function.comp_def, projectOne_restrict] at hh
    simpa only [Law.map_map, Function.comp_def, coreFamily, project, projectOne] using hh

/-- The singleton containing a vertex when its bit is one. -/
def bit (a : V) (b : Bool) : Finset V := if b = true then {a} else ∅

@[simp] theorem mem_bit (v a : V) (b : Bool) : v ∈ bit a b ↔ v = a ∧ b = true := by
  cases b <;> simp [bit]

/-- Reassemble a local pair state as a subset of its edge. -/
def assemblePair (T : Finset V) (a b : V) (x : Finset V × Bool × Bool) : Finset V :=
  (x.1 ∩ T) ∪ bit a x.2.1 ∪ bit b x.2.2

/-- Reassembly recovers the restriction of the original assignment exactly. -/
theorem assemblePair_project (T : Finset V) (a b : V) (x : Finset V) :
    assemblePair T a b (project T a b x) = x ∩ (T ∪ {a, b}) := by
  ext v
  simp only [assemblePair, project, Finset.mem_union, Finset.mem_inter, mem_bit,
    Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq]
  aesop

/-- Reassemble a global core state as a Boolean vertex assignment. -/
def assemble (T : Finset V) (a b c : V)
    (x : Finset V × Bool × Bool × Bool) : Finset V :=
  (x.1 ∩ T) ∪ bit a x.2.1 ∪ bit b x.2.2.1 ∪ bit c x.2.2.2

/-- Restricting the assembled assignment to `ab` forgets precisely the `c` bit. -/
theorem assemble_ab (T : Finset V) (a b c : V)
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Finset V × Bool × Bool × Bool) :
    assemble T a b c x ∩ (T ∪ {a, b}) =
      assemblePair T a b (x.1, x.2.1, x.2.2.1) := by
  ext v
  simp only [assemble, assemblePair, Finset.mem_union, Finset.mem_inter, mem_bit,
    Finset.mem_insert, Finset.mem_singleton]
  aesop

/-- Restricting the assembled assignment to `ac` forgets precisely the `b` bit. -/
theorem assemble_ac (T : Finset V) (a b c : V)
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Finset V × Bool × Bool × Bool) :
    assemble T a b c x ∩ (T ∪ {a, c}) =
      assemblePair T a c (x.1, x.2.1, x.2.2.2) := by
  ext v
  simp only [assemble, assemblePair, Finset.mem_union, Finset.mem_inter, mem_bit,
    Finset.mem_insert, Finset.mem_singleton]
  aesop

/-- Restricting the assembled assignment to `bc` forgets precisely the `a` bit. -/
theorem assemble_bc (T : Finset V) (a b c : V)
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Finset V × Bool × Bool × Bool) :
    assemble T a b c x ∩ (T ∪ {b, c}) =
      assemblePair T b c (x.1, x.2.2.1, x.2.2.2) := by
  ext v
  simp only [assemble, assemblePair, Finset.mem_union, Finset.mem_inter, mem_bit,
    Finset.mem_insert, Finset.mem_singleton]
  aesop

/-- The abstract slice criterion yields a genuine global Boolean assignment law
on the three reduced singleton edges. -/
theorem extension (T : Finset V) (a b c : V)
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (μab μac μbc : BooleanLaw V)
    (hoa : restrictLaw μab (T ∪ {a}) = restrictLaw μac (T ∪ {a}))
    (hob : restrictLaw μab (T ∪ {b}) = restrictLaw μbc (T ∪ {b}))
    (hoc : restrictLaw μac (T ∪ {c}) = restrictLaw μbc (T ∪ {c}))
    (htri : Positive.TriangleConditions (Positive.ofCoreFamily
      (coreFamily T a b c μab μac μbc) (core_consistent T a b c μab μac μbc hoa hob hoc))) :
    ∃ ν : BooleanLaw V,
      restrictLaw ν (T ∪ {a, b}) = restrictLaw μab (T ∪ {a, b}) ∧
      restrictLaw ν (T ∪ {a, c}) = restrictLaw μac (T ∪ {a, c}) ∧
      restrictLaw ν (T ∪ {b, c}) = restrictLaw μbc (T ∪ {b, c}) := by
  obtain ⟨μ, hmab, hmac, hmbc⟩ := (Positive.core_exact _
    (core_consistent T a b c μab μac μbc hoa hob hoc)).1 htri
  refine ⟨μ.map (assemble T a b c), ?_, ?_, ?_⟩
  · calc
      restrictLaw (μ.map (assemble T a b c)) (T ∪ {a, b}) =
          (μ.map (fun x => (x.1, x.2.1, x.2.2.1))).map (assemblePair T a b) := by
        simp only [restrictLaw, Law.map_map, Function.comp_def]
        congr 1
        funext x
        exact assemble_ab T a b c ha hb hc hab hac hbc x
      _ = (μab.map (project T a b)).map (assemblePair T a b) := by rw [hmab]; rfl
      _ = restrictLaw μab (T ∪ {a, b}) := by
        simp only [restrictLaw, Law.map_map, Function.comp_def, assemblePair_project]
  · calc
      restrictLaw (μ.map (assemble T a b c)) (T ∪ {a, c}) =
          (μ.map (fun x => (x.1, x.2.1, x.2.2.2))).map (assemblePair T a c) := by
        simp only [restrictLaw, Law.map_map, Function.comp_def]
        congr 1
        funext x
        exact assemble_ac T a b c ha hb hc hab hac hbc x
      _ = (μac.map (project T a c)).map (assemblePair T a c) := by rw [hmac]; rfl
      _ = restrictLaw μac (T ∪ {a, c}) := by
        simp only [restrictLaw, Law.map_map, Function.comp_def, assemblePair_project]
  · calc
      restrictLaw (μ.map (assemble T a b c)) (T ∪ {b, c}) =
          (μ.map (fun x => (x.1, x.2.2.1, x.2.2.2))).map (assemblePair T b c) := by
        simp only [restrictLaw, Law.map_map, Function.comp_def]
        congr 1
        funext x
        exact assemble_bc T a b c ha hb hc hab hac hbc x
      _ = (μbc.map (project T b c)).map (assemblePair T b c) := by rw [hmbc]; rfl
      _ = restrictLaw μbc (T ∪ {b, c}) := by
        simp only [restrictLaw, Law.map_map, Function.comp_def, assemblePair_project]

end AlphaCycle.Singleton
