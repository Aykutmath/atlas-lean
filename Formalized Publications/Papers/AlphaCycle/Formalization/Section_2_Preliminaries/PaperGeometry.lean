import Section_2_Preliminaries.GeometryCycle
import Section_2_Preliminaries.CyclePermutation
import Section_2_Preliminaries.SetGluing

/-! Explicit seven-block geometry and the paper's private-block reduction. -/
namespace AlphaCycle.Geometry

variable {V : Type*} [DecidableEq V]

/-- The paper's private blocks `D₁,D₂,D₃`, with zero-based edge indices. -/
def privateBlock (e : Fin 3 → Finset V) : Fin 3 → Finset V :=
  ![e 0 \ (e 1 ∪ e 2), e 1 \ (e 0 ∪ e 2), e 2 \ (e 0 ∪ e 1)]

/-- The seven disjoint Venn regions, ordered `T,A,B,C,D₁,D₂,D₃`. -/
def vennBlock (e : Fin 3 → Finset V) : Fin 7 → Finset V :=
  ![common e, blockA e, blockB e, blockC e,
    privateBlock e 0, privateBlock e 1, privateBlock e 2]

/-- The indexed private-block definition equals `eᵢ \ (eⱼ ∪ eₖ)` for every
ordering of the three distinct indices. -/
theorem privateBlock_eq (e : Fin 3 → Finset V) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    privateBlock e i = e i \ (e j ∪ e k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [privateBlock] <;> rw [Finset.union_comm]

/-- Every two distinct regions among the seven Venn blocks are disjoint. -/
theorem vennBlock_pairwise_disjoint (e : Fin 3 → Finset V) :
    Pairwise (fun i j => Disjoint (vennBlock e i) (vennBlock e j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [vennBlock, privateBlock, common, blockA, blockB, blockC,
      Finset.disjoint_left]

theorem edge0_decomposition (e : Fin 3 → Finset V) :
    e 0 = common e ∪ blockA e ∪ blockC e ∪ privateBlock e 0 := by
  ext v
  simp only [common, blockA, blockC, privateBlock, Fin.isValue,
    Matrix.cons_val_zero, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

theorem edge1_decomposition (e : Fin 3 → Finset V) :
    e 1 = common e ∪ blockA e ∪ blockB e ∪ privateBlock e 1 := by
  ext v
  simp [common, blockA, blockB, privateBlock]
  tauto

theorem edge2_decomposition (e : Fin 3 → Finset V) :
    e 2 = common e ∪ blockB e ∪ blockC e ∪ privateBlock e 2 := by
  ext v
  simp [common, blockB, blockC, privateBlock]
  tauto

/-- The union of the original three edges is precisely the union of all Venn blocks. -/
theorem union_support_decomposition (e : Fin 3 → Finset V) :
    e 0 ∪ e 1 ∪ e 2 =
      common e ∪ blockA e ∪ blockB e ∪ blockC e ∪
        privateBlock e 0 ∪ privateBlock e 1 ∪ privateBlock e 2 := by
  ext v
  simp [common, blockA, blockB, blockC, privateBlock]
  tauto

/-- The common block and pair-only blocks make up the full core. -/
theorem core_decomposition (e : Fin 3 → Finset V) :
    core e = common e ∪ blockA e ∪ blockB e ∪ blockC e := by
  ext v
  simp only [core, common, blockA, blockB, blockC,
    Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

/-- The paper's no-private condition is equivalent to the emptiness of all
three private blocks. -/
theorem noPrivate_iff_privateBlock_empty (e : Fin 3 → Finset V) :
    Triangle.NoPrivate (e 0) (e 1) (e 2) ↔ ∀ i, privateBlock e i = ∅ := by
  simp only [Triangle.NoPrivate]
  constructor
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i <;> simp [privateBlock, Finset.sdiff_eq_empty_iff_subset, h0, h1, h2]
  · intro h
    exact ⟨Finset.sdiff_eq_empty_iff_subset.mp (h 0),
      Finset.sdiff_eq_empty_iff_subset.mp (h 1),
      Finset.sdiff_eq_empty_iff_subset.mp (h 2)⟩

/-- A vertex of a no-private triple belongs to at least two of its edges. -/
theorem noPrivate_union_eq_core (e : Fin 3 → Finset V)
    (h : Triangle.NoPrivate (e 0) (e 1) (e 2)) :
    e 0 ∪ e 1 ∪ e 2 = core e := by
  rcases h with ⟨h0, h1, h2⟩
  ext v
  have h0v := @h0 v
  have h1v := @h1 v
  have h2v := @h2 v
  simp only [core, Finset.mem_union, Finset.mem_inter] at h0v h1v h2v ⊢
  tauto

/-- Deleting the private block agrees exactly with the existing core restriction. -/
theorem reduced_eq_sdiff_privateBlock (e : Fin 3 → Finset V) (i : Fin 3) :
    reduced e i = e i \ privateBlock e i := by
  fin_cases i <;> ext v <;> simp [reduced, privateBlock, core] <;> tauto

/-- The two formulas for the reduced edge in the paper coincide. -/
theorem reduced_eq_inter_other (e : Fin 3 → Finset V) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    reduced e i = e i ∩ (e j ∪ e k) := by
  rw [reduced_eq_sdiff_privateBlock, privateBlock_eq e i j k hij hik hjk]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
  tauto

/-- All pairwise intersections, and hence all Venn core blocks, are unchanged
by removing private blocks. -/
theorem reduced_blocks (e : Fin 3 → Finset V) :
    common (reduced e) = common e ∧ blockA (reduced e) = blockA e ∧
      blockB (reduced e) = blockB e ∧ blockC (reduced e) = blockC e := by
  repeat' apply And.intro
  all_goals
    ext v
    simp only [common, blockA, blockB, blockC, reduced, core,
      Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    tauto

end AlphaCycle.Geometry

namespace AlphaCycle.Geometry
variable {V : Type*} [DecidableEq V]

/-- The four regions used for a no-private subcycle, ordered `P,Q,R,S`. -/
def subcycleBlock (f : Fin 3 → Finset V) : Fin 4 → Finset V :=
  ![blockA f, blockB f, blockC f, common f]

theorem subcycleBlock_pairwise_disjoint (f : Fin 3 → Finset V) :
    Pairwise (fun i j => Disjoint (subcycleBlock f i) (subcycleBlock f j)) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [subcycleBlock, blockA, blockB, blockC, common, Finset.disjoint_left]

/-- The exact three disjoint decompositions in the reduced-subcycle lemma.
Pairwise disjointness is supplied by `subcycleBlock_pairwise_disjoint`. -/
theorem noPrivate_edge_decompositions (f : Fin 3 → Finset V)
    (hf : Triangle.NoPrivate (f 0) (f 1) (f 2)) :
    f 0 = blockA f ∪ blockC f ∪ common f ∧
    f 1 = blockA f ∪ blockB f ∪ common f ∧
    f 2 = blockB f ∪ blockC f ∪ common f := by
  have he := (noPrivate_iff_privateBlock_empty f).mp hf
  have h0 := edge0_decomposition f
  have h1 := edge1_decomposition f
  have h2 := edge2_decomposition f
  simp only [he, Finset.union_empty] at h0 h1 h2
  simpa only [Finset.union_comm, Finset.union_left_comm, Finset.union_assoc] using
    And.intro h0 (And.intro h1 h2)

/-- Each subcycle pair-only region lies in the corresponding original overlap;
the common subcycle region lies in the original common block. -/
theorem aligned_subcycle_containments (e f : Fin 3 → Finset V)
    (hf : ∀ i, f i ⊆ e i) :
    blockA f ⊆ blockA e ∪ common e ∧
    blockB f ⊆ blockB e ∪ common e ∧
    blockC f ⊆ blockC e ∪ common e ∧ common f ⊆ common e := by
  constructor
  · rw [Finset.union_comm, ← overlap01]
    exact Finset.sdiff_subset.trans (Finset.inter_subset_inter (hf 0) (hf 1))
  constructor
  · rw [Finset.union_comm, ← overlap12]
    exact Finset.sdiff_subset.trans (Finset.inter_subset_inter (hf 1) (hf 2))
  constructor
  · rw [Finset.union_comm, ← overlap02]
    exact Finset.sdiff_subset.trans (Finset.inter_subset_inter (hf 0) (hf 2))
  · exact Finset.inter_subset_inter (Finset.inter_subset_inter (hf 0) (hf 1)) (hf 2)

variable [Fintype V]

/-- The complete reduced-subcycle structure lemma: parent permutation,
four pairwise disjoint named regions, the three edge decompositions, and all
four containing-block conclusions. -/
theorem reduced_subcycle_structure (e : Fin 3 → Finset V) (f : SupportedCycle e) :
    ∃ σ : Equiv.Perm (Fin 3),
      let g := fun i => f.edge (σ i)
      (∀ i, g i ⊆ e i) ∧
      Pairwise (fun i j => Disjoint (subcycleBlock g i) (subcycleBlock g j)) ∧
      (g 0 = blockA g ∪ blockC g ∪ common g ∧
       g 1 = blockA g ∪ blockB g ∪ common g ∧
       g 2 = blockB g ∪ blockC g ∪ common g) ∧
      blockA g ⊆ blockA e ∪ common e ∧
      blockB g ⊆ blockB e ∪ common e ∧
      blockC g ⊆ blockC e ∪ common e ∧ common g ⊆ common e := by
  obtain ⟨σ, hσ⟩ := f.exists_alignment
  exact ⟨σ, hσ, subcycleBlock_pairwise_disjoint _,
    noPrivate_edge_decompositions (fun i => f.edge (σ i))
      (noPrivate_permute f.edge σ f.noPrivate),
    aligned_subcycle_containments e _ hσ⟩

/-- A family of local laws has a global realization exactly when its reduced
laws have a realization supported on the core. The explicit core support
condition makes precise the paper's phrase "on the core". -/
theorem private_block_reduction (e : Fin 3 → Finset V) (μ : Fin 3 → BooleanLaw V) :
    (∃ ρ : BooleanLaw V, ∀ i, restrictLaw ρ (e i) = restrictLaw (μ i) (e i)) ↔
    (∃ ν : BooleanLaw V, restrictLaw ν (core e) = ν ∧
      ∀ i, restrictLaw ν (reduced e i) = restrictLaw (μ i) (reduced e i)) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨restrictLaw ρ (core e), ?_, ?_⟩
    · simp only [restrictLaw_restrict, Finset.inter_self]
    · intro i
      rw [restrictLaw_restrict]
      change restrictLaw ρ (core e ∩ (core e ∩ e i)) = _
      rw [← Finset.inter_assoc, Finset.inter_self]
      exact restrictLaw_of_subset (hρ i) Finset.inter_subset_right
  · rintro ⟨ν, _, hν⟩
    obtain ⟨h01, h02, h12⟩ := overlaps_subset_core e
    obtain ⟨ρ, h0, h1, h2⟩ := restore_private_on_sets (core e) (e 0) (e 1) (e 2)
      ν (μ 0) (μ 1) (μ 2) h01 h02 h12 (hν 0) (hν 1) (hν 2)
    refine ⟨ρ, ?_⟩
    intro i
    fin_cases i <;> assumption

omit [Fintype V] in
/-- In the singleton case the core in the reduction theorem is literally
`T ∪ {a,b,c}`, as written in the paper. -/
theorem singleton_core_eq (e : Fin 3 → Finset V) (a b c : V)
    (ha : blockA e = {a}) (hb : blockB e = {b}) (hc : blockC e = {c}) :
    core e = common e ∪ {a, b, c} := by
  rw [core_decomposition, ha, hb, hc]
  ext v
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [Fintype V] in
/-- The three reduced edge formulas displayed at the start of the positive proof. -/
theorem singleton_reduced_edges (e : Fin 3 → Finset V) (a b c : V)
    (ha : blockA e = {a}) (hb : blockB e = {b}) (hc : blockC e = {c}) :
    reduced e 0 = common e ∪ {a, c} ∧
    reduced e 1 = common e ∪ {a, b} ∧
    reduced e 2 = common e ∪ {b, c} := by
  simp only [reduced, reduced0, reduced1, reduced2, ha, hb, hc]
  repeat' apply And.intro
  all_goals ext v; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto

/-- The exact private-block reduction statement specialized to the paper's
singleton notation and with the reduced local laws written as marginals. -/
theorem singleton_private_block_reduction (e : Fin 3 → Finset V)
    (a b c : V) (ha : blockA e = {a}) (hb : blockB e = {b}) (hc : blockC e = {c})
    (μ : Fin 3 → BooleanLaw V) :
    (∃ ρ : BooleanLaw V, ∀ i, restrictLaw ρ (e i) = restrictLaw (μ i) (e i)) ↔
    (∃ ν : BooleanLaw V, restrictLaw ν (common e ∪ {a, b, c}) = ν ∧
      ∀ i, restrictLaw ν (e i \ privateBlock e i) =
        restrictLaw (μ i) (e i \ privateBlock e i)) := by
  simpa only [singleton_core_eq e a b c ha hb hc, reduced_eq_sdiff_privateBlock]
    using private_block_reduction e μ

end AlphaCycle.Geometry

namespace AlphaCycle
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restoration can preserve the entire prescribed joint core law, including
correlations not seen by any one reduced edge. This is the existential content
of sampling the core first and then attaching the private variables. -/
theorem restore_private_on_sets_preserves_core (s e₁ e₂ e₃ : Finset V)
    (μ μ₁ μ₂ μ₃ : BooleanLaw V)
    (h₁₂ : e₁ ∩ e₂ ⊆ s) (h₁₃ : e₁ ∩ e₃ ⊆ s) (h₂₃ : e₂ ∩ e₃ ⊆ s)
    (h₁ : restrictLaw μ (s ∩ e₁) = restrictLaw μ₁ (s ∩ e₁))
    (h₂ : restrictLaw μ (s ∩ e₂) = restrictLaw μ₂ (s ∩ e₂))
    (h₃ : restrictLaw μ (s ∩ e₃) = restrictLaw μ₃ (s ∩ e₃)) :
    ∃ ρ : BooleanLaw V,
      restrictLaw ρ s = restrictLaw μ s ∧
      restrictLaw ρ e₁ = restrictLaw μ₁ e₁ ∧
      restrictLaw ρ e₂ = restrictLaw μ₂ e₂ ∧
      restrictLaw ρ e₃ = restrictLaw μ₃ e₃ := by
  obtain ⟨ρ₁, hρ₁s, hρ₁e⟩ := glue_on_sets μ μ₁ s e₁ h₁
  have hover₂ : restrictLaw ρ₁ ((s ∪ e₁) ∩ e₂) =
      restrictLaw μ₂ ((s ∪ e₁) ∩ e₂) := by
    rw [union_inter_eq_core_inter h₁₂]
    exact (restrictLaw_of_subset hρ₁s Finset.inter_subset_left).trans h₂
  obtain ⟨ρ₂, hρ₂s, hρ₂e⟩ := glue_on_sets ρ₁ μ₂ (s ∪ e₁) e₂ hover₂
  have hc : (s ∪ e₁ ∪ e₂) ∩ e₃ = s ∩ e₃ := by
    ext v
    have ha : v ∈ e₁ ∩ e₃ → v ∈ s ∩ e₃ := fun h =>
      Finset.mem_inter.mpr ⟨h₁₃ h, (Finset.mem_inter.mp h).2⟩
    have hb : v ∈ e₂ ∩ e₃ → v ∈ s ∩ e₃ := fun h =>
      Finset.mem_inter.mpr ⟨h₂₃ h, (Finset.mem_inter.mp h).2⟩
    simp only [Finset.mem_union, Finset.mem_inter] at ha hb ⊢
    tauto
  have hover₃ : restrictLaw ρ₂ ((s ∪ e₁ ∪ e₂) ∩ e₃) =
      restrictLaw μ₃ ((s ∪ e₁ ∪ e₂) ∩ e₃) := by
    rw [hc]
    exact (restrictLaw_of_subset hρ₂s (Finset.inter_subset_left.trans Finset.subset_union_left)).trans
      ((restrictLaw_of_subset hρ₁s Finset.inter_subset_left).trans h₃)
  obtain ⟨ρ₃, hρ₃s, hρ₃e⟩ := glue_on_sets ρ₂ μ₃ (s ∪ e₁ ∪ e₂) e₃ hover₃
  refine ⟨ρ₃, ?_, ?_, ?_, hρ₃e⟩
  · exact (restrictLaw_of_subset hρ₃s
      (Finset.subset_union_left.trans Finset.subset_union_left)).trans
      ((restrictLaw_of_subset hρ₂s Finset.subset_union_left).trans hρ₁s)
  · exact (restrictLaw_of_subset hρ₃s
      (Finset.subset_union_right.trans Finset.subset_union_left)).trans
      ((restrictLaw_of_subset hρ₂s Finset.subset_union_right).trans hρ₁e)
  · exact (restrictLaw_of_subset hρ₃s Finset.subset_union_right).trans hρ₂e

end AlphaCycle
