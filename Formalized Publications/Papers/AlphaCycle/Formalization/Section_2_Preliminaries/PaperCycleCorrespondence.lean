import Section_2_Preliminaries.PaperHypergraph

/-! Exact correspondence between the paper's physical hyperedge cycles and `SupportedCycle`. -/
namespace AlphaCycle.PaperHypergraph
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Literal length-three alpha-cycle conditions in an arbitrary finite hypergraph. -/
def IsAlphaCycle (H : PaperHypergraph V) (f : Fin 3 → Finset V) : Prop :=
  (∀ i, f i ∈ H.edges) ∧
  (∀ i j, i ≠ j → (f i \ f j).Nonempty) ∧
  ∀ h ∈ H.edges, ¬ Geometry.core f ⊆ h

/-- The paper's collection `C₀(H)` of no-private length-three alpha-cycles. -/
def NoPrivateAlphaCycle (H : PaperHypergraph V) (f : Fin 3 → Finset V) : Prop :=
  H.IsAlphaCycle f ∧ Triangle.NoPrivate (f 0) (f 1) (f 2)

/-- Three generating hyperedges without assuming they already form a cycle. -/
def ofThreeEdges (e : Fin 3 → Finset V) (hcard : ∀ i, 2 ≤ (e i).card)
    (hv : ∀ v, ∃ i, v ∈ e i) : PaperHypergraph V where
  edges := Finset.univ.image e
  edge_card s hs := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hcard i
  covers v := by
    obtain ⟨i, hi⟩ := hv v
    exact ⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩

 theorem ofThreeEdges_completion_edges (e : Fin 3 → Finset V)
    (hcard : ∀ i, 2 ≤ (e i).card) (hv : ∀ v, ∃ i, v ∈ e i) (s : Finset V) :
    s ∈ (ofThreeEdges e hcard hv).completion.edges ↔
      s ∈ completedSupport e ∧ 2 ≤ s.card := by
  change s ∈ (ofThreeEdges e hcard hv).completionEdges ↔ _
  simp [mem_completedSupport, ofThreeEdges, and_comm]

/-- The pair-only block criterion is equivalent to the literal hypergraph alpha-cycle definition. -/
theorem isAlphaCycle_ofThreeEdges_iff (e : Fin 3 → Finset V)
    (hcard : ∀ i, 2 ≤ (e i).card) (hv : ∀ v, ∃ i, v ∈ e i) :
    (ofThreeEdges e hcard hv).completion.IsAlphaCycle e ↔ Geometry.IsCycle e := by
  have he (i : Fin 3) : e i ∈ (ofThreeEdges e hcard hv).completion.edges :=
    (ofThreeEdges_completion_edges e hcard hv (e i)).mpr
      ⟨mem_completedSupport_of_subset e i (e i) (Finset.Subset.refl _), hcard i⟩
  constructor
  · intro h
    apply (Geometry.isCycle_iff_core_not_subset e).mpr
    intro i
    exact h.2.2 (e i) (he i)
  · intro hc
    refine ⟨he, ?_, ?_⟩
    · intro i j hij
      exact Finset.sdiff_nonempty.mpr (hc.incomparable i j hij)
    · intro h hh hcore
      obtain ⟨hs, _⟩ := (ofThreeEdges_completion_edges e hcard hv h).mp hh
      obtain ⟨i, hi⟩ := (mem_completedSupport e h).mp hs
      exact ((Geometry.isCycle_iff_core_not_subset e).mp hc i) (hcore.trans hi)

/-- A literal no-private alpha-cycle constructs a `SupportedCycle` with identical edges. -/
def toSupportedCycle (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (f : Fin 3 → Finset V)
    (hf : (ofThree e hc hv).completion.NoPrivateAlphaCycle f) : SupportedCycle e where
  edge := f
  supported i := ((ofThree_completion_edges e hc hv (f i)).mp (hf.1.1 i)).1
  noPrivate := hf.2
  incomparable i j hij := Finset.sdiff_nonempty.mp (hf.1.2.1 i j hij)
  alpha i := hf.1.2.2 (e i) ((ofThree_completion_edges e hc hv (e i)).mpr
    ⟨mem_completedSupport_of_subset e i (e i) (Finset.Subset.refl _), hc.two_le_card i⟩)

@[simp] theorem toSupportedCycle_edge (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (f : Fin 3 → Finset V)
    (hf : (ofThree e hc hv).completion.NoPrivateAlphaCycle f) :
    (toSupportedCycle e hc hv f hf).edge = f := rfl

/-- Every `SupportedCycle` uses genuine hyperedges and obeys the literal global alpha condition. -/
theorem supportedCycle_noPrivateAlphaCycle (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (F : SupportedCycle e) :
    (ofThree e hc hv).completion.NoPrivateAlphaCycle F.edge := by
  refine ⟨⟨?_, ?_, ?_⟩, F.noPrivate⟩
  · intro i
    exact (ofThree_completion_edges e hc hv (F.edge i)).mpr
      ⟨F.supported i, F.two_le_card i⟩
  · intro i j hij
    exact Finset.sdiff_nonempty.mpr (F.incomparable i j hij)
  · intro h hh hcore
    obtain ⟨hs, _⟩ := (ofThree_completion_edges e hc hv h).mp hh
    obtain ⟨i, hi⟩ := (mem_completedSupport e h).mp hs
    exact F.alpha i (hcore.trans hi)

/-- Exact equality of the quantified cycle classes, including physical-edge cardinalities. -/
theorem noPrivateAlphaCycle_iff_supportedCycle (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) (f : Fin 3 → Finset V) :
    (ofThree e hc hv).completion.NoPrivateAlphaCycle f ↔
      ∃ F : SupportedCycle e, F.edge = f := by
  constructor
  · intro hf
    exact ⟨toSupportedCycle e hc hv f hf, rfl⟩
  · rintro ⟨F, rfl⟩
    exact supportedCycle_noPrivateAlphaCycle e hc hv F

/-- A bijection of cycle objects, retaining exactly the same three physical edges. -/
def supportedCycleEquiv (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) : SupportedCycle e ≃
      {f : Fin 3 → Finset V // (ofThree e hc hv).completion.NoPrivateAlphaCycle f} where
  toFun F := ⟨F.edge, supportedCycle_noPrivateAlphaCycle e hc hv F⟩
  invFun f := toSupportedCycle e hc hv f.val f.property
  left_inv F := by cases F; rfl
  right_inv f := Subtype.ext rfl

/-- Every edge-only predicate can be quantified over either representation of `C₀(H)`. -/
theorem forall_supportedCycle_iff_noPrivateAlphaCycle (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i)
    (P : (Fin 3 → Finset V) → Prop) :
    (∀ F : SupportedCycle e, P F.edge) ↔
      ∀ f, (ofThree e hc hv).completion.NoPrivateAlphaCycle f → P f := by
  constructor
  · intro h f hf
    exact h (toSupportedCycle e hc hv f hf)
  · intro h F
    exact h F.edge (supportedCycle_noPrivateAlphaCycle e hc hv F)

end AlphaCycle.PaperHypergraph
