import Section_2_Preliminaries.Polytope
import Section_2_Preliminaries.DefinitionAudit

/-! Exact coordinate interfaces for the finite hypergraphs used in the paper. -/
namespace AlphaCycle
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Boolean vector is represented by the finite set of its coordinates equal to true. -/
noncomputable def boolAssignmentEquiv : (V → Bool) ≃ Finset V where
  toFun x := Finset.univ.filter (fun v => x v = true)
  invFun s v := decide (v ∈ s)
  left_inv x := by funext v; cases h : x v <;> simp [h]
  right_inv s := by ext v; simp

@[simp] theorem mem_boolAssignmentEquiv (x : V → Bool) (v : V) :
    v ∈ boolAssignmentEquiv x ↔ x v = true := by
  simp [boolAssignmentEquiv]

/-- The real zero-one vector associated with an assignment. -/
noncomputable def binaryVector (x : Finset V) (v : V) : ℝ := if v ∈ x then 1 else 0

/-- The paper's squarefree monomial, including the empty monomial. -/
def paperMonomial (s : Finset V) (x : V → ℝ) : ℝ := ∏ v ∈ s, x v

@[simp] theorem paperMonomial_empty (x : V → ℝ) : paperMonomial ∅ x = 1 := by
  simp [paperMonomial]

@[simp] theorem paperMonomial_singleton (v : V) (x : V → ℝ) :
    paperMonomial {v} x = x v := by simp [paperMonomial]

 theorem paperMonomial_binaryVector (s x : Finset V) :
    paperMonomial s (binaryVector x) = if s ⊆ x then 1 else 0 := by
  simp only [paperMonomial, binaryVector, Finset.prod_boole]
  rfl

 theorem moment_eq_expected_monomial (μ : BooleanLaw V) (s : Finset V) :
    moment μ s = ∑ x, μ.mass x * paperMonomial s (binaryVector x) := by
  simp only [paperMonomial_binaryVector, moment, Law.prob]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Relabeling a finite sample space gives an exact equivalence of probability laws. -/
noncomputable def Law.equivMap {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) : Law α ≃ Law β where
  toFun μ := μ.map e
  invFun μ := μ.map e.symm
  left_inv μ := by
    dsimp only
    rw [Law.map_map]
    have he : e.symm ∘ e = id := by funext a; simp
    rw [he, Law.map_id]
  right_inv μ := by
    dsimp only
    rw [Law.map_map]
    have he : e ∘ e.symm = id := by funext a; simp
    rw [he, Law.map_id]

/-- Probability distributions on `{0,1}^V` and the finite laws used in Lean coincide. -/
noncomputable def booleanLawEquiv : Law (V → Bool) ≃ BooleanLaw V :=
  Law.equivMap boolAssignmentEquiv

/-- Restrict an ambient assignment to the actual finite edge subtype. -/
noncomputable def edgeProject (e x : Finset V) : Finset {v // v ∈ e} :=
  x.subtype (fun v => v ∈ e)

/-- Extend an edge assignment by zeros away from its edge. -/
def edgeEmbed (e : Finset V) (x : Finset {v // v ∈ e}) : Finset V :=
  x.map (Function.Embedding.subtype _)

@[simp] theorem mem_edgeProject (e x : Finset V) (v : {v // v ∈ e}) :
    v ∈ edgeProject e x ↔ v.val ∈ x := by simp [edgeProject]

@[simp] theorem mem_edgeEmbed (e : Finset V) (x : Finset {v // v ∈ e})
    (v : {v // v ∈ e}) : v.val ∈ edgeEmbed e x ↔ v ∈ x := by
  simp [edgeEmbed]

@[simp] theorem edgeProject_edgeEmbed (e : Finset V) (x : Finset {v // v ∈ e}) :
    edgeProject e (edgeEmbed e x) = x := by ext v; simp

@[simp] theorem edgeEmbed_edgeProject (e x : Finset V) :
    edgeEmbed e (edgeProject e x) = x ∩ e := by
  ext v
  simp [edgeEmbed, edgeProject, Finset.subtype_map]

 theorem edgeEmbed_subset (e : Finset V) (x : Finset {v // v ∈ e}) : edgeEmbed e x ⊆ e := by
  intro v hv
  obtain ⟨w, _, hw⟩ := Finset.mem_map.mp hv
  subst v
  exact w.property

 theorem subset_edgeEmbed_iff (e s : Finset V) (hs : s ⊆ e)
    (x : Finset {v // v ∈ e}) : s ⊆ edgeEmbed e x ↔ edgeProject e s ⊆ x := by
  constructor
  · intro h v hv
    exact (mem_edgeEmbed e x v).mp (h ((mem_edgeProject e s v).mp hv))
  · intro h v hv
    exact (mem_edgeEmbed e x ⟨v, hs hv⟩).mpr
      (h ((mem_edgeProject e s ⟨v, hs hv⟩).mpr hv))

/-- Edge laws represented on their literal Boolean assignment space. -/
noncomputable def ambientToEdgeLaw (e : Finset V) (μ : BooleanLaw V) :
    BooleanLaw {v // v ∈ e} := μ.map (edgeProject e)

/-- Embed a literal edge law into the ambient assignment space. -/
noncomputable def edgeLawToAmbient (e : Finset V) (ν : BooleanLaw {v // v ∈ e}) :
    BooleanLaw V := ν.map (edgeEmbed e)

@[simp] theorem ambientToEdgeLaw_edgeLawToAmbient (e : Finset V)
    (ν : BooleanLaw {v // v ∈ e}) :
    ambientToEdgeLaw e (edgeLawToAmbient e ν) = ν := by
  unfold ambientToEdgeLaw edgeLawToAmbient
  rw [Law.map_map]
  have h : edgeProject e ∘ edgeEmbed e = id := by funext x; simp
  rw [h, Law.map_id]

 theorem edgeLawToAmbient_ambientToEdgeLaw (e : Finset V) (μ : BooleanLaw V) :
    edgeLawToAmbient e (ambientToEdgeLaw e μ) = restrictLaw μ e := by
  unfold ambientToEdgeLaw edgeLawToAmbient restrictLaw
  rw [Law.map_map]
  congr 1
  funext x
  exact edgeEmbed_edgeProject e x

 theorem restrictLaw_edgeLawToAmbient (e : Finset V)
    (ν : BooleanLaw {v // v ∈ e}) :
    restrictLaw (edgeLawToAmbient e ν) e = edgeLawToAmbient e ν := by
  rw [← edgeLawToAmbient_ambientToEdgeLaw, ambientToEdgeLaw_edgeLawToAmbient]

/-- Literal local laws correspond exactly to ambient laws already restricted to the edge. -/
noncomputable def edgeLawEquiv (e : Finset V) :
    BooleanLaw {v // v ∈ e} ≃ {μ : BooleanLaw V // restrictLaw μ e = μ} where
  toFun ν := ⟨edgeLawToAmbient e ν, restrictLaw_edgeLawToAmbient e ν⟩
  invFun μ := ambientToEdgeLaw e μ.val
  left_inv := ambientToEdgeLaw_edgeLawToAmbient e
  right_inv μ := Subtype.ext ((edgeLawToAmbient_ambientToEdgeLaw e μ.val).trans μ.property)

 theorem moment_edgeLawToAmbient (e s : Finset V) (hs : s ⊆ e)
    (ν : BooleanLaw {v // v ∈ e}) :
    moment (edgeLawToAmbient e ν) s = moment ν (edgeProject e s) := by
  rw [moment, edgeLawToAmbient, Law.prob_map, moment]
  exact ν.prob_congr (fun x => subset_edgeEmbed_iff e s hs x)

 theorem moment_ambientToEdgeLaw (e s : Finset V) (hs : s ⊆ e) (μ : BooleanLaw V) :
    moment (ambientToEdgeLaw e μ) (edgeProject e s) = moment μ s := by
  rw [← moment_edgeLawToAmbient e s hs, edgeLawToAmbient_ambientToEdgeLaw,
    moment_restrict μ e s hs]

/-- The paper's local subset moments uniquely determine its literal edge law. -/
 theorem edge_law_eq_of_moments (e : Finset V)
    (μ ν : BooleanLaw {v // v ∈ e})
    (h : ∀ s, s ⊆ e → moment μ (edgeProject e s) = moment ν (edgeProject e s)) : μ = ν := by
  apply law_eq_of_moments
  intro t
  simpa only [edgeProject_edgeEmbed] using h (edgeEmbed e t) (edgeEmbed_subset e t)

/-- Finite hypergraphs in the paper have no isolated vertices and no edges of size below two. -/
@[ext] structure PaperHypergraph (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Finset V)
  edge_card : ∀ e ∈ edges, 2 ≤ e.card
  covers : ∀ v : V, ∃ e ∈ edges, v ∈ e

namespace PaperHypergraph
variable (H : PaperHypergraph V)

/-- Completion as hyperedges, excluding the empty set and singletons. -/
def completionEdges : Finset (Finset V) :=
  H.edges.biUnion (fun e => e.powerset.filter (fun f => 2 ≤ f.card))

@[simp] theorem mem_completionEdges (f : Finset V) :
    f ∈ H.completionEdges ↔ 2 ≤ f.card ∧ ∃ e ∈ H.edges, f ⊆ e := by
  simp only [completionEdges, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powerset]
  aesop

 theorem edges_subset_completionEdges : H.edges ⊆ H.completionEdges := by
  intro e he
  exact (H.mem_completionEdges e).mpr ⟨H.edge_card e he, e, he, Finset.Subset.refl _⟩

/-- Completion is itself a hypergraph under precisely the paper's conventions. -/
def completion : PaperHypergraph V where
  edges := H.completionEdges
  edge_card e he := ((H.mem_completionEdges e).mp he).1
  covers v := by
    obtain ⟨e, he, hv⟩ := H.covers v
    exact ⟨e, H.edges_subset_completionEdges he, hv⟩

 theorem completion_idempotent : H.completion.completion = H.completion := by
  have hedges : H.completion.completion.edges = H.completion.edges := by
    ext f
    change f ∈ H.completion.completionEdges ↔ f ∈ H.completionEdges
    rw [mem_completionEdges, mem_completionEdges]
    constructor
    · rintro ⟨hf, e, he, hfe⟩
      obtain ⟨_, g, hg, heg⟩ := (H.mem_completionEdges e).mp he
      exact ⟨hf, g, hg, hfe.trans heg⟩
    · rintro ⟨hf, e, he, hfe⟩
      exact ⟨hf, e, H.edges_subset_completionEdges he, hfe⟩
  exact PaperHypergraph.ext hedges

/-- Literal vertex-plus-edge indexing avoids identifying vertices with sets. -/
abbrev Coordinate := V ⊕ {e // e ∈ H.edges}
abbrev Vector := H.Coordinate → ℝ

/-- The paper's binary monomial set `MS(H)`. -/
def multilinearSet : Set H.Vector :=
  {z | (∀ c, z c = 0 ∨ z c = 1) ∧
    ∀ e, z (Sum.inr e) = paperMonomial e.val (fun v => z (Sum.inl v))}

/-- The paper's `MP(H)`, in its literal vertex-plus-edge coordinates. -/
def polytope : Set H.Vector := convexHull ℝ H.multilinearSet

/-- Coordinate support used by the existing development, including bookkeeping `∅`. -/
def coordinateSupport : Finset (Finset V) :=
  insert ∅ ((Finset.univ.image (fun v : V => {v})) ∪ H.edges)

@[simp] theorem mem_coordinateSupport (s : Finset V) :
    s ∈ H.coordinateSupport ↔ s = ∅ ∨ (∃ v : V, s = {v}) ∨ s ∈ H.edges := by
  simp [coordinateSupport, eq_comm]

 theorem singleton_mem_coordinateSupport (v : V) : {v} ∈ H.coordinateSupport :=
  (H.mem_coordinateSupport {v}).mpr (Or.inr (Or.inl ⟨v, rfl⟩))

 theorem edge_mem_coordinateSupport (e : {e // e ∈ H.edges}) : e.val ∈ H.coordinateSupport :=
  (H.mem_coordinateSupport e.val).mpr (Or.inr (Or.inr e.property))

/-- Drop only the bookkeeping coordinate and relabel singleton coordinates by vertices. -/
def toPaperLinear : MomentVector H.coordinateSupport →ₗ[ℝ] H.Vector where
  toFun z c := match c with
    | Sum.inl v => z ⟨{v}, H.singleton_mem_coordinateSupport v⟩
    | Sum.inr e => z ⟨e.val, H.edge_mem_coordinateSupport e⟩
  map_add' x y := by funext c; cases c <;> rfl
  map_smul' r x := by funext c; cases c <;> rfl

 theorem singleton_not_mem_edges (v : V) : {v} ∉ H.edges := by
  intro hv
  have hc := H.edge_card {v} hv
  simpa using hc

/-- Restore the empty coordinate to one and relabel the vertex coordinates. -/
noncomputable def fromPaper (z : H.Vector) : MomentVector H.coordinateSupport := fun s =>
  if h0 : s.val = ∅ then 1
  else if he : s.val ∈ H.edges then z (Sum.inr ⟨s.val, he⟩)
  else z (Sum.inl (Classical.choose
    ((((H.mem_coordinateSupport s.val).mp s.property).resolve_left h0).resolve_right he)))

@[simp] theorem fromPaper_empty (z : H.Vector) :
    H.fromPaper z ⟨∅, (H.mem_coordinateSupport ∅).mpr (Or.inl rfl)⟩ = 1 := by
  simp [fromPaper]

@[simp] theorem fromPaper_singleton (z : H.Vector) (v : V) :
    H.fromPaper z ⟨{v}, H.singleton_mem_coordinateSupport v⟩ = z (Sum.inl v) := by
  simp only [fromPaper, Finset.singleton_ne_empty, ↓reduceDIte, H.singleton_not_mem_edges]
  congr 2
  exact Finset.singleton_injective (Classical.choose_spec
    ((((H.mem_coordinateSupport {v}).mp (H.singleton_mem_coordinateSupport v)).resolve_left
      (Finset.singleton_ne_empty v)).resolve_right (H.singleton_not_mem_edges v))).symm

@[simp] theorem fromPaper_edge (z : H.Vector) (e : {e // e ∈ H.edges}) :
    H.fromPaper z ⟨e.val, H.edge_mem_coordinateSupport e⟩ = z (Sum.inr e) := by
  have hn : e.val ≠ ∅ := by
    intro he
    have hc := H.edge_card e.val e.property
    simp [he] at hc
  simp [fromPaper, hn, e.property]

@[simp] theorem toPaper_fromPaper (z : H.Vector) : H.toPaperLinear (H.fromPaper z) = z := by
  funext c
  cases c with
  | inl v => exact H.fromPaper_singleton z v
  | inr e => exact H.fromPaper_edge z e

 theorem fromPaper_toPaper (z : MomentVector H.coordinateSupport)
    (h0 : z ⟨∅, (H.mem_coordinateSupport ∅).mpr (Or.inl rfl)⟩ = 1) :
    H.fromPaper (H.toPaperLinear z) = z := by
  funext s
  rcases (H.mem_coordinateSupport s.val).mp s.property with h | ⟨v, h⟩ | h
  · rcases s with ⟨s, hs⟩
    dsimp at h
    subst s
    simpa only [fromPaper_empty] using h0.symm
  · rcases s with ⟨s, hs⟩
    dsimp at h
    subst s
    exact H.fromPaper_singleton _ v
  · exact H.fromPaper_edge _ ⟨s.val, h⟩

/-- Exact bijection between literal paper vectors and normalized moment coordinates. -/
noncomputable def normalizedCoordinateEquiv : H.Vector ≃
    {z : MomentVector H.coordinateSupport //
      z ⟨∅, (H.mem_coordinateSupport ∅).mpr (Or.inl rfl)⟩ = 1} where
  toFun z := ⟨H.fromPaper z, H.fromPaper_empty z⟩
  invFun z := H.toPaperLinear z.val
  left_inv := H.toPaper_fromPaper
  right_inv z := Subtype.ext (H.fromPaper_toPaper z.val z.property)

/-- The deterministic lift in the paper's coordinates. -/
noncomputable def lift (x : Finset V) : H.Vector := H.toPaperLinear (monomialLift H.coordinateSupport x)

@[simp] theorem lift_vertex (x : Finset V) (v : V) : H.lift x (Sum.inl v) = binaryVector x v := by
  simp [lift, toPaperLinear, monomialLift, binaryVector]

@[simp] theorem lift_edge (x : Finset V) (e : {e // e ∈ H.edges}) :
    H.lift x (Sum.inr e) = paperMonomial e.val (binaryVector x) := by
  simp [lift, toPaperLinear, monomialLift, paperMonomial_binaryVector]

 theorem multilinearSet_eq_range_lift : H.multilinearSet = Set.range H.lift := by
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    let x : Finset V := Finset.univ.filter (fun v => z (Sum.inl v) = 1)
    have hx (v : V) : binaryVector x v = z (Sum.inl v) := by
      rcases hz (Sum.inl v) with h | h <;> simp [binaryVector, x, h]
    refine ⟨x, ?_⟩
    funext c
    cases c with
    | inl v => simpa using hx v
    | inr e => rw [lift_edge, hm e]
               exact congrArg (paperMonomial e.val) (funext hx)
  · rintro ⟨x, rfl⟩
    constructor
    · intro c
      cases c with
      | inl v => rw [lift_vertex]; unfold binaryVector; split_ifs <;> simp
      | inr e => rw [lift_edge, paperMonomial_binaryVector]; split_ifs <;> simp
    · intro e
      simp only [lift_edge, lift_vertex]

 theorem polytope_eq_image_multilinearPolytope :
    H.polytope = H.toPaperLinear '' multilinearPolytope H.coordinateSupport := by
  rw [polytope, multilinearSet_eq_range_lift, multilinearPolytope,
    H.toPaperLinear.image_convexHull]
  congr 1
  exact Set.range_comp H.toPaperLinear (monomialLift H.coordinateSupport)

/-- The probabilistic representation lemma for every finite hypergraph in the paper. -/
 theorem mem_polytope_iff (z : H.Vector) : z ∈ H.polytope ↔
    ∃ μ : BooleanLaw V,
      (∀ v, z (Sum.inl v) = moment μ {v}) ∧
      ∀ e, z (Sum.inr e) = moment μ e.val := by
  rw [polytope_eq_image_multilinearPolytope]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨μ, rfl⟩ := (mem_multilinearPolytope_iff _ _).mp hy
    exact ⟨μ, fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨μ, hv, he⟩
    refine ⟨momentVector H.coordinateSupport μ,
      (mem_multilinearPolytope_iff _ _).mpr ⟨μ, rfl⟩, ?_⟩
    funext c
    cases c with
    | inl v => exact (hv v).symm
    | inr e => exact (he e).symm

/-- The literal expected-product form of the probabilistic representation. -/
 theorem mem_polytope_iff_expectation (z : H.Vector) : z ∈ H.polytope ↔
    ∃ μ : BooleanLaw V,
      (∀ v, z (Sum.inl v) = ∑ x, μ.mass x * binaryVector x v) ∧
      ∀ e, z (Sum.inr e) = ∑ x, μ.mass x * paperMonomial e.val (binaryVector x) := by
  simp only [mem_polytope_iff, moment_eq_expected_monomial, paperMonomial_singleton]

 theorem mem_polytope_iff_fromPaper (z : H.Vector) :
    z ∈ H.polytope ↔ H.fromPaper z ∈ multilinearPolytope H.coordinateSupport := by
  constructor
  · intro hz
    obtain ⟨μ, hv, he⟩ := (H.mem_polytope_iff z).mp hz
    apply (mem_multilinearPolytope_iff _ _).mpr
    refine ⟨μ, ?_⟩
    have hp : H.toPaperLinear (momentVector H.coordinateSupport μ) = z := by
      funext c
      cases c with
      | inl v => exact (hv v).symm
      | inr e => exact (he e).symm
    rw [← hp, H.fromPaper_toPaper]
    exact moment_empty μ
  · intro hz
    rw [H.polytope_eq_image_multilinearPolytope]
    exact ⟨H.fromPaper z, hz, H.toPaper_fromPaper z⟩

/-- A three-edge generating hypergraph with exactly its covered vertices. -/
def ofThree (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) : PaperHypergraph V where
  edges := Finset.univ.image e
  edge_card s hs := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    exact hc.two_le_card i
  covers v := by
    obtain ⟨i, hi⟩ := hv v
    exact ⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hi⟩

 theorem ofThree_completion_edges (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (s : Finset V) :
    s ∈ (ofThree e hc hv).completion.edges ↔
      s ∈ completedSupport e ∧ 2 ≤ s.card := by
  change s ∈ (ofThree e hc hv).completionEdges ↔ _
  simp [mem_completedSupport, ofThree, and_comm, and_left_comm, and_assoc]

 theorem ofThree_completion_coordinateSupport (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    (ofThree e hc hv).completion.coordinateSupport = completedSupport e := by
  ext s
  rw [mem_coordinateSupport]
  constructor
  · rintro (rfl | ⟨v, rfl⟩ | hs)
    · exact mem_completedSupport_of_subset e 0 ∅ (Finset.empty_subset _)
    · obtain ⟨i, hi⟩ := hv v
      exact mem_completedSupport_of_subset e i {v} (Finset.singleton_subset_iff.mpr hi)
    · exact ((ofThree_completion_edges e hc hv s).mp hs).1
  · intro hs
    by_cases h0 : s.card = 0
    · exact Or.inl (Finset.card_eq_zero.mp h0)
    by_cases h1 : s.card = 1
    · exact Or.inr (Or.inl (Finset.card_eq_one.mp h1))
    · exact Or.inr (Or.inr ((ofThree_completion_edges e hc hv s).mpr ⟨hs, by omega⟩))

end PaperHypergraph
end AlphaCycle
