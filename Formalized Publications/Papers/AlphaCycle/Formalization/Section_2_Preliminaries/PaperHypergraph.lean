import Section_2_Preliminaries.PaperCoordinates
import Section_2_Preliminaries.MomentConverse

/-! The complete-edge/local-law dictionary for arbitrary completed finite hypergraphs. -/
namespace AlphaCycle.PaperHypergraph
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : PaperHypergraph V)

/-- Downward closure of hyperedges, with the paper's cardinality restriction. -/
def IsComplete : Prop :=
  ∀ e ∈ H.edges, ∀ s, s ⊆ e → 2 ≤ s.card → s ∈ H.edges

 theorem completion_isComplete : H.completion.IsComplete := by
  intro e he s hs hcard
  obtain ⟨_, f, hf, hef⟩ := (H.mem_completionEdges e).mp he
  exact (H.mem_completionEdges s).mpr ⟨hcard, f, hf, hs.trans hef⟩

 theorem isComplete_iff_completion_eq : H.IsComplete ↔ H.completion = H := by
  constructor
  · intro h
    apply PaperHypergraph.ext
    apply Finset.Subset.antisymm
    · intro s hs
      obtain ⟨hc, e, he, hse⟩ := (H.mem_completionEdges s).mp hs
      exact h e he s hse hc
    · exact H.edges_subset_completionEdges
  · intro h
    rw [← h]
    exact H.completion_isComplete

/-- Inclusion-wise maximal hyperedges. -/
noncomputable def maximalEdges : Finset (Finset V) :=
  H.edges.filter (fun e => ∀ f ∈ H.edges, e ⊆ f → f = e)

@[simp] theorem mem_maximalEdges (e : Finset V) :
    e ∈ H.maximalEdges ↔ e ∈ H.edges ∧ ∀ f ∈ H.edges, e ⊆ f → f = e := by
  simp [maximalEdges]

 theorem edge_subset_maximal (e : Finset V) (he : e ∈ H.edges) :
    ∃ f ∈ H.maximalEdges, e ⊆ f := by
  let supers := H.edges.filter (fun f => e ⊆ f)
  have hn : supers.Nonempty := ⟨e, by simp [supers, he]⟩
  obtain ⟨f, hf, hmax⟩ := Finset.exists_max_image supers Finset.card hn
  obtain ⟨hfE, hef⟩ := Finset.mem_filter.mp hf
  refine ⟨f, (H.mem_maximalEdges f).mpr ⟨hfE, ?_⟩, hef⟩
  intro g hg hfg
  symm
  apply Finset.eq_of_subset_of_card_le hfg
  exact hmax g (Finset.mem_filter.mpr ⟨hg, hef.trans hfg⟩)

 theorem vertex_mem_maximal (v : V) : ∃ e ∈ H.maximalEdges, v ∈ e := by
  obtain ⟨e, he, hv⟩ := H.covers v
  obtain ⟨f, hf, hef⟩ := H.edge_subset_maximal e he
  exact ⟨f, hf, hef hv⟩

 theorem subset_mem_coordinateSupport (hc : H.IsComplete) (e : Finset V)
    (he : e ∈ H.edges) (s : Finset V) (hs : s ⊆ e) : s ∈ H.coordinateSupport := by
  apply (H.mem_coordinateSupport s).mpr
  by_cases h0 : s.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp h0)
  by_cases h1 : s.card = 1
  · exact Or.inr (Or.inl (Finset.card_eq_one.mp h1))
  · exact Or.inr (Or.inr (hc e he s hs (by omega)))

/-- All nonempty coordinates occur in an inclusion-maximal edge. -/
 theorem coordinate_subset_maximal (s : Finset V) (hs : s ∈ H.coordinateSupport)
    (hn : s ≠ ∅) : ∃ e ∈ H.maximalEdges, s ⊆ e := by
  rcases (H.mem_coordinateSupport s).mp hs with h0 | ⟨v, rfl⟩ | he
  · exact (hn h0).elim
  · obtain ⟨e, he, hv⟩ := H.vertex_mem_maximal v
    exact ⟨e, he, Finset.singleton_subset_iff.mpr hv⟩
  · exact H.edge_subset_maximal s he

/-- A total extension of the paper's monomial coordinates; only supported subsets are used. -/
noncomputable def momentCoordinate (z : H.Vector) (s : Finset V) : ℝ :=
  if hs : s ∈ H.coordinateSupport then H.fromPaper z ⟨s, hs⟩ else 0

 theorem momentCoordinate_supported (z : H.Vector) (s : Finset V)
    (hs : s ∈ H.coordinateSupport) : H.momentCoordinate z s = H.fromPaper z ⟨s, hs⟩ := by
  simp [momentCoordinate, hs]

@[simp] theorem momentCoordinate_empty (z : H.Vector) : H.momentCoordinate z ∅ = 1 := by
  simp [momentCoordinate]

@[simp] theorem momentCoordinate_singleton (z : H.Vector) (v : V) :
    H.momentCoordinate z {v} = z (Sum.inl v) := by
  rw [H.momentCoordinate_supported z {v} (H.singleton_mem_coordinateSupport v)]
  exact H.fromPaper_singleton z v

@[simp] theorem momentCoordinate_edge (z : H.Vector) (e : {e // e ∈ H.edges}) :
    H.momentCoordinate z e.val = z (Sum.inr e) := by
  rw [H.momentCoordinate_supported z e.val (H.edge_mem_coordinateSupport e)]
  exact H.fromPaper_edge z e

/-- The paper's CER definition, using its inclusion-maximal edges. -/
def completeEdgeRelaxation : Set H.Vector :=
  {z | ∀ e ∈ H.maximalEdges, ∃ μ : BooleanLaw V,
    ∀ s, s ⊆ e → moment μ s = H.momentCoordinate z s}

/-- Replacing ambient witnesses by literal laws on `{0,1}^e` changes no constraint. -/
 theorem mem_completeEdgeRelaxation_iff_edge_laws (z : H.Vector) :
    z ∈ H.completeEdgeRelaxation ↔
      ∀ e ∈ H.maximalEdges, ∃ ν : BooleanLaw {v // v ∈ e},
        ∀ s, s ⊆ e → moment ν (edgeProject e s) = H.momentCoordinate z s := by
  constructor
  · intro h e he
    obtain ⟨μ, hμ⟩ := h e he
    exact ⟨ambientToEdgeLaw e μ, fun s hs => (moment_ambientToEdgeLaw e s hs μ).trans (hμ s hs)⟩
  · intro h e he
    obtain ⟨ν, hν⟩ := h e he
    exact ⟨edgeLawToAmbient e ν, fun s hs => (moment_edgeLawToAmbient e s hs ν).trans (hν s hs)⟩

/-- The finite complete-edge inequalities are precisely nonnegativity of every inverse cell. -/
 theorem mem_completeEdgeRelaxation_iff_inverseCell_nonneg (z : H.Vector) :
    z ∈ H.completeEdgeRelaxation ↔
      ∀ e ∈ H.maximalEdges, ∀ O, O ⊆ e → 0 ≤ inverseCell e (H.momentCoordinate z) O := by
  constructor
  · intro hz e he
    exact ((exists_law_with_moments_iff e (H.momentCoordinate z)).mp (hz e he)).2
  · intro hz e he
    exact (exists_law_with_moments_iff e (H.momentCoordinate z)).mpr
      ⟨H.momentCoordinate_empty z, hz e he⟩

/-- CER is the intersection of the exact full-edge multilinear polytopes. -/
 theorem mem_completeEdgeRelaxation_iff_edge_polytopes (z : H.Vector) :
    z ∈ H.completeEdgeRelaxation ↔
      ∀ e ∈ H.maximalEdges,
        (fun s : {s // s ∈ e.powerset} => H.momentCoordinate z s.val) ∈
          multilinearPolytope e.powerset := by
  constructor
  · intro hz e he
    obtain ⟨μ, hμ⟩ := hz e he
    apply (mem_multilinearPolytope_iff _ _).mpr
    refine ⟨μ, ?_⟩
    funext s
    exact hμ s.val (Finset.mem_powerset.mp s.property)
  · intro hz e he
    obtain ⟨μ, hμ⟩ := (mem_multilinearPolytope_iff _ _).mp (hz e he)
    exact ⟨μ, fun s hs => congrFun hμ ⟨s, Finset.mem_powerset.mpr hs⟩⟩

/-- Adding the bookkeeping empty moment does not change the paper's nonempty constraints. -/
 theorem mem_completeEdgeRelaxation_iff_nonempty_edge_laws (z : H.Vector) :
    z ∈ H.completeEdgeRelaxation ↔
      ∀ e ∈ H.maximalEdges, ∃ ν : BooleanLaw {v // v ∈ e},
        ∀ s, s ⊆ e → s.Nonempty →
          moment ν (edgeProject e s) = H.momentCoordinate z s := by
  rw [H.mem_completeEdgeRelaxation_iff_edge_laws]
  constructor
  · intro h e he
    obtain ⟨ν, hν⟩ := h e he
    exact ⟨ν, fun s hs _ => hν s hs⟩
  · intro h e he
    obtain ⟨ν, hν⟩ := h e he
    refine ⟨ν, ?_⟩
    intro s hs
    by_cases hn : s.Nonempty
    · exact hν s hs hn
    · have h0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst s
      have hp : edgeProject e ∅ = ∅ := by ext v; simp
      simp [hp]

/-- Consistency on overlaps follows from the shared subset coordinates. -/
 theorem local_witnesses_consistent (z : H.Vector)
    (μ : {e // e ∈ H.maximalEdges} → BooleanLaw V)
    (hμ : ∀ e s, s ⊆ e.val → moment (μ e) s = H.momentCoordinate z s)
    (e f : {e // e ∈ H.maximalEdges}) :
    restrictLaw (μ e) (e.val ∩ f.val) = restrictLaw (μ f) (e.val ∩ f.val) := by
  apply restrictLaw_eq_of_moments
  intro s hs
  obtain ⟨hse, hsf⟩ := Finset.subset_inter_iff.mp hs
  rw [hμ e s hse, hμ f s hsf]

 theorem mem_completeEdgeRelaxation_iff_consistent (z : H.Vector) :
    z ∈ H.completeEdgeRelaxation ↔
      ∃ μ : {e // e ∈ H.maximalEdges} → BooleanLaw V,
        (∀ e s, s ⊆ e.val → moment (μ e) s = H.momentCoordinate z s) ∧
        ∀ e f, restrictLaw (μ e) (e.val ∩ f.val) = restrictLaw (μ f) (e.val ∩ f.val) := by
  constructor
  · intro h
    have hex (e : {e // e ∈ H.maximalEdges}) := h e.val e.property
    choose μ hμ using hex
    exact ⟨μ, hμ, H.local_witnesses_consistent z μ hμ⟩
  · rintro ⟨μ, hμ, _⟩ e he
    exact ⟨μ ⟨e, he⟩, hμ ⟨e, he⟩⟩

/-- Choose one containing maximal edge for every nonempty moment coordinate. -/
noncomputable def localMomentVector
    (μ : {e // e ∈ H.maximalEdges} → BooleanLaw V) : MomentVector H.coordinateSupport := fun s =>
  if h0 : s.val = ∅ then 1 else
    let f := Classical.choose (H.coordinate_subset_maximal s.val s.property h0)
    moment (μ ⟨f, (Classical.choose_spec
      (H.coordinate_subset_maximal s.val s.property h0)).1⟩) s.val

 theorem localMomentVector_empty (μ : {e // e ∈ H.maximalEdges} → BooleanLaw V) :
    H.localMomentVector μ ⟨∅, (H.mem_coordinateSupport ∅).mpr (Or.inl rfl)⟩ = 1 := by
  simp [localMomentVector]

 theorem localMomentVector_eq (hc : H.IsComplete)
    (μ : {e // e ∈ H.maximalEdges} → BooleanLaw V)
    (hμ : ∀ e f, restrictLaw (μ e) (e.val ∩ f.val) = restrictLaw (μ f) (e.val ∩ f.val))
    (e : {e // e ∈ H.maximalEdges}) (s : Finset V) (hs : s ⊆ e.val) :
    moment (μ e) s = H.localMomentVector μ
      ⟨s, H.subset_mem_coordinateSupport hc e.val ((H.mem_maximalEdges e.val).mp e.property).1 s hs⟩ := by
  by_cases h0 : s = ∅
  · subst s
    simp [localMomentVector]
  · let hsup := H.subset_mem_coordinateSupport hc e.val
      ((H.mem_maximalEdges e.val).mp e.property).1 s hs
    let f := Classical.choose (H.coordinate_subset_maximal s hsup h0)
    have hf := Classical.choose_spec (H.coordinate_subset_maximal s hsup h0)
    have hinter : s ⊆ e.val ∩ f := Finset.subset_inter hs hf.2
    have hm := congrArg (fun ν => moment ν s) (hμ e ⟨f, hf.1⟩)
    simp only [moment_restrict _ _ _ hinter] at hm
    simpa only [localMomentVector, h0, ↓reduceDIte] using hm

/-- Any consistent family of maximal-edge laws constructs a point of CER. -/
 theorem consistent_laws_construct_vector (hc : H.IsComplete)
    (μ : {e // e ∈ H.maximalEdges} → BooleanLaw V)
    (hμ : ∀ e f, restrictLaw (μ e) (e.val ∩ f.val) = restrictLaw (μ f) (e.val ∩ f.val)) :
    ∃ z : H.Vector, z ∈ H.completeEdgeRelaxation ∧
      ∀ e s, s ⊆ e.val → moment (μ e) s = H.momentCoordinate z s := by
  let z := H.toPaperLinear (H.localMomentVector μ)
  have heq (e : {e // e ∈ H.maximalEdges}) (s : Finset V) (hs : s ⊆ e.val) :
      moment (μ e) s = H.momentCoordinate z s := by
    have hsup := H.subset_mem_coordinateSupport hc e.val
      ((H.mem_maximalEdges e.val).mp e.property).1 s hs
    rw [H.momentCoordinate_supported z s hsup]
    dsimp only [z]
    rw [H.fromPaper_toPaper (H.localMomentVector μ) (H.localMomentVector_empty μ)]
    exact H.localMomentVector_eq hc μ hμ e s hs
  refine ⟨z, ?_, heq⟩
  intro e he
  exact ⟨μ ⟨e, he⟩, heq ⟨e, he⟩⟩

/-- On a completed hypergraph, CER local laws admit a common law exactly in `MP(H)`. -/
 theorem mem_polytope_iff_realizes (hc : H.IsComplete) (z : H.Vector)
    (ν : {e // e ∈ H.maximalEdges} → BooleanLaw V)
    (hν : ∀ e s, s ⊆ e.val → moment (ν e) s = H.momentCoordinate z s) :
    z ∈ H.polytope ↔ ∃ μ : BooleanLaw V,
      ∀ e, restrictLaw μ e.val = restrictLaw (ν e) e.val := by
  constructor
  · intro hz
    obtain ⟨μ, hμ⟩ := (mem_multilinearPolytope_iff _ _).mp
      ((H.mem_polytope_iff_fromPaper z).mp hz)
    refine ⟨μ, ?_⟩
    intro e
    apply restrictLaw_eq_of_moments
    intro s hs
    rw [hν e s hs]
    have hsup := H.subset_mem_coordinateSupport hc e.val
      ((H.mem_maximalEdges e.val).mp e.property).1 s hs
    rw [H.momentCoordinate_supported z s hsup]
    exact congrFun hμ ⟨s, hsup⟩
  · rintro ⟨μ, hμ⟩
    apply (H.mem_polytope_iff_fromPaper z).mpr
    apply (mem_multilinearPolytope_iff _ _).mpr
    refine ⟨μ, ?_⟩
    funext s
    by_cases h0 : s.val = ∅
    · rcases s with ⟨s, hs⟩
      dsimp at h0
      subst s
      change moment μ ∅ = H.fromPaper z ⟨∅, hs⟩
      simp
    · obtain ⟨e, he, hse⟩ := H.coordinate_subset_maximal s.val s.property h0
      have hr := congrArg (fun ξ => moment ξ s.val) (hμ ⟨e, he⟩)
      rw [moment_restrict μ e s.val hse,
        moment_restrict (ν ⟨e, he⟩) e s.val hse,
        hν ⟨e, he⟩ s.val hse,
        H.momentCoordinate_supported z s.val s.property] at hr
      exact hr

 theorem polytope_subset_completeEdgeRelaxation (hc : H.IsComplete) :
    H.polytope ⊆ H.completeEdgeRelaxation := by
  intro z hz
  obtain ⟨μ, hμ⟩ := (mem_multilinearPolytope_iff _ _).mp
    ((H.mem_polytope_iff_fromPaper z).mp hz)
  intro e he
  refine ⟨μ, ?_⟩
  intro s hs
  have hsup := H.subset_mem_coordinateSupport hc e ((H.mem_maximalEdges e).mp he).1 s hs
  rw [H.momentCoordinate_supported z s hsup]
  exact congrFun hμ ⟨s, hsup⟩

/-- The only maximal completed hyperedges are the three generating edges. -/
 theorem ofThree_completion_maximalEdges (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i) :
    (ofThree e hc hv).completion.maximalEdges = Finset.univ.image e := by
  ext s
  rw [mem_maximalEdges]
  constructor
  · rintro ⟨hs, hmax⟩
    obtain ⟨hsup, _⟩ := (ofThree_completion_edges e hc hv s).mp hs
    obtain ⟨i, hi⟩ := (mem_completedSupport e s).mp hsup
    have hei : e i ∈ (ofThree e hc hv).completion.edges :=
      (ofThree_completion_edges e hc hv (e i)).mpr
        ⟨mem_completedSupport_of_subset e i (e i) (Finset.Subset.refl _), hc.two_le_card i⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hmax (e i) hei hi⟩
  · intro hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    refine ⟨(ofThree_completion_edges e hc hv (e i)).mpr
      ⟨mem_completedSupport_of_subset e i (e i) (Finset.Subset.refl _), hc.two_le_card i⟩, ?_⟩
    intro f hf hif
    obtain ⟨hfsup, _⟩ := (ofThree_completion_edges e hc hv f).mp hf
    obtain ⟨j, hfj⟩ := (mem_completedSupport e f).mp hfsup
    have hij : i = j := by
      by_contra hn
      exact hc.incomparable i j hn (hif.trans hfj)
    subst j
    exact Finset.Subset.antisymm hfj hif

/-- The literal paper vector in the existing development's completed-support coordinates. -/
noncomputable def cycleCoordinates (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : (ofThree e hc hv).completion.Vector) :
    MomentVector (completedSupport e) := fun s =>
  (ofThree e hc hv).completion.momentCoordinate z s.val

 theorem cycleCoordinates_eq_fromPaper (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : (ofThree e hc hv).completion.Vector)
    (s : Finset V) (hs : s ∈ completedSupport e) :
    cycleCoordinates e hc hv z ⟨s, hs⟩ =
      (ofThree e hc hv).completion.fromPaper z
        ⟨s, by rw [ofThree_completion_coordinateSupport e hc hv]; exact hs⟩ := by
  exact (ofThree e hc hv).completion.momentCoordinate_supported z s
    (by rw [ofThree_completion_coordinateSupport e hc hv]; exact hs)

/-- Exact equivalence of the literal paper MP and the existing three-edge MP. -/
 theorem ofThree_mem_polytope_iff (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : (ofThree e hc hv).completion.Vector) :
    z ∈ (ofThree e hc hv).completion.polytope ↔
      cycleCoordinates e hc hv z ∈ multilinearPolytope (completedSupport e) := by
  rw [mem_polytope_iff_fromPaper, mem_multilinearPolytope_iff, mem_multilinearPolytope_iff]
  constructor
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    funext s
    rw [cycleCoordinates_eq_fromPaper]
    exact congrFun hμ ⟨s.val, by
      rw [ofThree_completion_coordinateSupport e hc hv]; exact s.property⟩
  · rintro ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    funext s
    have hs : s.val ∈ completedSupport e := by
      rw [← ofThree_completion_coordinateSupport e hc hv]
      exact s.property
    have hm := congrFun hμ ⟨s.val, hs⟩
    rw [cycleCoordinates_eq_fromPaper] at hm
    exact hm

/-- Exact equivalence of the literal maximal-edge CER and the existing three-edge CER. -/
 theorem ofThree_mem_completeEdgeRelaxation_iff (e : Fin 3 → Finset V)
    (hc : Geometry.IsCycle e) (hv : ∀ v, ∃ i, v ∈ e i)
    (z : (ofThree e hc hv).completion.Vector) :
    z ∈ (ofThree e hc hv).completion.completeEdgeRelaxation ↔
      cycleCoordinates e hc hv z ∈ AlphaCycle.completeEdgeRelaxation e := by
  constructor
  · intro h i
    have hi : e i ∈ (ofThree e hc hv).completion.maximalEdges := by
      rw [ofThree_completion_maximalEdges]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨μ, hμ⟩ := h (e i) hi
    exact ⟨μ, hμ⟩
  · intro h s hs
    rw [ofThree_completion_maximalEdges] at hs
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨μ, hμ⟩ := h i
    exact ⟨μ, hμ⟩

/-- The reverse relabeling from the existing three-edge moment coordinates. -/
noncomputable def cycleFromMoment (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : MomentVector (completedSupport e)) :
    (ofThree e hc hv).completion.Vector :=
  (ofThree e hc hv).completion.toPaperLinear (fun s =>
    z ⟨s.val, by rw [← ofThree_completion_coordinateSupport e hc hv]; exact s.property⟩)

 theorem cycleFromMoment_cycleCoordinates (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : (ofThree e hc hv).completion.Vector) :
    cycleFromMoment e hc hv (cycleCoordinates e hc hv z) = z := by
  unfold cycleFromMoment
  have h : (fun s : {s // s ∈ (ofThree e hc hv).completion.coordinateSupport} =>
      cycleCoordinates e hc hv z
        ⟨s.val, by rw [← ofThree_completion_coordinateSupport e hc hv]; exact s.property⟩) =
      (ofThree e hc hv).completion.fromPaper z := by
    funext s
    exact cycleCoordinates_eq_fromPaper e hc hv z s.val _
  rw [h, toPaper_fromPaper]

 theorem cycleCoordinates_cycleFromMoment (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) (z : MomentVector (completedSupport e))
    (h0 : z ⟨∅, mem_completedSupport_of_subset e 0 ∅ (Finset.empty_subset _)⟩ = 1) :
    cycleCoordinates e hc hv (cycleFromMoment e hc hv z) = z := by
  funext s
  rw [cycleCoordinates_eq_fromPaper]
  unfold cycleFromMoment
  rw [fromPaper_toPaper]
  exact h0

/-- Exact equivalence including the bookkeeping normalization for the generating cycle. -/
noncomputable def cycleCoordinateEquiv (e : Fin 3 → Finset V) (hc : Geometry.IsCycle e)
    (hv : ∀ v, ∃ i, v ∈ e i) : (ofThree e hc hv).completion.Vector ≃
      {z : MomentVector (completedSupport e) //
        z ⟨∅, mem_completedSupport_of_subset e 0 ∅ (Finset.empty_subset _)⟩ = 1} where
  toFun z := ⟨cycleCoordinates e hc hv z, (ofThree e hc hv).completion.momentCoordinate_empty z⟩
  invFun z := cycleFromMoment e hc hv z.val
  left_inv := cycleFromMoment_cycleCoordinates e hc hv
  right_inv z := Subtype.ext (cycleCoordinates_cycleFromMoment e hc hv z.val z.property)

end AlphaCycle.PaperHypergraph
