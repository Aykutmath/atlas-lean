import Section_2_Preliminaries.Relaxation
import Section_5_Positive.Singleton

/-! Switched distinguished inequalities imply the exact per-common-state slice
conditions used by the positive construction. -/
namespace AlphaCycle.SliceBridge
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem pair_mass_event {T : Type*} [Fintype T] [DecidableEq T]
    (μ : Law (T × Bool × Bool)) (t : T) :
    (∑ i : Bool, ∑ j : Bool, μ.mass (t, i, j)) = μ.prob (fun x => x.1 = t) := by
  unfold Law.prob
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hu
    simp [hu]
  · simp

 theorem pair_a_event {T : Type*} [Fintype T] [DecidableEq T]
    (μ : Law (T × Bool × Bool)) (t : T) :
    (∑ j : Bool, μ.mass (t, true, j)) = μ.prob (fun x => x.1 = t ∧ x.2.1 = true) := by
  simp [Law.prob, Fintype.sum_prod_type, Finset.sum_add_distrib]

 theorem pair_b_event {T : Type*} [Fintype T] [DecidableEq T]
    (μ : Law (T × Bool × Bool)) (t : T) :
    (∑ i : Bool, μ.mass (t, i, true)) = μ.prob (fun x => x.1 = t ∧ x.2.2 = true) := by
  simp [Law.prob, Fintype.sum_prod_type, Finset.sum_add_distrib]

 theorem pair_ab_event {T : Type*} [Fintype T] [DecidableEq T]
    (μ : Law (T × Bool × Bool)) (t : T) :
    μ.mass (t, true, true) =
      μ.prob (fun x => x.1 = t ∧ x.2.1 = true ∧ x.2.2 = true) := by
  simp [Law.prob, Fintype.sum_prod_type, Finset.sum_add_distrib]

 theorem slice_literal_iff (T S t x : Finset V) (ht : t ⊆ T)
    (hs : Disjoint S T) :
    ((T ∪ S) \ (T \ t) ⊆ x ∧ Disjoint ((T ∪ S) ∩ (T \ t)) x) ↔
      x ∩ T = t ∧ S ⊆ x := by
  constructor
  · rintro ⟨hp, hn⟩
    constructor
    · apply Finset.ext
      intro v
      constructor
      · intro hv
        obtain ⟨hx, hT⟩ := Finset.mem_inter.mp hv
        by_contra hnt
        exact Finset.disjoint_left.mp hn
          (Finset.mem_inter.mpr ⟨Finset.mem_union_left S hT,
            Finset.mem_sdiff.mpr ⟨hT, hnt⟩⟩) hx
      · intro hv
        apply Finset.mem_inter.mpr
        refine ⟨hp ?_, ht hv⟩
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left S (ht hv),
          fun h => (Finset.mem_sdiff.mp h).2 hv⟩
    · intro v hv
      apply hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right T hv, ?_⟩
      intro h
      exact Finset.disjoint_left.mp hs hv (Finset.mem_sdiff.mp h).1
  · rintro ⟨hxt, hS⟩
    constructor
    · intro v hv
      obtain ⟨hTS, hn⟩ := Finset.mem_sdiff.mp hv
      rcases Finset.mem_union.mp hTS with hT | hS'
      · have hvt : v ∈ t := by
          by_contra hnt
          exact hn (Finset.mem_sdiff.mpr ⟨hT, hnt⟩)
        rw [← hxt] at hvt
        exact (Finset.mem_inter.mp hvt).1
      · exact hS hS'
    · rw [Finset.disjoint_left]
      intro v hv hx
      obtain ⟨_, hvT⟩ := Finset.mem_inter.mp hv
      obtain ⟨hT, hnt⟩ := Finset.mem_sdiff.mp hvT
      apply hnt
      rw [← hxt]
      exact Finset.mem_inter.mpr ⟨hx, hT⟩

 theorem switch_slice (e : Fin 3 → Finset V)
    (z : MomentVector (completedSupport e)) (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i s (hs : s ⊆ e i),
      moment (μ i) s = z ⟨s, mem_completedSupport_of_subset e i s hs⟩)
    (i : Fin 3) (T S t : Finset V) (ht : t ⊆ T) (hs : Disjoint S T)
    (hTS : T ∪ S ⊆ e i) :
    switchVector e (T \ t) z
      ⟨T ∪ S, mem_completedSupport_of_subset e i (T ∪ S) hTS⟩ =
      (μ i).prob (fun x => x ∩ T = t ∧ S ⊆ x) := by
  rw [switchVector_local_probability e (T \ t) z (μ i) i (hμ i)]
  · apply Law.prob_congr
    intro x
    exact slice_literal_iff T S t x ht hs
  · exact hTS

 theorem core_moments (T : Finset V) (a b c : V)
    (μab μac μbc : BooleanLaw V)
    (hc : (Singleton.coreFamily T a b c μab μac μbc).Consistent)
    (t : Finset V) :
    let p := Positive.moments (Positive.ofCoreFamily
      (Singleton.coreFamily T a b c μab μac μbc) hc) t
    p.mass = μab.prob (fun x => x ∩ T = t) ∧
    p.a = μab.prob (fun x => x ∩ T = t ∧ a ∈ x) ∧
    p.b = μab.prob (fun x => x ∩ T = t ∧ b ∈ x) ∧
    p.c = μac.prob (fun x => x ∩ T = t ∧ c ∈ x) ∧
    p.ab = μab.prob (fun x => x ∩ T = t ∧ a ∈ x ∧ b ∈ x) ∧
    p.ac = μac.prob (fun x => x ∩ T = t ∧ a ∈ x ∧ c ∈ x) ∧
    p.bc = μbc.prob (fun x => x ∩ T = t ∧ b ∈ x ∧ c ∈ x) := by
  change (∑ i : Bool, ∑ j : Bool, (μab.map (Singleton.project T a b)).mass (t,i,j)) = _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pair_mass_event, Law.prob_map]
    rfl
  · change (∑ j : Bool, (μab.map (Singleton.project T a b)).mass (t,true,j)) = _
    rw [pair_a_event, Law.prob_map]
    apply Law.prob_congr
    intro x
    simp [Singleton.project]
  · change (∑ i : Bool, (μab.map (Singleton.project T a b)).mass (t,i,true)) = _
    rw [pair_b_event, Law.prob_map]
    apply Law.prob_congr
    intro x
    simp [Singleton.project]
  · change (∑ i : Bool, (μac.map (Singleton.project T a c)).mass (t,i,true)) = _
    rw [pair_b_event, Law.prob_map]
    apply Law.prob_congr
    intro x
    simp [Singleton.project]
  · change (μab.map (Singleton.project T a b)).mass (t,true,true) = _
    rw [pair_ab_event, Law.prob_map]
    apply Law.prob_congr
    intro x
    simp [Singleton.project]
  · change (μac.map (Singleton.project T a c)).mass (t,true,true) = _
    rw [pair_ab_event, Law.prob_map]
    apply Law.prob_congr
    intro x
    simp [Singleton.project]
  · change (μbc.map (Singleton.project T b c)).mass (t,true,true) = _
    rw [pair_ab_event, Law.prob_map]
    apply Law.prob_congr
    intro x
    simp [Singleton.project]

/-- The paper's distinguished switched inequalities supply all seven moments
in every common-block slice, including zero-mass unsupported slices. -/
 theorem triangleConditions_of_distinguished (e : Fin 3 → Finset V)
    (f : SupportedCycle e) (z : MomentVector (completedSupport e))
    (hz : z ∈ distinguishedRelaxation e f) (μ : Fin 3 → BooleanLaw V)
    (hμ : ∀ i s (hs : s ⊆ e i),
      moment (μ i) s = z ⟨s, mem_completedSupport_of_subset e i s hs⟩)
    (T : Finset V) (a b c : V) (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h0 : f.edge 0 = T ∪ {a,c}) (h1 : f.edge 1 = T ∪ {a,b})
    (h2 : f.edge 2 = T ∪ {b,c}) (hparent : ∀ i, f.edge i ⊆ e i)
    (hcore : (Singleton.coreFamily T a b c (μ 1) (μ 0) (μ 2)).Consistent) :
    Positive.TriangleConditions (Positive.ofCoreFamily
      (Singleton.coreFamily T a b c (μ 1) (μ 0) (μ 2)) hcore) := by
  intro t
  obtain ⟨hm, hma, hmb, hmc, hmab, hmac, hmbc⟩ :=
    core_moments T a b c (μ 1) (μ 0) (μ 2) hcore t
  change Triangle.GT _ _ _ _ _ _ _
  rw [hm, hma, hmb, hmc, hmab, hmac, hmbc]
  by_cases ht : t ⊆ T
  · have he0 : T ∪ {a,c} ⊆ e 0 := h0 ▸ hparent 0
    have he1 : T ∪ {a,b} ⊆ e 1 := h1 ▸ hparent 1
    have he2 : T ∪ {b,c} ⊆ e 2 := h2 ▸ hparent 2
    have hT : T ⊆ e 1 := Finset.subset_union_left.trans he1
    have hea : T ∪ {a} ⊆ e 1 := by
      apply Finset.Subset.trans _ he1
      intro v hv
      simpa only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] using
        (show v ∈ T ∨ v = a ∨ v = b from (Finset.mem_union.mp hv).elim Or.inl
          (fun h => Or.inr (Or.inl (Finset.mem_singleton.mp h))))
    have heb : T ∪ {b} ⊆ e 1 := by
      intro v hv
      apply he1
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      tauto
    have hec : T ∪ {c} ⊆ e 0 := by
      intro v hv
      apply he0
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      tauto
    have h01 : (T ∪ {a,c}) ∩ (T ∪ {a,b}) = T ∪ {a} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    have h12 : (T ∪ {a,b}) ∩ (T ∪ {b,c}) = T ∪ {b} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    have h02 : (T ∪ {a,c}) ∩ (T ∪ {b,c}) = T ∪ {c} := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    have h012 : (T ∪ {a}) ∩ (T ∪ {b,c}) = T := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hs0 := switch_slice e z μ hμ 1 T ∅ t ht (by simp) (by simpa using hT)
    have hsa := switch_slice e z μ hμ 1 T {a} t ht (by simp [ha]) hea
    have hsb := switch_slice e z μ hμ 1 T {b} t ht (by simp [hb]) heb
    have hsc := switch_slice e z μ hμ 0 T {c} t ht (by simp [hc]) hec
    have hsab := switch_slice e z μ hμ 1 T {a,b} t ht (by simp [ha,hb]) he1
    have hsac := switch_slice e z μ hμ 0 T {a,c} t ht (by simp [ha,hc]) he0
    have hsbc := switch_slice e z μ hμ 2 T {b,c} t ht (by simp [hb,hc]) he2
    simp only [Finset.union_empty, Finset.empty_subset, and_true] at hs0
    simp only [Finset.singleton_subset_iff] at hsa hsb hsc
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hsab hsac hsbc
    have hg := hz.2 (T \ t)
    unfold generalizedTriangle at hg
    simp only [h0, h1, h2, h01, h12, h02, h012] at hg
    rw [hs0, hsa, hsb, hsc, hsab, hsac, hsbc] at hg
    exact hg
  · have hzero (ξ : BooleanLaw V) (P : Finset V → Prop) :
        ξ.prob (fun x => x ∩ T = t ∧ P x) = 0 := by
      apply (ξ.prob_eq_zero_iff _).mpr
      intro x hx
      exact (ht (hx.1 ▸ Finset.inter_subset_right)).elim
    have hmasszero : (μ 1).prob (fun x => x ∩ T = t) = 0 := by
      apply ((μ 1).prob_eq_zero_iff _).mpr
      intro x hx
      exact (ht (hx ▸ Finset.inter_subset_right)).elim
    rw [hmasszero, hzero, hzero, hzero, hzero, hzero, hzero]
    norm_num [Triangle.GT]

end AlphaCycle.SliceBridge
