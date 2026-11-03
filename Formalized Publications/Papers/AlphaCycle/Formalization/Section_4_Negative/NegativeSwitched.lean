import Section_4_Negative.NegativeVertex
import Section_2_Preliminaries.LocalVector
import Section_2_Preliminaries.Relaxation
import Section_2_Preliminaries.AllCycles
import Section_2_Preliminaries.CyclePermutation

/-! Connecting the lifted finite laws to the paper's signed switched coordinates. -/
noncomputable section
namespace AlphaCycle.NegativeVertex
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The signed event associated with a Boolean function is precisely the
all-true event of its switched literals. -/
theorem literal_event_iff (s U : Finset V) (x : V → Bool) :
    (s \ U ⊆ ofBits x ∧ Disjoint (s ∩ U) (ofBits x)) ↔
      Triangle.AllTrue (Triangle.switch x U) s := by
  constructor
  · rintro ⟨hp, hn⟩ v hv
    by_cases hu : v ∈ U
    · have hx : x v ≠ true := by
        intro he
        exact Finset.disjoint_left.mp hn (Finset.mem_inter.mpr ⟨hv,hu⟩) ((mem_ofBits x v).mpr he)
      cases he : x v <;> simp_all [Triangle.switch]
    · have hx := (mem_ofBits x v).mp (hp (Finset.mem_sdiff.mpr ⟨hv,hu⟩))
      simp [Triangle.switch, hu, hx]
  · intro h
    constructor
    · intro v hv
      obtain ⟨hvs,hvu⟩ := Finset.mem_sdiff.mp hv
      have hv' := h v hvs
      simpa [Triangle.switch, hvu] using hv'
    · rw [Finset.disjoint_left]
      intro v hv hvx
      obtain ⟨hvs,hvu⟩ := Finset.mem_inter.mp hv
      have hv' := h v hvs
      have hx := (mem_ofBits x v).mp hvx
      simp [Triangle.switch, hvu, hx] at hv'

/-- Expectations of switched conjunctions under a finitely sampled law. -/
theorem map_ofBits_literal_probability {Ω : Type*} [Fintype Ω]
    (μ : Law Ω) (x : Ω → V → Bool) (s U : Finset V) :
    (μ.map (fun a => ofBits (x a))).prob
      (fun t => s \ U ⊆ t ∧ Disjoint (s ∩ U) t) =
      ∑ a, μ.mass a * Triangle.event (Triangle.switch (x a) U) s := by
  rw [Law.prob_map]
  unfold Law.prob
  apply Finset.sum_congr rfl
  intro a _
  dsimp only
  simp only [literal_event_iff]
  by_cases h : Triangle.AllTrue (Triangle.switch (x a) U) s <;> simp [Triangle.event, h]

/-- The witness vector used in the negative direction. -/
def witness (e : Fin 3 → Finset V) (u v b c : V) : MomentVector (completedSupport e) :=
  localMomentVector e (locals u v b c)

theorem witness_local_moments (e : Fin 3 → Finset V) (u v b c : V)
    (hu : u ∉ e 2) (hv : v ∉ e 2) (hb : b ∉ e 0) (hc : c ∉ e 1)
    (i : Fin 3) (s : Finset V) (hs : s ⊆ e i) :
    moment (locals u v b c i) s = witness e u v b c ⟨s, mem_completedSupport_of_subset e i s hs⟩ :=
  localMomentVector_eq e _ (locals_consistent e u v b c hu hv hb hc) i s hs

theorem witness_in_CER (e : Fin 3 → Finset V) (u v b c : V)
    (hu : u ∉ e 2) (hv : v ∉ e 2) (hb : b ∉ e 0) (hc : c ∉ e 1) :
    witness e u v b c ∈ completeEdgeRelaxation e :=
  localMomentVector_mem_completeEdgeRelaxation e _ (locals_consistent e u v b c hu hv hb hc)

theorem witness_switch_probability (e : Fin 3 → Finset V) (u v b c : V)
    (hu : u ∉ e 2) (hv : v ∉ e 2) (hb : b ∉ e 0) (hc : c ∉ e 1)
    (i : Fin 3) (U : Finset V) (s : {s // s ∈ completedSupport e}) (hs : s.val ⊆ e i) :
    switchVector e U (witness e u v b c) s =
      (locals u v b c i).prob (fun t => s.val \ U ⊆ t ∧ Disjoint (s.val ∩ U) t) :=
  switchVector_local_probability e U _ _ i (witness_local_moments e u v b c hu hv hb hc i) s hs

 theorem oddLaw_probability (s U : Finset V) (u v w : V) :
    (oddLaw u v w).prob (fun t => s \ U ⊆ t ∧ Disjoint (s ∩ U) t) =
      AllCycles.oddMoment s U u v w := by
  unfold oddLaw encodeThree
  rw [map_ofBits_literal_probability]
  have he (a b c : Bool) :
      Triangle.event (Triangle.switch
        (fun k => if k = u then a else if k = v then b else if k = w then c else true) U) s =
      Triangle.event (Triangle.switch (AllCycles.assignThree u v w a b c) U) s := by
    apply AllCycles.switched_event_congr
    intro k _
    by_cases hku : k = u <;> by_cases hkv : k = v <;> by_cases hkw : k = w <;>
      simp [AllCycles.assignThree, hku, hkv, hkw]
  simp only [Negative.parityLaw, AllCycles.oddMoment, Fintype.sum_prod_type,
    Fintype.sum_bool, he]

 theorem fairLaw_probability (s U : Finset V) (u v : V) :
    (fairLaw u v).prob (fun t => s \ U ⊆ t ∧ Disjoint (s ∩ U) t) =
      AllCycles.independentMoment s U u v := by
  unfold fairLaw encodeTwo
  rw [map_ofBits_literal_probability]
  have he (a b : Bool) : Negative.twoBits u v (a,b) = AllCycles.assignTwo u v a b := by
    funext k
    simp [Negative.twoBits, AllCycles.assignTwo]
  simp only [Negative.independentLaw, AllCycles.independentMoment,
    Fintype.sum_prod_type, he]

 theorem oddMoment_drop_third (s U : Finset V) (u v w : V) (hw : w ∉ s) :
    AllCycles.oddMoment s U u v w = AllCycles.independentMoment s U u v := by
  unfold AllCycles.oddMoment AllCycles.independentMoment
  simp_rw [AllCycles.three_to_two s U u v w hw]
  simp only [FourVariable.odd, FourVariable.independent, Fintype.sum_bool]
  norm_num

 theorem oddMoment_drop_first_two (s U : Finset V) (u v w : V)
    (hu : u ∉ s) (hv : v ∉ s) :
    AllCycles.oddMoment s U u v w = AllCycles.singleMoment s U w := by
  unfold AllCycles.oddMoment AllCycles.singleMoment
  simp_rw [AllCycles.three_to_one s U u v w hu hv]
  simp only [FourVariable.odd, Fintype.sum_bool]
  norm_num
  ring

 theorem oddMoment_fixed (s U : Finset V) (u v w : V)
    (hu : u ∉ s) (hv : v ∉ s) (hw : w ∉ s) :
    AllCycles.oddMoment s U u v w =
      Triangle.event (Triangle.switch (fun _ : V => true) U) s := by
  have he (a b c : Bool) :
      Triangle.event (Triangle.switch (AllCycles.assignThree u v w a b c) U) s =
        Triangle.event (Triangle.switch (fun _ : V => true) U) s := by
    apply AllCycles.switched_event_congr
    intro k hk
    have hku : k ≠ u := fun h => hu (h ▸ hk)
    have hkv : k ≠ v := fun h => hv (h ▸ hk)
    have hkw : k ≠ w := fun h => hw (h ▸ hk)
    simp [AllCycles.assignThree, hku, hkv, hkw]
  simp only [AllCycles.oddMoment, he, FourVariable.odd, Fintype.sum_bool]
  norm_num
  ring

/-- The lifted parity point satisfies every switching of every relevant
no-private alpha-subcycle in the completed support. -/
 theorem witness_in_allCycleRelaxation (e : Fin 3 → Finset V) (u v b c : V)
    (huv : u ≠ v) (hu : u ∉ e 2) (hv : v ∉ e 2) (hb : b ∉ e 0) (hc : c ∉ e 1) :
    witness e u v b c ∈ allCycleRelaxation e := by
  apply allCycleRelaxation_of_aligned e _ (witness_in_CER e u v b c hu hv hb hc)
  intro f hf hnp U
  have huf : u ∉ f 2 := fun h => hu (hf 2 h)
  have hvf : v ∉ f 2 := fun h => hv (hf 2 h)
  have hbf : b ∉ f 0 := fun h => hb (hf 0 h)
  have hcf : c ∉ f 1 := fun h => hc (hf 1 h)
  have hm := witness_switch_probability e u v b c hu hv hb hc 0 U
    ⟨f 0 ∩ f 1 ∩ f 2, completedSupport_downward e
      (mem_completedSupport_of_subset e 0 (f 0) (hf 0))
      (Finset.inter_subset_left.trans Finset.inter_subset_left)⟩
    ((Finset.inter_subset_left.trans Finset.inter_subset_left).trans (hf 0))
  have hp := witness_switch_probability e u v b c hu hv hb hc 0 U
    ⟨f 0 ∩ f 1, completedSupport_downward e
      (mem_completedSupport_of_subset e 0 (f 0) (hf 0)) Finset.inter_subset_left⟩
    (Finset.inter_subset_left.trans (hf 0))
  have hq := witness_switch_probability e u v b c hu hv hb hc 1 U
    ⟨f 1 ∩ f 2, completedSupport_downward e
      (mem_completedSupport_of_subset e 1 (f 1) (hf 1)) Finset.inter_subset_left⟩
    (Finset.inter_subset_left.trans (hf 1))
  have hr := witness_switch_probability e u v b c hu hv hb hc 0 U
    ⟨f 0 ∩ f 2, completedSupport_downward e
      (mem_completedSupport_of_subset e 0 (f 0) (hf 0)) Finset.inter_subset_left⟩
    (Finset.inter_subset_left.trans (hf 0))
  have hab := witness_switch_probability e u v b c hu hv hb hc 1 U
    ⟨f 1, mem_completedSupport_of_subset e 1 (f 1) (hf 1)⟩ (hf 1)
  have hac := witness_switch_probability e u v b c hu hv hb hc 0 U
    ⟨f 0, mem_completedSupport_of_subset e 0 (f 0) (hf 0)⟩ (hf 0)
  have hbc := witness_switch_probability e u v b c hu hv hb hc 2 U
    ⟨f 2, mem_completedSupport_of_subset e 2 (f 2) (hf 2)⟩ (hf 2)
  change switchVector e U (witness e u v b c)
      ⟨f 2, mem_completedSupport_of_subset e 2 (f 2) (hf 2)⟩ =
    (fairLaw b c).prob (fun t => f 2 \ U ⊆ t ∧ Disjoint (f 2 ∩ U) t) at hbc
  rw [fairLaw_probability] at hbc
  simp only [locals, Matrix.cons_val_zero, Matrix.cons_val_one,
    oddLaw_probability] at hm hp hq hr hab hac
  rw [oddMoment_fixed _ _ _ _ _ (by simp [huf]) (by simp [hvf]) (by simp [hcf])] at hm
  rw [oddMoment_drop_third _ _ _ _ _ (by simp [hcf])] at hp
  rw [oddMoment_drop_first_two _ _ _ _ _ (by simp [huf]) (by simp [hvf])] at hq hr
  unfold generalizedTriangle
  rw [hm, hp, hq, hr, hab, hac, hbc]
  exact AllCycles.aligned U u v b c huv hnp huf hvf hbf hcf

end AlphaCycle.NegativeVertex
