import Section_4_Negative.Negative
import Section_2_Preliminaries.Polytope
import Section_2_Preliminaries.SetGluing
import Section_1_Introduction.Geometry

/-! The parity obstruction as actual Boolean laws on arbitrary vertex sets. -/
noncomputable section
namespace AlphaCycle.NegativeVertex
open Classical Negative
variable {V : Type*} [Fintype V] [DecidableEq V]

def ofBits (x : V → Bool) : Finset V := Finset.univ.filter (fun v => x v = true)

@[simp] theorem mem_ofBits (x : V → Bool) (v : V) : v ∈ ofBits x ↔ x v = true := by
  simp [ofBits]

def encodeOne (u : V) (a : Bool) : Finset V := ofBits (oneBit u a)
def encodeTwo (u v : V) (x : Bool × Bool) : Finset V := ofBits (twoBits u v x)
def encodeThree (u v w : V) (x : (Bool × Bool) × Bool) : Finset V :=
  ofBits (fun k => if k = u then x.1.1 else if k = v then x.1.2 else if k = w then x.2 else true)

def decodeTwo (u v : V) (x : Finset V) : Bool × Bool := (decide (u ∈ x), decide (v ∈ x))
def decodeThree (u v w : V) (x : Finset V) : (Bool × Bool) × Bool :=
  (decodeTwo u v x, decide (w ∈ x))

theorem decodeThree_encode (u v w : V) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.LeftInverse (decodeThree u v w) (encodeThree u v w) := by
  intro x
  simp [decodeThree, decodeTwo, encodeThree, huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw]

theorem decodeTwo_encode (u v : V) (huv : u ≠ v) :
    Function.LeftInverse (decodeTwo u v) (encodeTwo u v) := by
  intro x
  simp [decodeTwo, encodeTwo, twoBits, Ne.symm huv]

theorem decodeThree_restrict (u v w : V) (s x : Finset V)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    decodeThree u v w (x ∩ s) = decodeThree u v w x := by
  simp [decodeThree, decodeTwo, hu, hv, hw]

theorem decodeTwo_restrict (u v : V) (s x : Finset V)
    (hu : u ∈ s) (hv : v ∈ s) : decodeTwo u v (x ∩ s) = decodeTwo u v x := by
  simp [decodeTwo, hu, hv]

theorem encodeThree_restrict_two (u v w : V) (s : Finset V) (hw : w ∉ s)
    (x : (Bool × Bool) × Bool) :
    encodeThree u v w x ∩ s = encodeTwo u v x.1 ∩ s := by
  ext k
  by_cases hks : k ∈ s
  · have hkw : k ≠ w := fun he => hw (he ▸ hks)
    simp [encodeThree, encodeTwo, twoBits, hks, hkw]
  · simp [hks]

theorem encodeThree_restrict_one (u v w : V) (s : Finset V) (hu : u ∉ s) (hv : v ∉ s)
    (x : (Bool × Bool) × Bool) :
    encodeThree u v w x ∩ s = encodeOne w x.2 ∩ s := by
  ext k
  by_cases hks : k ∈ s
  · have hku : k ≠ u := fun he => hu (he ▸ hks)
    have hkv : k ≠ v := fun he => hv (he ▸ hks)
    simp [encodeThree, encodeOne, oneBit, hks, hku, hkv]
  · simp [hks]

theorem encodeTwo_restrict_left (u v : V) (s : Finset V) (hv : v ∉ s) (x : Bool × Bool) :
    encodeTwo u v x ∩ s = encodeOne u x.1 ∩ s := by
  ext k
  by_cases hks : k ∈ s
  · have hkv : k ≠ v := fun he => hv (he ▸ hks)
    simp [encodeTwo, encodeOne, twoBits, oneBit, hks, hkv]
  · simp [hks]

theorem encodeTwo_restrict_right (u v : V) (s : Finset V) (hu : u ∉ s) (x : Bool × Bool) :
    encodeTwo u v x ∩ s = encodeOne v x.2 ∩ s := by
  ext k
  by_cases hks : k ∈ s
  · have hku : k ≠ u := fun he => hu (he ▸ hks)
    simp [encodeTwo, encodeOne, twoBits, oneBit, hks, hku]
  · simp [hks]

/-- The local parity law, with all vertices outside its three active coordinates fixed to one. -/
def oddLaw (u v w : V) : BooleanLaw V := parityLaw.map (encodeThree u v w)
def fairLaw (u v : V) : BooleanLaw V := independentLaw.map (encodeTwo u v)

def locals (u v b c : V) : Fin 3 → BooleanLaw V := ![oddLaw u v c, oddLaw u v b, fairLaw b c]

theorem local_overlap01 (u v b c : V) (s : Finset V) (hb : b ∉ s) (hc : c ∉ s) :
    restrictLaw (oddLaw u v c) s = restrictLaw (oddLaw u v b) s := by
  simp only [restrictLaw, oddLaw, Law.map_map, Function.comp_def,
    encodeThree_restrict_two u v c s hc, encodeThree_restrict_two u v b s hb]

theorem local_overlap02 (u v b c : V) (s : Finset V)
    (hu : u ∉ s) (hv : v ∉ s) (hb : b ∉ s) :
    restrictLaw (oddLaw u v c) s = restrictLaw (fairLaw b c) s := by
  have he := congrArg (Law.map (fun x => encodeOne c x ∩ s)) parityFamily_consistent.2.2
  simpa only [parityFamily, restrictLaw, oddLaw, fairLaw, Law.map_map, Function.comp_def,
    encodeThree_restrict_one u v c s hu hv, encodeTwo_restrict_right b c s hb] using he

theorem local_overlap12 (u v b c : V) (s : Finset V)
    (hu : u ∉ s) (hv : v ∉ s) (hc : c ∉ s) :
    restrictLaw (oddLaw u v b) s = restrictLaw (fairLaw b c) s := by
  have he := congrArg (Law.map (fun x => encodeOne b x ∩ s)) parityFamily_consistent.2.1
  simpa only [parityFamily, restrictLaw, oddLaw, fairLaw, Law.map_map, Function.comp_def,
    encodeThree_restrict_one u v b s hu hv, encodeTwo_restrict_left b c s hc] using he

/-- The three exact edge laws agree on every pairwise overlap. -/
theorem locals_consistent (e : Fin 3 → Finset V) (u v b c : V)
    (hu : u ∉ e 2) (hv : v ∉ e 2) (hb : b ∉ e 0) (hc : c ∉ e 1) :
    ∀ i j, restrictLaw (locals u v b c i) (e i ∩ e j) =
      restrictLaw (locals u v b c j) (e i ∩ e j) := by
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact local_overlap01 u v b c _ (by simp [hb]) (by simp [hc])
  · exact local_overlap02 u v b c _ (by simp [hu]) (by simp [hv]) (by simp [hb])
  · exact (local_overlap01 u v b c _ (by simp [hb]) (by simp [hc])).symm
  · rfl
  · exact local_overlap12 u v b c _ (by simp [hu]) (by simp [hv]) (by simp [hc])
  · exact (local_overlap02 u v b c _ (by simp [hu]) (by simp [hv]) (by simp [hb])).symm
  · exact (local_overlap12 u v b c _ (by simp [hu]) (by simp [hv]) (by simp [hc])).symm
  · rfl

/-- A nonnegative global law would decode to the impossible four-bit joint law. -/
theorem locals_not_realizable (e : Fin 3 → Finset V) (u v b c : V)
    (huv : u ≠ v) (hub : u ≠ b) (huc : u ≠ c) (hvb : v ≠ b) (hvc : v ≠ c) (hbc : b ≠ c)
    (hu0 : u ∈ e 0) (hv0 : v ∈ e 0) (hc0 : c ∈ e 0)
    (hu1 : u ∈ e 1) (hv1 : v ∈ e 1) (hb1 : b ∈ e 1)
    (hb2 : b ∈ e 2) (hc2 : c ∈ e 2) :
    ¬ ∃ μ : BooleanLaw V, ∀ i, restrictLaw μ (e i) = restrictLaw (locals u v b c i) (e i) := by
  rintro ⟨μ, hμ⟩
  have h0 := congrArg (Law.map (decodeThree u v c)) (hμ 0)
  have h1 := congrArg (Law.map (decodeThree u v b)) (hμ 1)
  have h2 := congrArg (Law.map (decodeTwo b c)) (hμ 2)
  change (restrictLaw μ (e 0)).map (decodeThree u v c) =
    (restrictLaw (oddLaw u v c) (e 0)).map (decodeThree u v c) at h0
  change (restrictLaw μ (e 1)).map (decodeThree u v b) =
    (restrictLaw (oddLaw u v b) (e 1)).map (decodeThree u v b) at h1
  change (restrictLaw μ (e 2)).map (decodeTwo b c) =
    (restrictLaw (fairLaw b c) (e 2)).map (decodeTwo b c) at h2
  have huc' := decodeThree_encode u v c huv huc hvc
  have hub' := decodeThree_encode u v b huv hub hvb
  have hbc' := decodeTwo_encode b c hbc
  simp only [Function.LeftInverse] at huc' hub' hbc'
  simp only [restrictLaw, locals, Matrix.cons_val_zero, oddLaw, Law.map_map,
    Function.comp_def, decodeThree_restrict u v c _ _ hu0 hv0 hc0, huc'] at h0
  simp only [restrictLaw, locals, Matrix.cons_val_one, oddLaw, Law.map_map,
    Function.comp_def, decodeThree_restrict u v b _ _ hu1 hv1 hb1, hub'] at h1
  simp only [restrictLaw, locals, Matrix.cons_val_two, fairLaw, Law.map_map,
    Function.comp_def, decodeTwo_restrict b c _ _ hb2 hc2, hbc'] at h2
  change μ.map (decodeThree u v c) = parityLaw.map id at h0
  change μ.map (decodeThree u v b) = parityLaw.map id at h1
  change μ.map (decodeTwo b c) = independentLaw.map id at h2
  rw [Law.map_id] at h0 h1 h2
  apply parityFamily_not_realizable
  refine ⟨μ.map (fun x => (decodeTwo u v x, decide (b ∈ x), decide (c ∈ x))), ?_, ?_, ?_⟩
  · change (μ.map _).map _ = parityLaw
    rw [Law.map_map]
    exact h1
  · change (μ.map _).map _ = parityLaw
    rw [Law.map_map]
    exact h0
  · change (μ.map _).map _ = independentLaw
    rw [Law.map_map]
    exact h2

end AlphaCycle.NegativeVertex
