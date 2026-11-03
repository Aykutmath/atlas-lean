import Section_2_Preliminaries.Triangle

/-! Reduction of switched conjunction events under the lifted parity construction. -/
noncomputable section
namespace AlphaCycle.AllCycles
open Triangle
variable {V : Type*} [DecidableEq V]

/-- Two active bits and otherwise deterministic ones. -/
def assignTwo (u v : V) (a b : Bool) : V → Bool :=
  fun w => if w = u then a else if w = v then b else true

/-- One active bit and otherwise deterministic ones. -/
def assignOne (u : V) (a : Bool) : V → Bool :=
  fun w => if w = u then a else true

def FixedGate (s U : Finset V) (u v : V) : Prop :=
  ∀ w ∈ s, w ≠ u → w ≠ v → w ∉ U

def gate (s U : Finset V) (u v : V) : ℝ := by
  classical
  exact if FixedGate s U u v then 1 else 0

/-- Select the positive or negative literal when the vertex is present. -/
def selectLiteral (s U : Finset V) (u : V) : Literal :=
  if u ∈ s then if u ∈ U then .neg else .pos else .one

lemma selectLiteral_eval (s U : Finset V) (u : V) (a : Bool) :
    (selectLiteral s U u).eval a =
      if (u ∈ s → (if u ∈ U then !a else a) = true) then 1 else 0 := by
  classical
  by_cases hs : u ∈ s <;> by_cases hU : u ∈ U <;> cases a <;>
    simp [selectLiteral, Literal.eval, hs, hU]

lemma two_allTrue_iff (s U : Finset V) (u v : V) (huv : u ≠ v) (a b : Bool) :
    AllTrue (switch (assignTwo u v a b) U) s ↔
      FixedGate s U u v ∧
      (u ∈ s → (if u ∈ U then !a else a) = true) ∧
      (v ∈ s → (if v ∈ U then !b else b) = true) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro w hw hwu hwv hwU
      have hh := h w hw
      simp [switch, assignTwo, hwu, hwv, hwU] at hh
    · intro hu
      simpa [switch, assignTwo] using h u hu
    · intro hv
      simpa [switch, assignTwo, Ne.symm huv] using h v hv
  · rintro ⟨hg, hu, hv⟩ w hw
    by_cases hwu : w = u
    · subst w
      simpa [switch, assignTwo] using hu hw
    by_cases hwv : w = v
    · subst w
      simpa [switch, assignTwo, Ne.symm huv] using hv hw
    · simp [switch, assignTwo, hwu, hwv, hg w hw hwu hwv]

lemma and_indicator (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℝ) else 0) =
      (if p then (1 : ℝ) else 0) * (if q then (1 : ℝ) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma two_event_factor (s U : Finset V) (u v : V) (huv : u ≠ v) (a b : Bool) :
    event (switch (assignTwo u v a b) U) s =
      gate s U u v *
        (selectLiteral s U u).eval a * (selectLiteral s U v).eval b := by
  classical
  rw [selectLiteral_eval, selectLiteral_eval]
  unfold event gate
  rw [two_allTrue_iff s U u v huv a b]
  cases a <;> cases b <;> split_ifs <;> norm_num at * <;> tauto

/-- A conjunction of arbitrarily many fixed and two active literals always has
one of the forms exhaustively covered by the finite certificate. -/
theorem two_event_literal (s U : Finset V) (u v : V) (huv : u ≠ v) :
    ∃ l₁ l₂ : Literal, ∀ a b : Bool,
      event (switch (assignTwo u v a b) U) s = activeX l₁ l₂ a b := by
  classical
  by_cases hg : FixedGate s U u v
  · refine ⟨selectLiteral s U u, selectLiteral s U v, ?_⟩
    intro a b
    simp [two_event_factor s U u v huv, gate, hg, activeX]
  · refine ⟨.zero, .one, ?_⟩
    intro a b
    simp [two_event_factor s U u v huv, gate, hg, activeX, Literal.eval]

lemma one_allTrue_iff (s U : Finset V) (u : V) (a : Bool) :
    AllTrue (switch (assignOne u a) U) s ↔
      (∀ w ∈ s, w ≠ u → w ∉ U) ∧
      (u ∈ s → (if u ∈ U then !a else a) = true) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro w hw hwu hwU
      have hh := h w hw
      simp [switch, assignOne, hwu, hwU] at hh
    · intro hu
      simpa [switch, assignOne] using h u hu
  · rintro ⟨hg, hu⟩ w hw
    by_cases hwu : w = u
    · subst w
      simpa [switch, assignOne] using hu hw
    · simp [switch, assignOne, hwu, hg w hw hwu]

theorem one_event_literal (s U : Finset V) (u : V) :
    ∃ l : Literal, ∀ a : Bool,
      event (switch (assignOne u a) U) s = l.eval a := by
  classical
  by_cases hg : ∀ w ∈ s, w ≠ u → w ∉ U
  · refine ⟨selectLiteral s U u, ?_⟩
    intro a
    rw [selectLiteral_eval]
    rw [event, one_allTrue_iff]
    congr 1
    exact propext ⟨And.right, fun h => ⟨hg, h⟩⟩
  · refine ⟨.zero, ?_⟩
    intro a
    simp only [event, one_allTrue_iff, hg, false_and, ite_false, Literal.eval]

/-- The full event-factor statement underlying every aligned no-private
subcycle: arbitrary switched conjunctions in its three pair-only blocks satisfy
the four inequalities under the parity and independent local laws. -/
theorem block_certificate (P Q R U : Finset V) (u v b c : V) (huv : u ≠ v) :
    let X := fun a d => event (switch (assignTwo u v a d) U) P
    let Y := fun a => event (switch (assignOne b a) U) Q
    let Z := fun a => event (switch (assignOne c a) U) R
    GT 1
      ((∑ a : Bool, ∑ d : Bool, X a d) / 4)
      ((∑ a : Bool, Y a) / 2) ((∑ a : Bool, Z a) / 2)
      (∑ a : Bool, ∑ d : Bool, ∑ y : Bool, FourVariable.odd a d y * X a d * Y y)
      (∑ a : Bool, ∑ d : Bool, ∑ z : Bool, FourVariable.odd a d z * X a d * Z z)
      (∑ y : Bool, ∑ z : Bool, FourVariable.independent y z * Y y * Z z) := by
  obtain ⟨lu, lv, hX⟩ := two_event_literal P U u v huv
  obtain ⟨lb, hY⟩ := one_event_literal Q U b
  obtain ⟨lc, hZ⟩ := one_event_literal R U c
  simp only [hX, hY, hZ]
  convert active_certificate lu lv lb lc using 1
  · simp [fairPair, Fintype.sum_bool, add_comm, add_left_comm, add_assoc]
  · simp [fairMoment, Fintype.sum_bool, add_comm]
  · simp [fairMoment, Fintype.sum_bool, add_comm]
  · rfl
  · rfl
  · exact (fairPair_eq_sum lb lc).symm

/-- Three active bits and otherwise deterministic ones. -/
def assignThree (u v w : V) (a b c : Bool) : V → Bool :=
  fun x => if x = u then a else if x = v then b else if x = w then c else true

lemma switched_event_congr (s U : Finset V) (x y : V → Bool)
    (h : ∀ v ∈ s, x v = y v) :
    event (switch x U) s = event (switch y U) s := by
  classical
  have he : AllTrue (switch x U) s ↔ AllTrue (switch y U) s := by
    simp only [AllTrue, switch]
    constructor <;> intro ha v hv <;> simpa [h v hv] using ha v hv
  simp only [event, he]

lemma event_factor (x : V → Bool) {a b c : Finset V} (h : a ⊆ b ∪ c) :
    event x a = event x (a ∩ b) * event x (a ∩ c) := by
  classical
  simp only [event, allTrue_from_intersections x h]
  by_cases hab : AllTrue x (a ∩ b) <;>
    by_cases hac : AllTrue x (a ∩ c) <;> simp [hab, hac]

lemma three_to_two (s U : Finset V) (u v w : V) (hw : w ∉ s) (a b c : Bool) :
    event (switch (assignThree u v w a b c) U) s =
      event (switch (assignTwo u v a b) U) s := by
  apply switched_event_congr
  intro x hx
  have hxw : x ≠ w := fun h => hw (h ▸ hx)
  simp [assignThree, assignTwo, hxw]

lemma three_to_one (s U : Finset V) (u v w : V) (hu : u ∉ s) (hv : v ∉ s)
    (a b c : Bool) :
    event (switch (assignThree u v w a b c) U) s =
      event (switch (assignOne w c) U) s := by
  apply switched_event_congr
  intro x hx
  have hxu : x ≠ u := fun h => hu (h ▸ hx)
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  simp [assignThree, assignOne, hxu, hxv]

lemma two_to_left (s U : Finset V) (u v : V) (hv : v ∉ s) (a b : Bool) :
    event (switch (assignTwo u v a b) U) s =
      event (switch (assignOne u a) U) s := by
  apply switched_event_congr
  intro x hx
  have hxv : x ≠ v := fun h => hv (h ▸ hx)
  simp [assignTwo, assignOne, hxv]

lemma two_to_right (s U : Finset V) (u v : V) (hu : u ∉ s) (a b : Bool) :
    event (switch (assignTwo u v a b) U) s =
      event (switch (assignOne v b) U) s := by
  apply switched_event_congr
  intro x hx
  have hxu : x ≠ u := fun h => hu (h ▸ hx)
  simp [assignTwo, assignOne, hxu]

/-- The switched moment under a parity local law on three active bits. -/
def oddMoment (s U : Finset V) (u v w : V) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    FourVariable.odd a b c * event (switch (assignThree u v w a b c) U) s

/-- The switched moment under a fair independent local law on two active bits. -/
def independentMoment (s U : Finset V) (u v : V) : ℝ :=
  ∑ a : Bool, ∑ b : Bool,
    FourVariable.independent a b * event (switch (assignTwo u v a b) U) s

def singleMoment (s U : Finset V) (u : V) : ℝ :=
  (∑ a : Bool, event (switch (assignOne u a) U) s) / 2

/-- Aligned no-private triples satisfy the switched inequalities with common
mass one. The following theorem restores the exact common-block mass. -/
theorem aligned_one {f₁ f₂ f₃ : Finset V} (U : Finset V) (u v b c : V)
    (huv : u ≠ v) (hnp : NoPrivate f₁ f₂ f₃)
    (hu : u ∉ f₃) (hv : v ∉ f₃) (hb : b ∉ f₁) (hc : c ∉ f₂) :
    GT 1
      (independentMoment (f₁ ∩ f₂) U u v)
      (singleMoment (f₂ ∩ f₃) U b) (singleMoment (f₁ ∩ f₃) U c)
      (oddMoment f₂ U u v b) (oddMoment f₁ U u v c)
      (independentMoment f₃ U b c) := by
  have h₁ (a d z : Bool) :
      event (switch (assignThree u v c a d z) U) f₁ =
        event (switch (assignTwo u v a d) U) (f₁ ∩ f₂) *
          event (switch (assignOne c z) U) (f₁ ∩ f₃) := by
    rw [event_factor _ hnp.1]
    rw [three_to_two _ _ _ _ _ (by simp [hc]),
      three_to_one _ _ _ _ _ (by simp [hu]) (by simp [hv])]
  have h₂ (a d y : Bool) :
      event (switch (assignThree u v b a d y) U) f₂ =
        event (switch (assignTwo u v a d) U) (f₁ ∩ f₂) *
          event (switch (assignOne b y) U) (f₂ ∩ f₃) := by
    rw [event_factor _ hnp.2.1, Finset.inter_comm f₂ f₁]
    rw [three_to_two _ _ _ _ _ (by simp [hb]),
      three_to_one _ _ _ _ _ (by simp [hu]) (by simp [hv])]
  have h₃ (y z : Bool) :
      event (switch (assignTwo b c y z) U) f₃ =
        event (switch (assignOne b y) U) (f₂ ∩ f₃) *
          event (switch (assignOne c z) U) (f₁ ∩ f₃) := by
    rw [event_factor _ hnp.2.2, Finset.inter_comm f₃ f₁, Finset.inter_comm f₃ f₂]
    rw [two_to_right _ _ _ _ (by simp [hb]), two_to_left _ _ _ _ (by simp [hc])]
    ring
  have hcert := block_certificate (f₁ ∩ f₂) (f₂ ∩ f₃) (f₁ ∩ f₃) U u v b c huv
  dsimp only at hcert
  convert hcert using 1
  · simp only [independentMoment, FourVariable.independent, Fintype.sum_bool]
    ring
  · rfl
  · rfl
  · simp only [oddMoment, h₂, mul_assoc]
  · simp only [oddMoment, h₁, mul_assoc]
  · simp only [independentMoment, h₃, mul_assoc]

lemma event_zero_of_switched_fixed (s U : Finset V) (w : V)
    (hw : w ∈ s) (hU : w ∈ U) (x : V → Bool) (hx : x w = true) :
    event (switch x U) s = 0 := by
  classical
  unfold event
  apply if_neg
  intro ha
  have hh := ha w hw
  simp [switch, hU, hx] at hh

/-- Every switching of every aligned no-private triple is satisfied by the
lifted parity point. The four exclusions are precisely the constraints imposed
by the three parent edges; extra vertices are fixed to one. No bound on the
number of extra, common, or private vertices is imposed. -/
theorem aligned {f₁ f₂ f₃ : Finset V} (U : Finset V) (u v b c : V)
    (huv : u ≠ v) (hnp : NoPrivate f₁ f₂ f₃)
    (hu : u ∉ f₃) (hv : v ∉ f₃) (hb : b ∉ f₁) (hc : c ∉ f₂) :
    GT (event (switch (fun _ : V => true) U) (f₁ ∩ f₂ ∩ f₃))
      (independentMoment (f₁ ∩ f₂) U u v)
      (singleMoment (f₂ ∩ f₃) U b) (singleMoment (f₁ ∩ f₃) U c)
      (oddMoment f₂ U u v b) (oddMoment f₁ U u v c)
      (independentMoment f₃ U b c) := by
  classical
  by_cases hs : AllTrue (switch (fun _ : V => true) U) (f₁ ∩ f₂ ∩ f₃)
  · simpa only [event, if_pos hs] using aligned_one U u v b c huv hnp hu hv hb hc
  · have hex : ∃ w, w ∈ f₁ ∩ f₂ ∩ f₃ ∧ w ∈ U := by
      by_contra hn
      apply hs
      intro w hw
      have hnot : w ∉ U := by
        intro hU
        exact hn ⟨w, hw, hU⟩
      simp [switch, hnot]
    obtain ⟨w, hw, hwU⟩ := hex
    rcases Finset.mem_inter.mp hw with ⟨hw₁₂, hw₃⟩
    rcases Finset.mem_inter.mp hw₁₂ with ⟨hw₁, hw₂⟩
    have hwu : w ≠ u := fun h => hu (h ▸ hw₃)
    have hwv : w ≠ v := fun h => hv (h ▸ hw₃)
    have hwb : w ≠ b := fun h => hb (h ▸ hw₁)
    have hwc : w ≠ c := fun h => hc (h ▸ hw₂)
    have hzeroTwo (s : Finset V) (hws : w ∈ s) (r t : V)
        (hr : w ≠ r) (ht : w ≠ t) (a d : Bool) :
        event (switch (assignTwo r t a d) U) s = 0 :=
      event_zero_of_switched_fixed s U w hws hwU _ (by simp [assignTwo, hr, ht])
    have hzeroOne (s : Finset V) (hws : w ∈ s) (r : V)
        (hr : w ≠ r) (a : Bool) :
        event (switch (assignOne r a) U) s = 0 :=
      event_zero_of_switched_fixed s U w hws hwU _ (by simp [assignOne, hr])
    have hzeroThree (s : Finset V) (hws : w ∈ s) (r t k : V)
        (hr : w ≠ r) (ht : w ≠ t) (hk : w ≠ k) (a d z : Bool) :
        event (switch (assignThree r t k a d z) U) s = 0 :=
      event_zero_of_switched_fixed s U w hws hwU _ (by simp [assignThree, hr, ht, hk])
    have hzP := hzeroTwo (f₁ ∩ f₂) (Finset.mem_inter.mpr ⟨hw₁, hw₂⟩) u v hwu hwv
    have hzQ := hzeroOne (f₂ ∩ f₃) (Finset.mem_inter.mpr ⟨hw₂, hw₃⟩) b hwb
    have hzR := hzeroOne (f₁ ∩ f₃) (Finset.mem_inter.mpr ⟨hw₁, hw₃⟩) c hwc
    have hz₁ := hzeroThree f₁ hw₁ u v c hwu hwv hwc
    have hz₂ := hzeroThree f₂ hw₂ u v b hwu hwv hwb
    have hz₃ := hzeroTwo f₃ hw₃ b c hwb hwc
    simp only [independentMoment, singleMoment, oddMoment, hzP, hzQ, hzR, hz₁, hz₂,
      hz₃, mul_zero, Finset.sum_const_zero, zero_div]
    simp [GT, event]
    split_ifs <;> norm_num

end AlphaCycle.AllCycles
