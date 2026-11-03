import Section_3_Obstruction.FourVariable

/-! Generalized triangle inequalities, and the finite certificate used by the
four-variable obstruction. -/
namespace AlphaCycle.Triangle
noncomputable section

/-- The four generalized triangle inequalities in common/pair-only coordinates.
Here `m` is the common-block mass; `p`, `q`, `r` are the three intersection
moments; and `pq`, `pr`, `qr` are the three edge moments. -/
def GT (m p q r pq pr qr : ℝ) : Prop :=
  pq + pr ≤ p + qr ∧ pq + qr ≤ q + pr ∧ pr + qr ≤ r + pq ∧
    p + q + r ≤ m + pq + pr + qr

variable {V : Type*} [DecidableEq V]

/-- The conjunction event associated with a set of vertices. -/
def AllTrue (x : V → Bool) (s : Finset V) : Prop := ∀ v ∈ s, x v = true

/-- Indicator of the conjunction event. -/
noncomputable def event (x : V → Bool) (s : Finset V) : ℝ :=
by
  classical
  exact if AllTrue x s then 1 else 0

/-- A triple has no vertex occurring in just one of its edges. -/
def NoPrivate (f₁ f₂ f₃ : Finset V) : Prop :=
  f₁ ⊆ f₂ ∪ f₃ ∧ f₂ ⊆ f₁ ∪ f₃ ∧ f₃ ⊆ f₁ ∪ f₂

lemma allTrue_mono (x : V → Bool) {s t : Finset V} (h : s ⊆ t) :
    AllTrue x t → AllTrue x s := by
  intro ht v hv
  exact ht v (h hv)

lemma allTrue_from_intersections (x : V → Bool) {a b c : Finset V}
    (h : a ⊆ b ∪ c) :
    AllTrue x a ↔ AllTrue x (a ∩ b) ∧ AllTrue x (a ∩ c) := by
  constructor
  · intro ha
    exact ⟨allTrue_mono x Finset.inter_subset_left ha,
      allTrue_mono x Finset.inter_subset_left ha⟩
  · rintro ⟨hab, hac⟩ v hv
    rcases Finset.mem_union.mp (h hv) with hb | hc
    · exact hab v (Finset.mem_inter.mpr ⟨hv, hb⟩)
    · exact hac v (Finset.mem_inter.mpr ⟨hv, hc⟩)

/-- Every deterministic Boolean vector satisfies the no-private inequalities. -/
theorem deterministic (x : V → Bool) {f₁ f₂ f₃ : Finset V}
    (h : NoPrivate f₁ f₂ f₃) :
    GT (event x (f₁ ∩ f₂ ∩ f₃))
      (event x (f₁ ∩ f₂)) (event x (f₂ ∩ f₃)) (event x (f₁ ∩ f₃))
      (event x f₂) (event x f₁) (event x f₃) := by
  classical
  have h₁ := allTrue_from_intersections x h.1
  have h₂ := allTrue_from_intersections x h.2.1
  have h₃ := allTrue_from_intersections x h.2.2
  rw [Finset.inter_comm f₂ f₁] at h₂
  rw [Finset.inter_comm f₃ f₁, Finset.inter_comm f₃ f₂] at h₃
  have hab : AllTrue x (f₁ ∩ f₂) → AllTrue x (f₁ ∩ f₂ ∩ f₃) :=
    allTrue_mono x Finset.inter_subset_left
  have hbc : AllTrue x (f₂ ∩ f₃) → AllTrue x (f₁ ∩ f₂ ∩ f₃) := by
    apply allTrue_mono x
    intro v hv
    simp only [Finset.mem_inter] at hv ⊢
    exact ⟨hv.1.2, hv.2⟩
  have hac : AllTrue x (f₁ ∩ f₃) → AllTrue x (f₁ ∩ f₂ ∩ f₃) := by
    apply allTrue_mono x
    intro v hv
    simp only [Finset.mem_inter] at hv ⊢
    exact ⟨hv.1.1, hv.2⟩
  by_cases hp : AllTrue x (f₁ ∩ f₂) <;>
    by_cases hq : AllTrue x (f₂ ∩ f₃) <;>
    by_cases hr : AllTrue x (f₁ ∩ f₃) <;>
    by_cases hs : AllTrue x (f₁ ∩ f₂ ∩ f₃) <;>
    simp_all [GT, event]

/-- If two members of a no-private triple lie in one edge, so does the third.
This handles the subcycles whose chosen parent edges are not all distinct. -/
theorem third_subset_of_two {f₁ f₂ f₃ e : Finset V}
    (h : NoPrivate f₁ f₂ f₃) (h₁ : f₁ ⊆ e) (h₂ : f₂ ⊆ e) : f₃ ⊆ e := by
  intro v hv
  rcases Finset.mem_union.mp (h.2.2 hv) with h₁v | h₂v
  · exact h₁ h₁v
  · exact h₂ h₂v

/-- The global alpha-cycle condition excludes two edges in one parent edge. -/
theorem distinct_parents {f₁ f₂ f₃ e : Finset V}
    (hα : ¬ ((f₁ ∩ f₂) ∪ (f₂ ∩ f₃) ∪ (f₁ ∩ f₃) ⊆ e))
    (h₁ : f₁ ⊆ e) (h₂ : f₂ ⊆ e) : False := by
  apply hα
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact h₁ (Finset.mem_inter.mp h).1
    · exact h₂ (Finset.mem_inter.mp h).1
  · exact h₁ (Finset.mem_inter.mp h).1

/-- Switching simply replaces the Boolean assignment by its literal assignment. -/
def switch (x : V → Bool) (u : Finset V) : V → Bool :=
  fun v => if v ∈ u then !(x v) else x v

/-- Validity includes every switching, with no restriction on the switching set. -/
theorem switched_deterministic (x : V → Bool) (u : Finset V)
    {f₁ f₂ f₃ : Finset V} (h : NoPrivate f₁ f₂ f₃) :
    GT (event (switch x u) (f₁ ∩ f₂ ∩ f₃))
      (event (switch x u) (f₁ ∩ f₂))
      (event (switch x u) (f₂ ∩ f₃))
      (event (switch x u) (f₁ ∩ f₃))
      (event (switch x u) f₂) (event (switch x u) f₁)
      (event (switch x u) f₃) :=
  deterministic (switch x u) h

/-- Multiplication by a nonnegative common-block mass preserves validity. -/
theorem scale {m p q r pq pr qr : ℝ} (h : GT m p q r pq pr qr)
    (w : ℝ) (hw : 0 ≤ w) :
    GT (w * m) (w * p) (w * q) (w * r) (w * pq) (w * pr) (w * qr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mul_add] using mul_le_mul_of_nonneg_left h.1 hw
  · simpa [mul_add] using mul_le_mul_of_nonneg_left h.2.1 hw
  · simpa [mul_add] using mul_le_mul_of_nonneg_left h.2.2.1 hw
  · simpa [mul_add] using mul_le_mul_of_nonneg_left h.2.2.2 hw

/-- Nonnegative weighted sums preserve the four inequalities. -/
theorem weighted_sum {I : Type*} [Fintype I]
    (w m p q r pq pr qr : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h : ∀ i, GT (m i) (p i) (q i) (r i) (pq i) (pr i) (qr i)) :
    GT (∑ i, w i * m i) (∑ i, w i * p i) (∑ i, w i * q i)
      (∑ i, w i * r i) (∑ i, w i * pq i) (∑ i, w i * pr i)
      (∑ i, w i * qr i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [mul_add, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (h i).1 (hw i))
  · simpa [mul_add, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (h i).2.1 (hw i))
  · simpa [mul_add, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (h i).2.2.1 (hw i))
  · simpa [mul_add, Finset.sum_add_distrib] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_left (h i).2.2.2 (hw i))

/-- The four possible literal events after ignoring deterministic coordinates. -/
inductive Literal where
  | zero | one | pos | neg
  deriving DecidableEq

def Literal.eval : Literal → Bool → ℝ
  | .zero, _ => 0
  | .one, _ => 1
  | .pos, b => if b then 1 else 0
  | .neg, b => if b then 0 else 1

/-- The `(u,v)` conjunction indicator. -/
def activeX (u v : Literal) (a b : Bool) : ℝ := u.eval a * v.eval b

/-- Marginal expectation of a literal of a fair bit. -/
def fairMoment (b : Literal) : ℝ := (b.eval false + b.eval true) / 2

/-- Expectation of two literal indicators on independent fair bits. -/
def fairPair (u v : Literal) : ℝ :=
  (activeX u v false false + activeX u v false true +
    activeX u v true false + activeX u v true true) / 4

/-- The mixed moment between the `(u,v)` conjunction and the parity bit. -/
def parityMoment (u v w : Literal) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    FourVariable.odd a b c * activeX u v a b * w.eval c

theorem fairPair_eq_sum (u v : Literal) :
    fairPair u v = ∑ a : Bool, ∑ b : Bool,
      FourVariable.independent a b * u.eval a * v.eval b := by
  simp [fairPair, activeX, FourVariable.independent, Fintype.sum_bool]
  ring

theorem fairMoment_eq_sum (u : Literal) :
    fairMoment u = ∑ a : Bool, (1 / 2 : ℝ) * u.eval a := by
  simp [fairMoment, Fintype.sum_bool]
  ring

set_option maxHeartbeats 4000000 in
/-- Complete finite certificate for every switched literal choice in the
four-variable obstruction. Zero/one literals also cover fixed-coordinate gates
and omitted active vertices. Every case is checked using kernel arithmetic. -/
theorem active_certificate (u v b c : Literal) :
    GT 1 (fairPair u v) (fairMoment b) (fairMoment c)
      (parityMoment u v b) (parityMoment u v c) (fairPair b c) := by
  cases u <;> cases v <;> cases b <;> cases c <;>
    norm_num [GT, fairPair, fairMoment, activeX, parityMoment,
      Literal.eval, FourVariable.odd, Fintype.sum_bool]

end
end AlphaCycle.Triangle
