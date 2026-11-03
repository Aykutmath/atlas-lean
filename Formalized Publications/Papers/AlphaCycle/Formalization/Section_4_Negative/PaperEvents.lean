import Section_2_Preliminaries.PaperGeometry
import Section_4_Negative.NegativeSwitched

/-! Literal products and the seven block-factor identities used in the paper.
These identify the product notation with the existing conjunction-event proofs. -/
noncomputable section
namespace AlphaCycle.Triangle
open Classical
variable {V : Type*} [DecidableEq V]

/-- A switched literal, written in the paper's real-valued `X` / `1-X` notation. -/
def literal (x : V → Bool) (U : Finset V) (v : V) : ℝ :=
  if v ∈ U then 1 - (if x v then 1 else 0) else if x v then 1 else 0

def literalProduct (x : V → Bool) (U s : Finset V) : ℝ :=
  ∏ v ∈ s, literal x U v

theorem literal_eq_switched_bit (x : V → Bool) (U : Finset V) (v : V) :
    literal x U v = if switch x U v then 1 else 0 := by
  by_cases hv : v ∈ U <;> cases hx : x v <;> simp [literal, switch, hv, hx]

theorem allTrue_union (x : V → Bool) (s t : Finset V) :
    AllTrue x (s ∪ t) ↔ AllTrue x s ∧ AllTrue x t := by
  simp only [AllTrue, Finset.mem_union]
  aesop

theorem event_union (x : V → Bool) (s t : Finset V) :
    event x (s ∪ t) = event x s * event x t := by
  classical
  simp only [event, allTrue_union]
  by_cases hs : AllTrue x s <;> by_cases ht : AllTrue x t <;> simp [hs, ht]

theorem literalProduct_eq_event (x : V → Bool) (U s : Finset V) :
    literalProduct x U s = event (switch x U) s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [literalProduct, event, AllTrue]
  | @insert v s hv ih =>
      rw [literalProduct, Finset.prod_insert hv]
      change literal x U v * literalProduct x U s = _
      rw [ih, literal_eq_switched_bit]
      simp only [event, AllTrue, Finset.mem_insert, forall_eq_or_imp]
      cases h : switch x U v <;> simp <;> split_ifs with hh
      · exact if_pos hh
      · exact if_neg hh

/-- The positive/negative product in the moment inversion proof is the atom indicator. -/
theorem atom_indicator_product (x : V → Bool) (O Z : Finset V) :
    (∏ v ∈ O, (if x v then (1 : ℝ) else 0)) *
      (∏ v ∈ Z, (1 - (if x v then (1 : ℝ) else 0))) =
      if AllTrue x O ∧ (∀ v ∈ Z, x v = false) then 1 else 0 := by
  classical
  have hp : (∏ v ∈ O, (if x v then (1 : ℝ) else 0)) = event x O := by
    have sw : switch x ∅ = x := by funext v; simp [switch]
    simpa [literalProduct, literal, sw] using literalProduct_eq_event x ∅ O
  have hn : (∏ v ∈ Z, (1 - (if x v then (1 : ℝ) else 0))) =
      if ∀ v ∈ Z, x v = false then (1 : ℝ) else 0 := by
    have hh := literalProduct_eq_event x Z Z
    simp only [literalProduct, literal] at hh
    have he : (∏ v ∈ Z, if v ∈ Z then 1 - (if x v then (1 : ℝ) else 0)
        else if x v then 1 else 0) =
        ∏ v ∈ Z, (1 - (if x v then (1 : ℝ) else 0)) := by
      apply Finset.prod_congr rfl
      intro v hv
      simp [hv]
    rw [he] at hh
    rw [hh]
    have hi : AllTrue (switch x Z) Z ↔ ∀ v ∈ Z, x v = false := by
      apply forall₂_congr
      intro v hv
      simp [switch, hv]
    simp only [event, hi]
  rw [hp, hn]
  unfold event
  by_cases ho : AllTrue x O <;> by_cases hz : ∀ v ∈ Z, x v = false <;> simp [ho, hz]

/-- All seven terms of a no-private triple factor through its four Venn regions.
This works for any assignment, including any switched assignment. -/
theorem seven_event_factors (f : Fin 3 → Finset V)
    (h : NoPrivate (f 0) (f 1) (f 2)) (x : V → Bool) :
    let P := event x (Geometry.blockA f)
    let Q := event x (Geometry.blockB f)
    let R := event x (Geometry.blockC f)
    let S := event x (Geometry.common f)
    event x (f 0) = P * R * S ∧
    event x (f 1) = P * Q * S ∧
    event x (f 2) = Q * R * S ∧
    event x (f 0 ∩ f 1) = P * S ∧
    event x (f 1 ∩ f 2) = Q * S ∧
    event x (f 0 ∩ f 2) = R * S ∧
    event x (f 0 ∩ f 1 ∩ f 2) = S := by
  dsimp only
  obtain ⟨h₀, h₁, h₂⟩ := Geometry.noPrivate_edge_decompositions f h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · rw [h₀, event_union, event_union]
  · rw [h₁, event_union, event_union]
  · rw [h₂, event_union, event_union]
  · rw [Geometry.overlap01, event_union, mul_comm]
  · rw [Geometry.overlap12, event_union, mul_comm]
  · rw [Geometry.overlap02, event_union, mul_comm]

/-- A zero common factor annihilates every term of the four inequalities. -/
theorem common_zero_all_terms (f : Fin 3 → Finset V)
    (h : NoPrivate (f 0) (f 1) (f 2)) (x : V → Bool)
    (hs : event x (Geometry.common f) = 0) :
    event x (f 0) = 0 ∧ event x (f 1) = 0 ∧ event x (f 2) = 0 ∧
    event x (f 0 ∩ f 1) = 0 ∧ event x (f 1 ∩ f 2) = 0 ∧
    event x (f 0 ∩ f 2) = 0 ∧ event x (f 0 ∩ f 1 ∩ f 2) = 0 := by
  simpa only [hs, mul_zero] using seven_event_factors f h x

/-- With common factor one, the seven terms are exactly the three pair
products, three single factors, and one displayed in the paper. -/
theorem common_one_event_factors (f : Fin 3 → Finset V)
    (h : NoPrivate (f 0) (f 1) (f 2)) (x : V → Bool)
    (hs : event x (Geometry.common f) = 1) :
    let P := event x (Geometry.blockA f)
    let Q := event x (Geometry.blockB f)
    let R := event x (Geometry.blockC f)
    event x (f 0) = P * R ∧ event x (f 1) = P * Q ∧ event x (f 2) = Q * R ∧
    event x (f 0 ∩ f 1) = P ∧ event x (f 1 ∩ f 2) = Q ∧
    event x (f 0 ∩ f 2) = R ∧ event x (f 0 ∩ f 1 ∩ f 2) = 1 := by
  simpa only [hs, mul_one] using seven_event_factors f h x

end AlphaCycle.Triangle

namespace AlphaCycle
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact expected-product interpretation of the signed switching formula,
using only a containing local law, without assuming a global law exists. -/
theorem switchVector_local_expected_product (e : Fin 3 → Finset V)
    (U : Finset V) (z : MomentVector (completedSupport e)) (μ : BooleanLaw V)
    (i : Fin 3)
    (hμ : ∀ t (ht : t ⊆ e i),
      moment μ t = z ⟨t, mem_completedSupport_of_subset e i t ht⟩)
    (s : {s // s ∈ completedSupport e}) (hs : s.val ⊆ e i) :
    switchVector e U z s =
      ∑ x, μ.mass x * Triangle.literalProduct (fun v => decide (v ∈ x)) U s.val := by
  classical
  rw [switchVector_local_probability e U z μ i hμ s hs]
  unfold Law.prob
  apply Finset.sum_congr rfl
  intro x _
  have hx : NegativeVertex.ofBits (fun v => decide (v ∈ x)) = x := by
    ext v
    simp [NegativeVertex.mem_ofBits]
  have hl := NegativeVertex.literal_event_iff s.val U (fun v => decide (v ∈ x))
  rw [hx] at hl
  rw [Triangle.literalProduct_eq_event]
  by_cases h : s.val \ U ⊆ x ∧ Disjoint (s.val ∩ U) x
  · simp only [if_pos h, Triangle.event, if_pos (hl.mp h), mul_one]
  · simp only [if_neg h, Triangle.event, if_neg (mt hl.mpr h), mul_zero]

/-- The precise local-law factorization `φ(z_(P∪R∪S))=E[XR]` when the
common literal product is one almost surely. Taking an empty factor covers
the single-factor intersection identities as well. -/
theorem switchVector_local_two_factors (e : Fin 3 → Finset V)
    (U : Finset V) (z : MomentVector (completedSupport e)) (μ : BooleanLaw V)
    (i : Fin 3)
    (hμ : ∀ t (ht : t ⊆ e i),
      moment μ t = z ⟨t, mem_completedSupport_of_subset e i t ht⟩)
    (P R S : Finset V) (hs : P ∪ R ∪ S ⊆ e i)
    (hS : ∀ x, μ.mass x ≠ 0 →
      Triangle.literalProduct (fun v => decide (v ∈ x)) U S = 1) :
    switchVector e U z ⟨P ∪ R ∪ S, mem_completedSupport_of_subset e i _ hs⟩ =
      ∑ x, μ.mass x *
        (Triangle.literalProduct (fun v => decide (v ∈ x)) U P *
          Triangle.literalProduct (fun v => decide (v ∈ x)) U R) := by
  rw [switchVector_local_expected_product e U z μ i hμ _ hs]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.mass x = 0
  · simp only [hx, zero_mul]
  · have hcommon := hS x hx
    simp only [Triangle.literalProduct_eq_event] at hcommon ⊢
    rw [Triangle.event_union, Triangle.event_union, hcommon, mul_one]

/-- The expected positive/negative product equals the probability of its Boolean cell. -/
theorem atom_probability_eq_expected_product (μ : BooleanLaw V) (O Z : Finset V) :
    μ.prob (fun x => O ⊆ x ∧ Disjoint Z x) =
      ∑ x, μ.mass x *
        ((∏ v ∈ O, if v ∈ x then (1 : ℝ) else 0) *
          ∏ v ∈ Z, (1 - (if v ∈ x then (1 : ℝ) else 0))) := by
  classical
  unfold Law.prob
  apply Finset.sum_congr rfl
  intro x _
  have hh := Triangle.atom_indicator_product (fun v => decide (v ∈ x)) O Z
  simp only [decide_eq_true_eq, Triangle.AllTrue, decide_eq_false_iff_not] at hh
  have hp : (∀ v ∈ O, v ∈ x) ↔ O ⊆ x := Iff.rfl
  have hn : (∀ v ∈ Z, v ∉ x) ↔ Disjoint Z x := Finset.disjoint_left.symm
  simp only [hp, hn] at hh
  rw [hh]
  split_ifs <;> simp

end AlphaCycle
