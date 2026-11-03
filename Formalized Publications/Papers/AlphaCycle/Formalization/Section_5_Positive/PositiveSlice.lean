import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The three-variable slice extension theorem

All masses in this file are unnormalized.  The four triangle inequalities,
together with nonnegativity of the three prescribed two-variable tables,
are precisely sufficient for a joint table on three Boolean variables.
-/

namespace AlphaCycle.Slice

/-- The total mass and six first- and second-order moments of a slice. -/
structure Moments where
  mass : ℝ
  a : ℝ
  b : ℝ
  c : ℝ
  ab : ℝ
  ac : ℝ
  bc : ℝ

/-- The four nonnegativity conditions for a Boolean two-variable table. -/
def PairBounds (m p q pq : ℝ) : Prop :=
  0 ≤ pq ∧ pq ≤ p ∧ pq ≤ q ∧ 0 ≤ m - p - q + pq

/-- Local feasibility and the four (unswitched) triangle inequalities. -/
structure Conditions (s : Moments) : Prop where
  pair_ab : PairBounds s.mass s.a s.b s.ab
  pair_ac : PairBounds s.mass s.a s.c s.ac
  pair_bc : PairBounds s.mass s.b s.c s.bc
  triangle_a : s.ab + s.ac ≤ s.a + s.bc
  triangle_b : s.ab + s.bc ≤ s.b + s.ac
  triangle_c : s.ac + s.bc ≤ s.c + s.ab
  triangle_sum : s.a + s.b + s.c ≤ s.mass + s.ab + s.ac + s.bc

/-- The lower endpoint for the mass of the cell `111`. -/
def lower (s : Moments) : ℝ :=
  max (max 0 (s.ab + s.ac - s.a))
    (max (s.ab + s.bc - s.b) (s.ac + s.bc - s.c))

/-- The upper endpoint for the mass of the cell `111`. -/
def upper (s : Moments) : ℝ :=
  min (min s.ab s.ac)
    (min s.bc (s.mass - s.a - s.b - s.c + s.ab + s.ac + s.bc))

/-- Every lower bound is at most every upper bound.  This includes zero-mass slices. -/
theorem interval_nonempty (s : Moments) (h : Conditions s) : lower s ≤ upper s := by
  rcases h with ⟨⟨hab0, haba, habb, hab00⟩, ⟨hac0, haca, hacc, hac00⟩,
    ⟨hbc0, hbcb, hbcc, hbc00⟩, ha, hb, hc, hsum⟩
  simp only [lower, upper, max_le_iff, le_min_iff]
  repeat' apply And.intro
  all_goals linarith

/-- The unique Boolean pair table with the specified moments. -/
def pairAtom (m p q pq : ℝ) : Bool → Bool → ℝ
  | true, true => pq
  | true, false => p - pq
  | false, true => q - pq
  | false, false => m - p - q + pq

/-- The eight cells of the slice, parameterized by the mass of `111`. -/
def atom (s : Moments) (r : ℝ) : Bool → Bool → Bool → ℝ
  | true, true, true => r
  | true, true, false => s.ab - r
  | true, false, true => s.ac - r
  | false, true, true => s.bc - r
  | true, false, false => s.a - s.ab - s.ac + r
  | false, true, false => s.b - s.ab - s.bc + r
  | false, false, true => s.c - s.ac - s.bc + r
  | false, false, false => s.mass - s.a - s.b - s.c + s.ab + s.ac + s.bc - r

/-- Nonnegativity of all eight cells is exactly the endpoint condition. -/
theorem atom_nonnegative_iff (s : Moments) (r : ℝ) :
    (∀ i j k, 0 ≤ atom s r i j k) ↔ lower s ≤ r ∧ r ≤ upper s := by
  simp only [Bool.forall_bool, atom, lower, upper, max_le_iff, le_min_iff]
  constructor
  · intro h
    rcases h with ⟨⟨⟨h000, h001⟩, ⟨h010, h011⟩⟩, ⟨⟨h100, h101⟩, ⟨h110, h111⟩⟩⟩
    repeat' apply And.intro
    all_goals linarith
  · intro h
    rcases h with ⟨⟨⟨h0, ha⟩, ⟨hb, hc⟩⟩, ⟨⟨hab, hac⟩, ⟨hbc, hm⟩⟩⟩
    repeat' apply And.intro
    all_goals linarith

open scoped BigOperators

/-- The moments of any nonnegative Boolean pair table satisfy Fréchet bounds. -/
theorem pairBounds_of_nonnegative (p : Bool → Bool → ℝ)
    (h : ∀ i j, 0 ≤ p i j) :
    PairBounds (∑ i : Bool, ∑ j : Bool, p i j)
      (∑ j : Bool, p true j) (∑ i : Bool, p i true) (p true true) := by
  have h00 := h false false
  have h01 := h false true
  have h10 := h true false
  have h11 := h true true
  simp only [PairBounds, Fintype.sum_bool]
  repeat' apply And.intro
  all_goals linarith

/-- The `ab` marginal is independent of the selected triple mass. -/
theorem atom_marginal_ab (s : Moments) (r : ℝ) (i j : Bool) :
    (∑ k : Bool, atom s r i j k) = pairAtom s.mass s.a s.b s.ab i j := by
  cases i <;> cases j <;> (simp only [Fintype.sum_bool, atom, pairAtom]; ring)

/-- The `ac` marginal is independent of the selected triple mass. -/
theorem atom_marginal_ac (s : Moments) (r : ℝ) (i k : Bool) :
    (∑ j : Bool, atom s r i j k) = pairAtom s.mass s.a s.c s.ac i k := by
  cases i <;> cases k <;> simp only [Fintype.sum_bool, atom, pairAtom] <;> ring

/-- The `bc` marginal is independent of the selected triple mass. -/
theorem atom_marginal_bc (s : Moments) (r : ℝ) (j k : Bool) :
    (∑ i : Bool, atom s r i j k) = pairAtom s.mass s.b s.c s.bc j k := by
  cases j <;> cases k <;> simp only [Fintype.sum_bool, atom, pairAtom] <;> ring

/-- The eight cells have exactly the prescribed total mass. -/
theorem atom_mass (s : Moments) (r : ℝ) :
    (∑ i : Bool, ∑ j : Bool, ∑ k : Bool, atom s r i j k) = s.mass := by
  simp only [Fintype.sum_bool, atom]
  ring

/-- An explicit choice of triple mass supplies a nonnegative joint slice. -/
theorem extension (s : Moments) (h : Conditions s) :
    ∃ q : Bool → Bool → Bool → ℝ,
      (∀ i j k, 0 ≤ q i j k) ∧
      (∑ i : Bool, ∑ j : Bool, ∑ k : Bool, q i j k) = s.mass ∧
      (∀ i j, (∑ k : Bool, q i j k) = pairAtom s.mass s.a s.b s.ab i j) ∧
      (∀ i k, (∑ j : Bool, q i j k) = pairAtom s.mass s.a s.c s.ac i k) ∧
      (∀ j k, (∑ i : Bool, q i j k) = pairAtom s.mass s.b s.c s.bc j k) := by
  exact ⟨atom s (lower s), (atom_nonnegative_iff s (lower s)).2
    ⟨le_rfl, interval_nonempty s h⟩, atom_mass s (lower s),
    atom_marginal_ab s (lower s), atom_marginal_ac s (lower s),
    atom_marginal_bc s (lower s)⟩

/-- A pair table is determined by its total mass and three moments. -/
theorem pairAtom_reconstruction (p : Bool → Bool → ℝ) (m a b ab : ℝ)
    (hm : (∑ i : Bool, ∑ j : Bool, p i j) = m)
    (ha : (∑ j : Bool, p true j) = a)
    (hb : (∑ i : Bool, p i true) = b)
    (hab : p true true = ab) :
    ∀ i j, p i j = pairAtom m a b ab i j := by
  simp only [Fintype.sum_bool] at hm ha hb
  intro i j
  cases i <;> cases j <;> simp only [pairAtom] <;> linarith

/-- Exact extension data for an unnormalized three-variable slice. -/
def IsExtension (s : Moments) (q : Bool → Bool → Bool → ℝ) : Prop :=
  (∀ i j k, 0 ≤ q i j k) ∧
  (∑ i : Bool, ∑ j : Bool, ∑ k : Bool, q i j k) = s.mass ∧
  (∀ i j, (∑ k : Bool, q i j k) = pairAtom s.mass s.a s.b s.ab i j) ∧
  (∀ i k, (∑ j : Bool, q i j k) = pairAtom s.mass s.a s.c s.ac i k) ∧
  (∀ j k, (∑ i : Bool, q i j k) = pairAtom s.mass s.b s.c s.bc j k)

/-- Every nonnegative joint table necessarily satisfies the slice inequalities. -/
theorem conditions_of_extension (s : Moments) (q : Bool → Bool → Bool → ℝ)
    (h : IsExtension s q) : Conditions s := by
  rcases h with ⟨hnonneg, hm, hab, hac, hbc⟩
  have hab11 := hab true true
  have hab10 := hab true false
  have hab01 := hab false true
  have hac11 := hac true true
  have hac01 := hac false true
  have hbc11 := hbc true true
  have h000 := hnonneg false false false
  have h001 := hnonneg false false true
  have h010 := hnonneg false true false
  have h011 := hnonneg false true true
  have h100 := hnonneg true false false
  have h101 := hnonneg true false true
  have h110 := hnonneg true true false
  have h111 := hnonneg true true true
  simp only [Fintype.sum_bool, pairAtom] at hm hab11 hab10 hab01 hac11 hac01 hbc11
  constructor
  · unfold PairBounds
    repeat' apply And.intro
    all_goals linarith
  · unfold PairBounds
    repeat' apply And.intro
    all_goals linarith
  · unfold PairBounds
    repeat' apply And.intro
    all_goals linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- The four triangle inequalities are exactly the additional conditions needed
beyond the three pair tables.  The statement includes unnormalized and zero slices. -/
theorem conditions_iff_extension (s : Moments) :
    Conditions s ↔ ∃ q, IsExtension s q := by
  constructor
  · exact extension s
  · rintro ⟨q, hq⟩
    exact conditions_of_extension s q hq

end AlphaCycle.Slice
