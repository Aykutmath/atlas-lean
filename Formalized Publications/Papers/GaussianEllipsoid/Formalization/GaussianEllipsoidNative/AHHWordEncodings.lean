import Mathlib.Data.List.Count
import Mathlib.Data.Fintype.List
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Common
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Explicit two-cut and three-cut AHH word encodings

These are combinatorial theorems about actual words, for every alphabet. They do
not assume either of the claimed multiplicity bounds. `Rearrangement` is the
block move `U s A V ↦ U V A`, where `V` starts with the removed letter. `Collision`
is the rank-one trace merge `U a V; X a Y ↦ U a Y X a V`. The records include the
word pieces themselves, rather than assuming an abstract injective map.

For an output of length `j - 1`, the fibers have at most `j²` and `j³` elements.
This file is independent of Haar integration and does not assert a moment law.
-/
noncomputable section
open scoped BigOperators
namespace AHH
variable {α : Type*}

/-- A rearrangement used in elimination of a repeated first letter. -/
@[ext] structure Rearrangement (α : Type*) where
  s : α
  U : List α
  V : List α
  A : List α
  V_head : V.head? = some s
  U_head : U = [] ∨ U.head? = some s
  A_avoids : s ∉ A

namespace Rearrangement

def output (d : Rearrangement α) : List α := d.U ++ d.V ++ d.A

def original (d : Rearrangement α) : List α := d.U ++ [d.s] ++ d.A ++ d.V

/-- The eliminated occurrence's block index is recovered without an extra choice. -/
def index [DecidableEq α] (d : Rearrangement α) : ℕ := d.U.count d.s + 1

@[simp] theorem original_length (d : Rearrangement α) :
    d.original.length = d.output.length + 1 := by
  simp [original, output]
  omega

/-- The first output letter is exactly the removed letter, also when `U` is empty. -/
theorem output_head (d : Rearrangement α) : d.output.head? = some d.s := by
  rcases d.U_head with h | h
  · simp [output, h, d.V_head]
  · simp [output, h]

/-- The two recorded cuts are `|U|` and `|U| + |V|`. -/
def cuts (d : Rearrangement α) : ℕ × ℕ := (d.U.length, d.U.length + d.V.length)

theorem cuts_injective (d e : Rearrangement α)
    (ho : d.output = e.output) (hc : d.cuts = e.cuts) : d = e := by
  have hUlen : d.U.length = e.U.length := congrArg Prod.fst hc
  have hUVlen : d.U.length + d.V.length = e.U.length + e.V.length :=
    congrArg Prod.snd hc
  have hVlen : d.V.length = e.V.length := by omega
  have ho' : d.U ++ (d.V ++ d.A) = e.U ++ (e.V ++ e.A) := by
    simpa [output, List.append_assoc] using ho
  obtain ⟨hU, hVA⟩ := List.append_inj ho' hUlen
  obtain ⟨hV, hA⟩ := List.append_inj hVA hVlen
  have hs : d.s = e.s := by
    have h := congrArg List.head? hV
    simpa [d.V_head, e.V_head] using h
  exact Rearrangement.ext hs hU hV hA

/-- Literal inverse: the first cut recovers `U`. -/
theorem decode_U (d : Rearrangement α) :
    d.output.take d.cuts.1 = d.U := by
  simp [output, cuts, List.append_assoc]

/-- Literal inverse: dropping the first cut and taking the cut difference recovers `V`. -/
theorem decode_V (d : Rearrangement α) :
    (d.output.drop d.cuts.1).take (d.cuts.2 - d.cuts.1) = d.V := by
  simp [output, cuts, List.append_assoc]

/-- Literal inverse: dropping the second cut recovers the moved block. -/
theorem decode_A (d : Rearrangement α) :
    d.output.drop d.cuts.2 = d.A := by
  simpa [output, cuts] using (List.drop_append_length (l₁ := d.U ++ d.V) (l₂ := d.A))

abbrev Fiber (o : List α) := {d : Rearrangement α // d.output = o}

/-- No alphabet factor occurs: both letters and all blocks are read from the output. -/
def fiberCode (o : List α) (d : Fiber o) : Fin (o.length + 1) × Fin (o.length + 1) :=
  (⟨d.val.U.length, by have := congrArg List.length d.property; simp [output] at this; omega⟩,
   ⟨d.val.U.length + d.val.V.length, by
     have := congrArg List.length d.property; simp [output] at this; omega⟩)

theorem fiberCode_injective (o : List α) : Function.Injective (fiberCode o) := by
  intro d e h
  apply Subtype.ext
  apply cuts_injective d.val e.val (d.property.trans e.property.symm)
  have h₁ := congrArg (fun q : Fin (o.length + 1) × Fin (o.length + 1) => q.1.val) h
  have h₂ := congrArg (fun q : Fin (o.length + 1) × Fin (o.length + 1) => q.2.val) h
  exact Prod.ext h₁ h₂

instance fiberFinite (o : List α) : Finite (Fiber o) :=
  Finite.of_injective (fiberCode o) (fiberCode_injective o)

/-- The actual rearrangement multiplicity bound: two cuts, hence `(length + 1)²`. -/
theorem fiber_card_le (o : List α) : Nat.card (Fiber o) ≤ (o.length + 1) ^ 2 := by
  have h := Nat.card_le_card_of_injective (fiberCode o) (fiberCode_injective o)
  simpa [Nat.card_eq_fintype_card, pow_two] using h

/-- A finite collection cannot contain more preimages than the full fiber. -/
theorem filter_card_le [DecidableEq α] (D : Finset (Rearrangement α)) (o : List α) :
    (D.filter (fun d => d.output = o)).card ≤ (o.length + 1) ^ 2 := by
  classical
  calc
    _ ≤ ((Finset.range (o.length + 1)).product (Finset.range (o.length + 1))).card := by
      apply Finset.card_le_card_of_injOn cuts
      · intro d hd
        have ho := (Finset.mem_filter.mp hd).2
        have hl := congrArg List.length ho
        simp only [output, List.length_append] at hl
        apply Finset.mem_product.mpr
        constructor <;> apply Finset.mem_range.mpr <;> dsimp [cuts] <;> omega
      · intro d hd e he hc
        exact cuts_injective d e ((Finset.mem_filter.mp hd).2.trans
          (Finset.mem_filter.mp he).2.symm) hc
    _ = _ := by simp [pow_two]

/-- Weighted actual-word rearrangement counting, with no independent choice of a letter. -/
theorem sum_output_le (D : Finset (Rearrangement α)) (W : Finset (List α))
    (n : ℕ) (weight : List α → ℝ) (hweight : ∀ w, 0 ≤ weight w)
    (hmap : ∀ d ∈ D, d.output ∈ W) (hlen : ∀ w ∈ W, w.length = n) :
    ∑ d ∈ D, weight d.output ≤ (n + 1 : ℕ) ^ 2 * ∑ w ∈ W, weight w := by
  classical
  rw [Finset.sum_comp weight output]
  calc
    _ ≤ ∑ w ∈ D.image output, ((n + 1 : ℕ) ^ 2 : ℝ) * weight w := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
      have hc := filter_card_le D d.output
      rw [hlen d.output (hmap d hd)] at hc
      simpa only [nsmul_eq_mul, Nat.cast_pow] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (hweight d.output)
    _ ≤ ∑ w ∈ W, ((n + 1 : ℕ) ^ 2 : ℝ) * weight w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr hmap
      · intro w _ _; exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hweight w)
    _ = _ := by rw [Finset.mul_sum]

end Rearrangement

/-- A split trace with a designated occurrence of a shared letter on either side.
The left prefix is nonempty and starts with the original first letter. -/
@[ext] structure Collision (α : Type*) where
  s : α
  a : α
  U : List α
  V : List α
  X : List α
  Y : List α
  U_head : U.head? = some s

namespace Collision

/-- In an actual shared-letter split, the right word avoids `s`, so the shared
letter differs from `s`; its occurrence in the left word must follow the first letter. -/
theorem shared_prefix_head {s a : α} {U V X Y : List α}
    (hleft : (U ++ [a] ++ V).head? = some s)
    (havoid : s ∉ X ++ [a] ++ Y) : U.head? = some s := by
  have hne : a ≠ s := by
    intro h
    subst a
    exact havoid (by simp)
  cases U with
  | nil => simp only [List.nil_append, List.singleton_append, List.head?_cons,
      Option.some.injEq] at hleft; exact (hne hleft).elim
  | cons b U => simpa using hleft

/-- Construct the merge record from concrete split words, deriving nonempty prefix. -/
def ofSplit (s a : α) (U V X Y : List α)
    (hleft : (U ++ [a] ++ V).head? = some s)
    (havoid : s ∉ X ++ [a] ++ Y) : Collision α :=
  ⟨s, a, U, V, X, Y, shared_prefix_head hleft havoid⟩

def left (d : Collision α) : List α := d.U ++ [d.a] ++ d.V

def right (d : Collision α) : List α := d.X ++ [d.a] ++ d.Y

def original (d : Collision α) : List α := d.left ++ [d.s] ++ d.right

def output (d : Collision α) : List α := d.U ++ [d.a] ++ d.Y ++ d.X ++ [d.a] ++ d.V

/-- First shared-letter position, middle cut, second shared-letter position. -/
def cuts (d : Collision α) : ℕ × ℕ × ℕ :=
  (d.U.length, d.U.length + 1 + d.Y.length, d.U.length + 1 + d.Y.length + d.X.length)

@[simp] theorem original_length (d : Collision α) :
    d.original.length = d.output.length + 1 := by
  simp [original, left, right, output]
  omega

theorem output_head (d : Collision α) : d.output.head? = some d.s := by
  simp [output, d.U_head]

/-- The three cuts reconstruct every field, including both letters. -/
theorem cuts_injective (d e : Collision α)
    (ho : d.output = e.output) (hc : d.cuts = e.cuts) : d = e := by
  have hUlen : d.U.length = e.U.length := congrArg (fun x => x.1) hc
  have hUYlen : d.U.length + 1 + d.Y.length = e.U.length + 1 + e.Y.length :=
    congrArg (fun x => x.2.1) hc
  have hUYXlen : d.U.length + 1 + d.Y.length + d.X.length =
      e.U.length + 1 + e.Y.length + e.X.length := congrArg (fun x => x.2.2) hc
  have hYlen : d.Y.length = e.Y.length := by omega
  have hXlen : d.X.length = e.X.length := by omega
  have ho' : d.U ++ (d.a :: (d.Y ++ (d.X ++ (d.a :: d.V)))) =
      e.U ++ (e.a :: (e.Y ++ (e.X ++ (e.a :: e.V)))) := by
    simpa [output, List.append_assoc] using ho
  obtain ⟨hU, hrest⟩ := List.append_inj ho' hUlen
  obtain ⟨ha, hrest⟩ := List.cons.inj hrest
  obtain ⟨hY, hrest⟩ := List.append_inj hrest hYlen
  obtain ⟨hX, hrest⟩ := List.append_inj hrest hXlen
  have hV := (List.cons.inj hrest).2
  have hs : d.s = e.s := by
    have h := congrArg List.head? hU
    simpa [d.U_head, e.U_head] using h
  exact Collision.ext hs ha hU hV hX hY

abbrev Fiber (o : List α) := {d : Collision α // d.output = o}

def fiberCode (o : List α) (d : Fiber o) :
    Fin (o.length + 1) × Fin (o.length + 1) × Fin (o.length + 1) :=
  (⟨d.val.U.length, by have := congrArg List.length d.property; simp [output] at this; omega⟩,
   ⟨d.val.U.length + 1 + d.val.Y.length, by
     have := congrArg List.length d.property; simp [output] at this; omega⟩,
   ⟨d.val.U.length + 1 + d.val.Y.length + d.val.X.length, by
     have := congrArg List.length d.property; simp [output] at this; omega⟩)

theorem fiberCode_injective (o : List α) : Function.Injective (fiberCode o) := by
  intro d e h
  apply Subtype.ext
  apply cuts_injective d.val e.val (d.property.trans e.property.symm)
  have h₁ := congrArg (fun q : Fin (o.length + 1) × Fin (o.length + 1) × Fin (o.length + 1) => q.1.val) h
  have h₂ := congrArg (fun q : Fin (o.length + 1) × Fin (o.length + 1) × Fin (o.length + 1) => q.2.1.val) h
  have h₃ := congrArg (fun q : Fin (o.length + 1) × Fin (o.length + 1) × Fin (o.length + 1) => q.2.2.val) h
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

instance fiberFinite (o : List α) : Finite (Fiber o) :=
  Finite.of_injective (fiberCode o) (fiberCode_injective o)

/-- The actual collision-gluing multiplicity bound: three cuts, hence `(length + 1)³`. -/
theorem fiber_card_le (o : List α) : Nat.card (Fiber o) ≤ (o.length + 1) ^ 3 := by
  have h := Nat.card_le_card_of_injective (fiberCode o) (fiberCode_injective o)
  simpa [Nat.card_eq_fintype_card, pow_succ, pow_two, Nat.mul_assoc] using h

theorem filter_card_le [DecidableEq α] (D : Finset (Collision α)) (o : List α) :
    (D.filter (fun d => d.output = o)).card ≤ (o.length + 1) ^ 3 := by
  classical
  calc
    _ ≤ ((Finset.range (o.length + 1)).product
        ((Finset.range (o.length + 1)).product (Finset.range (o.length + 1)))).card := by
      apply Finset.card_le_card_of_injOn cuts
      · intro d hd
        have ho := (Finset.mem_filter.mp hd).2
        have hl := congrArg List.length ho
        simp only [output, List.length_append, List.length_singleton] at hl
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_range.mpr; dsimp [cuts]; omega
        · apply Finset.mem_product.mpr
          constructor <;> apply Finset.mem_range.mpr <;> dsimp [cuts] <;> omega
      · intro d hd e he hc
        exact cuts_injective d e ((Finset.mem_filter.mp hd).2.trans
          (Finset.mem_filter.mp he).2.symm) hc
    _ = _ := by simp [pow_succ, pow_two, Nat.mul_assoc]

/-- Weighted actual-word collision counting. The designated shared letter is read
from either recorded position; it does not create an extra alphabet factor. -/
theorem sum_output_le (D : Finset (Collision α)) (W : Finset (List α))
    (n : ℕ) (weight : List α → ℝ) (hweight : ∀ w, 0 ≤ weight w)
    (hmap : ∀ d ∈ D, d.output ∈ W) (hlen : ∀ w ∈ W, w.length = n) :
    ∑ d ∈ D, weight d.output ≤ (n + 1 : ℕ) ^ 3 * ∑ w ∈ W, weight w := by
  classical
  rw [Finset.sum_comp weight output]
  calc
    _ ≤ ∑ w ∈ D.image output, ((n + 1 : ℕ) ^ 3 : ℝ) * weight w := by
      apply Finset.sum_le_sum
      intro w hw
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
      have hc := filter_card_le D d.output
      rw [hlen d.output (hmap d hd)] at hc
      simpa only [nsmul_eq_mul, Nat.cast_pow] using
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (hweight d.output)
    _ ≤ ∑ w ∈ W, ((n + 1 : ℕ) ^ 3 : ℝ) * weight w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.image_subset_iff.mpr hmap
      · intro w _ _; exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hweight w)
    _ = _ := by rw [Finset.mul_sum]

end Collision
end AHH
