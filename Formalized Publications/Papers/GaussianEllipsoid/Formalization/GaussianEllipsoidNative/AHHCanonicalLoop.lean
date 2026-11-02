import AHHCanonicalMoves
import Mathlib.Algebra.BigOperators.Fin

/-! Exact conversion of the Gaussian position loop to canonical word moves.
Only cyclic trace and rank-one gluing identities are hypotheses here; finite
index partitioning, the final occurrence and all move inverses are proved. -/
noncomputable section
open scoped BigOperators
namespace AHH
attribute [local instance] Classical.propDecidable
variable {α : Type*}

/-- Position zero is the covariance contraction; positive positions are derivative terms. -/
def loopPositionTerm (f : List α → ℝ) (g : List α → List α → ℝ)
    (W : List α) (s : α) (i : Fin W.length) : ℝ :=
  if i.val = 0 then f W.tail else
    if W[i.val]? = some s then g (W.take i.val) (W.drop (i.val + 1)) else 0

theorem sum_loopPositionTerm_cons (f : List α → ℝ) (g : List α → List α → ℝ)
    (s : α) (w : List α) :
    (∑ i : Fin (s :: w).length, loopPositionTerm f g (s :: w) s i) =
      f w + ∑ k : Fin w.length, if s = w.get k then
        g (s :: w.take k.val) (w.drop (k.val + 1)) else 0 := by
  change (∑ i : Fin (w.length + 1), loopPositionTerm f g (s :: w) s i) = _
  rw [Fin.sum_univ_succ]
  simp [loopPositionTerm, List.get_eq_getElem, eq_comm]

namespace WordSplit

def lastPosition (d : WordSplit α) : Fin d.original.length :=
  ⟨d.L.length, by simp [original]⟩

theorem occurrence_le_last (d : WordSplit α) (i : Fin d.original.length)
    (hi : d.original[i.val]? = some d.s) : i.val ≤ d.L.length := by
  by_contra h
  have hlt : d.L.length < i.val := by omega
  have hd : i.val - d.L.length = (i.val - d.L.length - 1) + 1 := by omega
  have hr : d.R[i.val - d.L.length - 1]? = some d.s := by
    have hi' : (d.L ++ (d.s :: d.R))[i.val]? = some d.s := by
      simpa only [original, List.append_assoc, List.singleton_append] using hi
    rw [List.getElem?_append_right hlt.le, hd, List.getElem?_cons_succ] at hi'
    exact hi'
  exact d.R_avoids (List.mem_of_getElem? hr)

theorem loopPositionTerm_last (f : List α → ℝ) (g : List α → List α → ℝ)
    (d : WordSplit α) : loopPositionTerm f g d.original d.s d.lastPosition = g d.L d.R := by
  have hL : d.L.length ≠ 0 := ne_of_gt (List.length_pos_iff.mpr d.left_ne_nil)
  have hget : d.original[d.L.length]? = some d.s := by
    simp [original, List.append_assoc, List.getElem?_append_right]
  simp only [loopPositionTerm, lastPosition, hL, if_false, hget, if_true]
  congr 1
  · simp [original, List.append_assoc]
  · have heq : d.L.length + 1 = (d.L ++ [d.s]).length := by simp
    rw [original, heq, List.drop_append_length]

/-- Every non-last eligible summand is exactly its canonical rearranged trace. -/
theorem loopPositionTerm_move (f : List α → ℝ) (g : List α → List α → ℝ)
    (hcyclic : ∀ U V, f (U ++ V) = f (V ++ U))
    (hglue : ∀ (a : α) U V X Y,
      g (U ++ [a] ++ V) (X ++ [a] ++ Y) = f (U ++ [a] ++ Y ++ X ++ [a] ++ V))
    (d : WordSplit α) (i : MovablePosition d.original d.s) :
    loopPositionTerm f g d.original d.s i.val = f (i.move d.original_head).output := by
  by_cases hi : i.val.val = 0
  · have htail : d.original.tail = i.nextPrefix ++ [d.s] ++ i.nextTail := by
      simpa [hi] using i.next_eq
    rw [loopPositionTerm, if_pos hi, htail]
    simpa [MovablePosition.move, Rearrangement.output, hi, List.append_assoc] using
      hcyclic i.nextPrefix (d.s :: i.nextTail)
  · have hUhead : (d.original.take i.val.val).head? = some d.s := by
      simpa [List.head?_take, hi] using d.original_head
    obtain ⟨U, hU⟩ := List.head?_eq_some_iff.mp hUhead
    rw [loopPositionTerm, if_neg hi, if_pos i.property.1, i.next_eq, hU]
    have hg := hglue d.s [] U i.nextPrefix i.nextTail
    simp only [List.nil_append, List.singleton_append] at hg
    rw [hg]
    have hc := hcyclic ((d.s :: i.nextTail) ++ i.nextPrefix) (d.s :: U)
    simpa [MovablePosition.move, Rearrangement.output, hU, List.append_assoc] using hc

/-- Summands outside the last position and actual move positions vanish. -/
theorem loopPositionTerm_zero (f : List α → ℝ) (g : List α → List α → ℝ)
    (d : WordSplit α) (i : Fin d.original.length) (hlast : i ≠ d.lastPosition)
    (hmove : ¬ (d.original[i.val]? = some d.s ∧ d.s ∈ d.original.drop (i.val + 1))) :
    loopPositionTerm f g d.original d.s i = 0 := by
  have hi0 : i.val ≠ 0 := by
    intro hi
    apply hmove
    constructor
    · simpa only [hi, ← List.head?_eq_getElem?] using d.original_head
    · apply (d.later_mem_iff_before_last i.val).mpr
      rw [hi]; exact List.length_pos_iff.mpr d.left_ne_nil
  rw [loopPositionTerm, if_neg hi0]
  apply if_neg
  intro hget
  apply hmove
  refine ⟨hget, (d.later_mem_iff_before_last i.val).mpr ?_⟩
  have hle := d.occurrence_le_last i hget
  have hne : i.val ≠ d.L.length := by
    intro h
    apply hlast
    exact Fin.ext h
  omega

/-- Exact partition of the position loop into the last split and canonical moves. -/
theorem sum_loopPositionTerm (f : List α → ℝ) (g : List α → List α → ℝ)
    (hcyclic : ∀ U V, f (U ++ V) = f (V ++ U))
    (hglue : ∀ (a : α) U V X Y,
      g (U ++ [a] ++ V) (X ++ [a] ++ Y) = f (U ++ [a] ++ Y ++ X ++ [a] ++ V))
    (d : WordSplit α) :
    (∑ i : Fin d.original.length, loopPositionTerm f g d.original d.s i) =
      g d.L d.R + ∑ r ∈ d.moves, f r.output := by
  classical
  let P : Fin d.original.length → Prop := fun i =>
    d.original[i.val]? = some d.s ∧ d.s ∈ d.original.drop (i.val + 1)
  let I := Finset.univ.filter P
  have hlast : d.lastPosition ∉ I := by
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, P]
    intro h
    have hl := (d.later_mem_iff_before_last d.L.length).mp h.2
    exact (Nat.lt_irrefl _ hl)
  have hsupport : (∑ i : Fin d.original.length, loopPositionTerm f g d.original d.s i) =
      ∑ i ∈ insert d.lastPosition I, loopPositionTerm f g d.original d.s i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply loopPositionTerm_zero f g d i
    · intro heq; exact hi (by simp [heq])
    · intro hp
      exact hi (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩))
  rw [hsupport, Finset.sum_insert hlast, loopPositionTerm_last]
  congr 1
  rw [d.sum_moves_eq_positions (fun r => f r.output)]
  calc
    _ = ∑ i : MovablePosition d.original d.s, loopPositionTerm f g d.original d.s i.val := by
      have hh := Finset.sum_subtype_eq_sum_filter
        (s := Finset.univ) (p := P) (loopPositionTerm f g d.original d.s)
      simpa only [I, Finset.subtype_univ] using hh.symm
    _ = _ := Finset.sum_congr rfl (fun i _ => loopPositionTerm_move f g hcyclic hglue d i)

/-- The exact Gaussian position loop implies the canonical loop required by
`moment_bound_of_one_subsystem_laws`; no combinatorial premise remains. -/
theorem canonical_loop_of_position_loop (f : List α → ℝ) (g : List α → List α → ℝ)
    (hcyclic : ∀ U V, f (U ++ V) = f (V ++ U))
    (hglue : ∀ (a : α) U V X Y,
      g (U ++ [a] ++ V) (X ++ [a] ++ Y) = f (U ++ [a] ++ Y ++ X ++ [a] ++ V))
    (H : ℝ)
    (hloop : ∀ s w, f (s :: w) =
      (f w + ∑ k : Fin w.length, if s = w.get k then
        g (s :: w.take k.val) (w.drop (k.val + 1)) else 0) / H)
    (d : WordSplit α) :
    f d.original = (g d.L d.R + ∑ r ∈ d.moves, f r.output) / H := by
  obtain ⟨w, hw⟩ := List.head?_eq_some_iff.mp d.original_head
  have hh := hloop d.s w
  rw [← sum_loopPositionTerm_cons f g d.s w] at hh
  have hs := sum_loopPositionTerm f g hcyclic hglue d
  rw [hw] at hs
  simpa only [← hw, hs] using hh

end WordSplit
end AHH
