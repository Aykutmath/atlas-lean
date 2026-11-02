import AHHWordRecurrence

/-! Canonical enumeration of every non-last occurrence of the first letter.
The occurrence-to-rearrangement map is injective because the recorded prefix length
is exactly the occurrence position. This supplies concrete finite move sets to the
word recurrence, including the base term at position zero. -/
noncomputable section
namespace AHH
attribute [local instance] Classical.propDecidable
variable {α : Type*}

/-- A word containing `s` has a split at its first `s`. -/
theorem exists_first_split (s : α) (w : List α) (h : s ∈ w) :
    ∃ A B, w = A ++ [s] ++ B ∧ s ∉ A := by
  classical
  induction w with
  | nil => simp at h
  | cons a w ih =>
      by_cases ha : a = s
      · subst a; exact ⟨[], w, by simp, by simp⟩
      · have has : s ≠ a := Ne.symm ha
        have hw : s ∈ w := by simpa [has] using h
        obtain ⟨A, B, heq, hn⟩ := ih hw
        exact ⟨a :: A, B, by simp [heq], by simp [has, hn]⟩

/-- An actual non-last occurrence, indexed by its position in the word. -/
abbrev MovablePosition (W : List α) (s : α) :=
  {i : Fin W.length // W[i.val]? = some s ∧ s ∈ W.drop (i.val + 1)}

namespace MovablePosition

/-- The first marker in the remaining suffix. -/
def nextPrefix {W : List α} {s : α} (i : MovablePosition W s) : List α :=
  (exists_first_split s (W.drop (i.val.val + 1)) i.property.2).choose

def nextTail {W : List α} {s : α} (i : MovablePosition W s) : List α :=
  ((exists_first_split s (W.drop (i.val.val + 1)) i.property.2).choose_spec).choose

theorem next_eq {W : List α} {s : α} (i : MovablePosition W s) :
    W.drop (i.val.val + 1) = i.nextPrefix ++ [s] ++ i.nextTail :=
  ((exists_first_split s (W.drop (i.val.val + 1)) i.property.2).choose_spec).choose_spec.1

theorem next_avoids {W : List α} {s : α} (i : MovablePosition W s) :
    s ∉ i.nextPrefix :=
  ((exists_first_split s (W.drop (i.val.val + 1)) i.property.2).choose_spec).choose_spec.2

/-- Actual rearrangement record for this occurrence. -/
def move {W : List α} {s : α} (hhead : W.head? = some s)
    (i : MovablePosition W s) : Rearrangement α where
  s := s
  U := W.take i.val.val
  V := s :: i.nextTail
  A := i.nextPrefix
  V_head := rfl
  U_head := by
    by_cases hi : i.val.val = 0
    · left; simp [hi]
    · right; simpa [List.head?_take, hi] using hhead
  A_avoids := i.next_avoids

@[simp] theorem move_prefix_length {W : List α} {s : α} (hhead : W.head? = some s)
    (i : MovablePosition W s) : (i.move hhead).U.length = i.val.val := by
  exact List.length_take_of_le i.val.isLt.le

/-- Reconstruction proves that no new word is silently introduced by the move map. -/
theorem move_original {W : List α} {s : α} (hhead : W.head? = some s)
    (i : MovablePosition W s) : (i.move hhead).original = W := by
  have helem : W[i.val.val] = s := (List.getElem?_eq_some_iff.mp i.property.1).2
  have hdrop : s :: W.drop (i.val.val + 1) = W.drop i.val.val := by
    simpa [helem] using (List.getElem_cons_drop (as := W) (i := i.val.val) i.val.isLt)
  calc
    (i.move hhead).original = W.take i.val.val ++ s :: W.drop (i.val.val + 1) := by
      simp [move, Rearrangement.original, i.next_eq, List.append_assoc]
    _ = W.take i.val.val ++ W.drop i.val.val := by rw [hdrop]
    _ = W := List.take_append_drop _ _

theorem move_injective {W : List α} {s : α} (hhead : W.head? = some s) :
    Function.Injective (fun i : MovablePosition W s => i.move hhead) := by
  intro i j h
  have hh := congrArg (fun d : Rearrangement α => d.U.length) h
  simp only [move_prefix_length] at hh
  apply Subtype.ext
  exact Fin.ext hh

/-- The canonical next split agrees with any concrete split whose prefix avoids `s`. -/
theorem next_unique {W : List α} {s : α} (i : MovablePosition W s)
    {A B : List α} (heq : W.drop (i.val.val + 1) = A ++ [s] ++ B) (havoid : s ∉ A) :
    i.nextPrefix = A ∧ i.nextTail = B := by
  apply first_marker_inj s i.next_avoids havoid
  simpa [List.append_assoc] using i.next_eq.symm.trans heq

end MovablePosition

namespace WordSplit

def moves (d : WordSplit α) : Finset (Rearrangement α) := by
  classical
  exact Finset.univ.image (fun i : MovablePosition d.original d.s => i.move d.original_head)

theorem mem_moves_original (d : WordSplit α) (r : Rearrangement α) (hr : r ∈ d.moves) :
    r.original = d.original := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  exact i.move_original d.original_head

/-- The move set has no more than `j-1` elements: every movable occurrence has a later one. -/
theorem card_moves_le (d : WordSplit α) : d.moves.card ≤ d.original.length - 1 := by
  classical
  let f : MovablePosition d.original d.s → Fin (d.original.length - 1) := fun i =>
    ⟨i.val.val, by
      have hp : 0 < (d.original.drop (i.val.val + 1)).length :=
        List.length_pos_iff.mpr (List.ne_nil_of_mem i.property.2)
      simp only [List.length_drop] at hp
      omega⟩
  have hf : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    apply Fin.ext
    simpa [f] using congrArg (fun x : Fin (d.original.length - 1) => x.val) h
  calc
    d.moves.card = Fintype.card (MovablePosition d.original d.s) := by
      rw [moves, Finset.card_image_of_injective _ (MovablePosition.move_injective d.original_head)]
      exact Finset.card_univ
    _ ≤ Fintype.card (Fin (d.original.length - 1)) := Fintype.card_le_of_injective f hf
    _ = _ := Fintype.card_fin _

/-- A later occurrence exists exactly before the final designated first letter. -/
theorem later_mem_iff_before_last (d : WordSplit α) (i : ℕ) :
    d.s ∈ d.original.drop (i + 1) ↔ i < d.L.length := by
  by_cases hi : i < d.L.length
  · rw [original, List.append_assoc, List.drop_append_of_le_length (by omega)]
    simp [hi]
  · have heq : i + 1 = d.L.length + (i + 1 - d.L.length) := by omega
    have hdiff : i + 1 - d.L.length = (i - d.L.length) + 1 := by omega
    rw [original, List.append_assoc, heq, List.drop_length_add_append, hdiff]
    simp only [List.singleton_append, List.drop_succ_cons]
    constructor
    · intro hm
      exact (d.R_avoids (List.mem_of_mem_drop hm)).elim
    · intro h; exact (hi h).elim

/-- Re-indexing canonical moves by their positions preserves the sum exactly. -/
theorem sum_moves_eq_positions (d : WordSplit α) (F : Rearrangement α → ℝ) :
    ∑ r ∈ d.moves, F r =
      ∑ i : MovablePosition d.original d.s, F (i.move d.original_head) := by
  classical
  rw [moves, Finset.sum_image (fun i _ j _ h => MovablePosition.move_injective d.original_head h)]

/-- Every repeated word has its base deletion at position zero in the canonical move family. -/
def basePosition (d : WordSplit α) : MovablePosition d.original d.s :=
  ⟨⟨0, by
    have h := d.left_ne_nil
    simp [original]
    ⟩,
   by simpa only [List.head?_eq_getElem?] using d.original_head,
   (d.later_mem_iff_before_last 0).mpr (List.length_pos_iff.mpr d.left_ne_nil)⟩

@[simp] theorem basePosition_prefix (d : WordSplit α) :
    ((d.basePosition).move d.original_head).U = [] := by simp [MovablePosition.move, basePosition]

end WordSplit
end AHH
