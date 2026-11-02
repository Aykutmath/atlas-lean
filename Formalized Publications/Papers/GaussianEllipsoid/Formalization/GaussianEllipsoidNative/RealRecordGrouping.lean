import Mathlib.Data.List.TakeWhile
import Mathlib.Data.List.Chain
import Mathlib.Tactic

namespace GaussianEllipsoid.PaperRealRecord

/-- A finite certificate for the first-later-q-multiple support selection rule.
Each output block consists of its record and the intervening smaller levels. -/
inductive RecordGrouping {α : Type*} (q : ℝ) (weight : α → ℝ) : List α → List (List α) → Prop
  | nil : RecordGrouping q weight [] []
  | cons (a : α) (pref rest : List α) (groups : List (List α))
      (small : ∀ b ∈ pref, weight b < q * weight a)
      (next : ∀ b tail, rest = b :: tail → q * weight a ≤ weight b)
      (rec : RecordGrouping q weight rest groups) :
      RecordGrouping q weight (a :: (pref ++ rest)) ((a :: pref) :: groups)

/-- Every finite list has a greedy record decomposition. No restriction on
length, gaps, zeros, or dynamic range is required. -/
theorem exists_recordGrouping {α : Type*} (q : ℝ) (weight : α → ℝ) (xs : List α) :
    ∃ groups, RecordGrouping q weight xs groups := by
  classical
  have hall : ∀ n : ℕ, ∀ ys : List α, ys.length = n →
      ∃ groups, RecordGrouping q weight ys groups := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ys hy
      cases ys with
      | nil => exact ⟨[], RecordGrouping.nil⟩
      | cons a tail =>
        let p : α → Bool := fun b => decide (weight b < q * weight a)
        let pref := tail.takeWhile p
        let rest := tail.dropWhile p
        have hsplit : pref ++ rest = tail := List.takeWhile_append_dropWhile
        have hlen : rest.length < n := by
          have hslen := congrArg List.length hsplit
          simp only [List.length_append] at hslen
          simp only [List.length_cons] at hy
          omega
        obtain ⟨groups, hg⟩ := ih rest.length hlen rest rfl
        have hsmall : ∀ b ∈ pref, weight b < q * weight a := by
          intro b hb
          have hh := List.mem_takeWhile_imp hb
          simpa [p] using hh
        have hnext : ∀ b bs, rest = b :: bs → q * weight a ≤ weight b := by
          intro b bs hb
          have hh := List.head?_dropWhile_not p tail
          change (match rest.head? with | some x => p x = false | none => True) at hh
          rw [hb] at hh
          simp only [List.head?_cons] at hh
          have hn : ¬ weight b < q * weight a := by simpa [p] using hh
          exact le_of_not_gt hn
        have hcert := RecordGrouping.cons a pref rest groups hsmall hnext hg
        rw [hsplit] at hcert
        exact ⟨(a :: pref) :: groups, hcert⟩
  exact hall xs.length xs rfl

/-- The grouping preserves the exact original order and every input entry. -/
theorem RecordGrouping.flatten_eq {α : Type*} {q : ℝ} {weight : α → ℝ}
    {xs : List α} {groups : List (List α)} (h : RecordGrouping q weight xs groups) :
    groups.flatten = xs := by
  induction h with
  | nil => rfl
  | cons a pref rest groups small next rec ih =>
      simp [List.flatten_cons, ih]

/-- Every group is nonempty and all its nonrecord entries lie below the next
support-record threshold. -/
theorem RecordGrouping.regular {α : Type*} {q : ℝ} {weight : α → ℝ}
    {xs : List α} {groups : List (List α)} (h : RecordGrouping q weight xs groups) :
    ∀ g ∈ groups, ∃ a pref, g = a :: pref ∧
      ∀ b ∈ pref, weight b < q * weight a := by
  induction h with
  | nil => simp
  | cons a pref rest groups small next rec ih =>
      intro g hg
      rcases List.mem_cons.mp hg with heq | htail
      · subst g
        exact ⟨a, pref, rfl, small⟩
      · exact ih g htail

def RecordSuccessor {α : Type*} (q : ℝ) (weight : α → ℝ) (g h : List α) : Prop :=
  ∀ a ∈ g.head?, ∀ b ∈ h.head?, q * weight a ≤ weight b

/-- Consecutive selected records grow by a factor of at least q. -/
theorem RecordGrouping.chain {α : Type*} {q : ℝ} {weight : α → ℝ}
    {xs : List α} {groups : List (List α)} (h : RecordGrouping q weight xs groups) :
    groups.IsChain (RecordSuccessor q weight) := by
  induction h with
  | nil => simp
  | cons a pref rest groups small next rec ih =>
      cases groups with
      | nil => simp
      | cons g gs =>
        obtain ⟨b, tail, hg, _⟩ := rec.regular g (by simp)
        subst g
        have hr : rest = b :: (tail ++ gs.flatten) := by
          simpa using rec.flatten_eq.symm
        have hb := next b (tail ++ gs.flatten) hr
        apply List.IsChain.cons ih
        intro y hy
        simp only [List.head?_cons, Option.mem_some_iff] at hy
        subst y
        simpa [RecordSuccessor] using hb

#print axioms exists_recordGrouping
#print axioms RecordGrouping.flatten_eq
#print axioms RecordGrouping.regular
#print axioms RecordGrouping.chain

end GaussianEllipsoid.PaperRealRecord
