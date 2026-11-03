import Section_2_Preliminaries.FiniteLaw
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Boolean moments and their finite inversion. A Boolean assignment is its finset
of coordinates equal to one. -/
namespace AlphaCycle
open Classical

abbrev BooleanLaw (α : Type*) [Fintype α] := Law (Finset α)

/-- The squarefree moment indexed by `s`: all coordinates of `s` equal one. -/
noncomputable def moment {α : Type*} [Fintype α]
    (μ : BooleanLaw α) (s : Finset α) : ℝ := μ.prob (fun t => s ⊆ t)

@[simp] theorem moment_empty {α : Type*} [Fintype α] (μ : BooleanLaw α) :
    moment μ ∅ = 1 := by
  simp [moment, Law.prob, μ.total]

 theorem moment_nonneg {α : Type*} [Fintype α]
    (μ : BooleanLaw α) (s : Finset α) : 0 ≤ moment μ s := μ.prob_nonneg _

 theorem moment_le_one {α : Type*} [Fintype α]
    (μ : BooleanLaw α) (s : Finset α) : moment μ s ≤ 1 := μ.prob_le_one _

/-- A moment is its exact cell mass plus all its strictly larger cell masses.
This triangular identity gives a constructive finite moment inversion. -/
 theorem moment_eq_mass_add {α : Type*} [Fintype α] [DecidableEq α]
    (μ : BooleanLaw α) (s : Finset α) :
    moment μ s = μ.mass s + ∑ t ∈ Finset.univ.erase s,
      if s ⊆ t then μ.mass t else 0 := by
  classical
  calc
    moment μ s = ∑ t, if s ⊆ t then μ.mass t else 0 := by
      unfold moment Law.prob
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : s ⊆ t <;> simp [h]
    _ = _ := by
      symm
      simpa only [if_pos (Finset.Subset.refl s)] using
        (Finset.add_sum_erase Finset.univ
          (fun t => if s ⊆ t then μ.mass t else 0) (Finset.mem_univ s))

/-- All squarefree moments determine the Boolean law. This is the finite
triangular form of Möbius inversion on the Boolean lattice. -/
 theorem law_eq_of_moments {α : Type*} [Fintype α] [DecidableEq α]
    {μ ν : BooleanLaw α} (h : ∀ s, moment μ s = moment ν s) : μ = ν := by
  ext s
  classical
  refine Finset.strongDownwardInduction (n := Fintype.card α)
    (p := fun s => μ.mass s = ν.mass s) ?_ s (Finset.card_le_univ s)
  intro s ih hs
  have hrest : (∑ t ∈ Finset.univ.erase s, if s ⊆ t then μ.mass t else 0) =
      ∑ t ∈ Finset.univ.erase s, if s ⊆ t then ν.mass t else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hst : s ⊆ t
    · rw [if_pos hst, if_pos hst]
      apply ih (Finset.card_le_univ t)
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hst, Ne.symm (Finset.mem_erase.mp ht).1⟩
    · simp [hst]
  have hm := h s
  rw [moment_eq_mass_add, moment_eq_mass_add, hrest] at hm
  linarith

/-- The moment vector is an injective coordinate system for Boolean laws. -/
 theorem moment_injective {α : Type*} [Fintype α] [DecidableEq α] :
    Function.Injective (moment (α := α)) := by
  intro μ ν h
  exact law_eq_of_moments (congrFun h)

/-- Restrict a Boolean assignment to a coordinate block. -/
noncomputable def restrictLaw {α : Type*} [Fintype α] [DecidableEq α]
    (μ : BooleanLaw α) (e : Finset α) : BooleanLaw α :=
  μ.map (fun t => t ∩ e)

 theorem moment_restrict {α : Type*} [Fintype α] [DecidableEq α]
    (μ : BooleanLaw α) (e s : Finset α) (hse : s ⊆ e) :
    moment (restrictLaw μ e) s = moment μ s := by
  rw [moment, restrictLaw, Law.prob_map, moment]
  apply Law.prob_congr
  intro t
  exact ⟨fun h => (Finset.subset_inter_iff.mp h).1,
    fun h => Finset.subset_inter_iff.mpr ⟨h, hse⟩⟩

/-- Pointwise inclusion-exclusion for a conjunction of positive and negative
Boolean literals. No disjointness hypothesis on the two index sets is needed. -/
 theorem signed_monomial_identity {α : Type*} [DecidableEq α]
    (O Z x : Finset α) :
    (∑ W ∈ Z.powerset, (-1 : ℝ) ^ W.card *
      (if O ∪ W ⊆ x then 1 else 0)) =
      if O ⊆ x ∧ Disjoint Z x then 1 else 0 := by
  classical
  by_cases ho : O ⊆ x
  · simp only [Finset.union_subset_iff, ho, true_and]
    calc
      (∑ W ∈ Z.powerset, (-1 : ℝ) ^ W.card * (if W ⊆ x then 1 else 0)) =
          ∑ W ∈ Z.powerset, (-1 : ℝ) ^ W.card *
            ∏ v ∈ W, (if v ∈ x then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro W _
        rw [Finset.prod_boole]
        rfl
      _ = ∏ v ∈ Z, (1 - if v ∈ x then (1 : ℝ) else 0) := by
        simpa using (Finset.prod_sub (fun _ : α => (1 : ℝ))
          (fun v => if v ∈ x then (1 : ℝ) else 0) Z).symm
      _ = if Disjoint Z x then 1 else 0 := by
        have hh (v : α) : (1 : ℝ) - (if v ∈ x then 1 else 0) =
            if v ∉ x then 1 else 0 := by
          by_cases h : v ∈ x <;> simp [h]
        simp_rw [hh]
        rw [Finset.prod_boole]
        congr 1
        exact propext Finset.disjoint_left.symm
  · have hn (W : Finset α) : ¬ O ∪ W ⊆ x := by
      intro h
      exact ho (Finset.Subset.trans Finset.subset_union_left h)
    simp [ho, hn]

/-- The signed moment expansion equals the probability of its Boolean literal
event. This is both cell inversion and the switching identity. -/
 theorem signed_moments_eq_probability {α : Type*} [Fintype α] [DecidableEq α]
    (μ : BooleanLaw α) (O Z : Finset α) :
    (∑ W ∈ Z.powerset, (-1 : ℝ) ^ W.card * moment μ (O ∪ W)) =
      μ.prob (fun x => O ⊆ x ∧ Disjoint Z x) := by
  classical
  unfold moment Law.prob
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = μ.mass x * ∑ W ∈ Z.powerset, (-1 : ℝ) ^ W.card *
          (if O ∪ W ⊆ x then 1 else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro W _
      by_cases h : O ∪ W ⊆ x <;> simp [h, mul_comm]
    _ = _ := by
      rw [signed_monomial_identity]
      by_cases h : O ⊆ x ∧ Disjoint Z x <;> simp [h]

/-- Explicit Boolean-lattice moment inversion: an atom is the alternating sum
of all moments obtained by adding subsets of its zero coordinates. -/
 theorem mass_eq_signed_moments {α : Type*} [Fintype α] [DecidableEq α]
    (μ : BooleanLaw α) (O : Finset α) :
    μ.mass O = ∑ W ∈ (Finset.univ \ O).powerset,
      (-1 : ℝ) ^ W.card * moment μ (O ∪ W) := by
  classical
  rw [signed_moments_eq_probability]
  have h (x : Finset α) : (O ⊆ x ∧ Disjoint (Finset.univ \ O) x) ↔ x = O := by
    constructor
    · rintro ⟨ho, hd⟩
      apply Finset.Subset.antisymm _ ho
      intro v hv
      by_contra hn
      exact Finset.disjoint_left.mp hd (by simp [hn]) hv
    · rintro rfl
      refine ⟨Finset.Subset.refl _, ?_⟩
      rw [Finset.disjoint_left]
      intro v hv hvO
      exact (Finset.mem_sdiff.mp hv).2 hvO
  rw [Law.prob_congr μ h]
  unfold Law.prob
  symm
  rw [Finset.sum_eq_single O]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

end AlphaCycle
