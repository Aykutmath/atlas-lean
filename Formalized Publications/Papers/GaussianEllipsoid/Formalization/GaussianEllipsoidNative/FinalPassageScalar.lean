import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Measure.Basic

/-!
Pure Mathlib lemmas for the final mixed-norm assembly.

These lemmas prove the scalar, triangle-inequality, and event bookkeeping
steps. They do not assert the probabilistic small-coordinate or sparse
estimates, and they do not redefine the supplied `mixedNorm`.
-/

noncomputable section

namespace GaussianEllipsoidFinalPassage

/-- Cancellation leaves the head gain minus the controlled tail. -/
theorem small_tail_scalar
    {M t beta cH L H T R : ℝ}
    (hcH : 0 ≤ cH) (hL : 0 ≤ L)
    (ht : t ≤ beta * M)
    (hhead : cH * (M - t) ≤ H)
    (htail : T ≤ L * t)
    (htriangle : H - T ≤ R) :
    (cH * (1 - beta) - L * beta) * M ≤ R := by
  have h1 := mul_le_mul_of_nonneg_left ht hcH
  have h2 := mul_le_mul_of_nonneg_left ht hL
  nlinarith

/-- The preceding scalar cancellation lemma applied to an ordinary norm.
To use this with the nuclear norm, instantiate its normed-space realization,
or use `small_tail_scalar` with the nuclear-norm triangle inequality. -/
theorem small_tail_norm {E : Type*} [NormedAddCommGroup E]
    {M t beta cH L : ℝ} {U V : E}
    (hcH : 0 ≤ cH) (hL : 0 ≤ L)
    (ht : t ≤ beta * M)
    (hhead : cH * (M - t) ≤ ‖U‖)
    (htail : ‖V‖ ≤ L * t) :
    (cH * (1 - beta) - L * beta) * M ≤ ‖U + V‖ := by
  have htriangle : ‖U‖ - ‖V‖ ≤ ‖U + V‖ := by
    have h := norm_add_le (U + V) (-V)
    simp only [add_neg_cancel_right, norm_neg] at h
    linarith
  exact small_tail_scalar hcH hL ht hhead htail htriangle

/-- A two-branch lower bound combines by taking the minimum coefficient. -/
theorem combine_branches
    {M t beta cS cHead R : ℝ} (hM : 0 ≤ M)
    (hlargeTail : beta * M ≤ t → cS * M ≤ R)
    (hsmallTail : t < beta * M → cHead * M ≤ R) :
    min cS cHead * M ≤ R := by
  by_cases h : beta * M ≤ t
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hM).trans
      (hlargeTail h)
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hM).trans
      (hsmallTail (lt_of_not_ge h))

/-- An explicit margin for the choice beta = 2 eta.
`Dlog` will be `1 + 2 * log (1 / eta)`. -/
theorem explicit_absorption
    {eta mu L Dlog cH : ℝ}
    (hmu : 0 < mu) (hD : 0 < Dlog)
    (heta : eta ≤ 1 / 16)
    (hhead : mu ≤ cH * Dlog)
    (herror : 2 * L * eta * Dlog ≤ 3 * mu / 32) :
    mu / (2 * Dlog) ≤ cH * (1 - 2 * eta) - 2 * L * eta := by
  have hfactor : 0 ≤ 1 - 2 * eta := by linarith
  have h1 := mul_le_mul_of_nonneg_right hhead hfactor
  have h2 := mul_le_mul_of_nonneg_right heta (le_of_lt hmu)
  apply (div_le_iff₀ (mul_pos (by norm_num) hD)).2
  nlinarith

/-- The chosen eta is positive, smaller than one, and at most 1/16. -/
theorem explicit_eta_range {mu L : ℝ} (hmu : 0 < mu) (hL : 0 ≤ L) :
    let eta := min (1 / 16 : ℝ) ((mu / (64 * (L + 1))) ^ 2)
    0 < eta ∧ eta < 1 ∧ eta ≤ 1 / 16 := by
  dsimp
  have hq : 0 < mu / (64 * (L + 1)) := by positivity
  have hp : 0 < (mu / (64 * (L + 1))) ^ 2 := sq_pos_of_pos hq
  have hmin : min (1 / 16 : ℝ) ((mu / (64 * (L + 1))) ^ 2) ≤ 1 / 16 :=
    min_le_left _ _
  exact ⟨lt_min (by norm_num) hp, lt_of_le_of_lt hmin (by norm_num), hmin⟩

/-- A finite exceptional prefix is removed rather than left implicit. -/
def goodAfter {X : ℕ → Type*} (D : ℕ) (G : ∀ d, Set (X d))
    (d : ℕ) : Set (X d) :=
  if D ≤ d then G d else ∅

theorem goodAfter_eventually_eq {X : ℕ → Type*}
    (D : ℕ) (G : ∀ d, Set (X d)) :
    ∀ᶠ d in Filter.atTop, goodAfter D G d = G d := by
  filter_upwards [Filter.eventually_ge_atTop D] with d hd
  simp [goodAfter, hd]

theorem goodAfter_property {X : ℕ → Type*}
    (D : ℕ) (G : ∀ d, Set (X d)) (P : ∀ d, X d → Prop)
    (h : ∀ d, D ≤ d → ∀ x ∈ G d, P d x) :
    ∀ d, ∀ x ∈ goodAfter D G d, P d x := by
  intro d x hx
  by_cases hd : D ≤ d
  · exact h d hd x (by simpa [goodAfter, hd] using hx)
  · simp [goodAfter, hd] at hx

/-- The localized bad event is paid only on the continuity event. -/
theorem bad_intersection_subset {X : Type*} (E H F : Set X) :
    (E ∩ H ∩ Fᶜ)ᶜ ⊆ (Eᶜ ∪ Hᶜ) ∪ (F ∩ E) := by
  intro x hx
  by_cases he : x ∈ E
  · by_cases hh : x ∈ H
    · have hf : x ∈ F := by
        by_contra hnf
        exact hx ⟨⟨he, hh⟩, hnf⟩
      exact Or.inr ⟨hf, he⟩
    · exact Or.inl (Or.inr hh)
  · exact Or.inl (Or.inl he)

open MeasureTheory

/-- This union bound does not require measurability of the three sets. -/
theorem bad_intersection_measure {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (E H F : Set X) :
    mu (E ∩ H ∩ Fᶜ)ᶜ ≤ mu Eᶜ + mu Hᶜ + mu (F ∩ E) := by
  calc
    mu (E ∩ H ∩ Fᶜ)ᶜ ≤ mu ((Eᶜ ∪ Hᶜ) ∪ (F ∩ E)) :=
      measure_mono (bad_intersection_subset E H F)
    _ ≤ mu (Eᶜ ∪ Hᶜ) + mu (F ∩ E) := measure_union_le _ _
    _ ≤ mu Eᶜ + mu Hᶜ + mu (F ∩ E) :=
      add_le_add (measure_union_le Eᶜ Hᶜ) le_rfl

end GaussianEllipsoidFinalPassage
