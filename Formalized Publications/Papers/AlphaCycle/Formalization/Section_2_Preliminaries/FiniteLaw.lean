import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite probability laws, with real cell masses. All probability identities in this
file are finite sums; no measure-theoretic completion is involved. -/
namespace AlphaCycle

open Classical

/-- A probability law on a finite sample space. -/
@[ext] structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Law
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The probability of a finite event. -/
noncomputable def prob (μ : Law α) (p : α → Prop) : ℝ :=
  ∑ a, if p a then μ.mass a else 0

 theorem prob_nonneg (μ : Law α) (p : α → Prop) : 0 ≤ μ.prob p := by
  classical
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [μ.nonneg]

@[simp] theorem prob_true (μ : Law α) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.total]

@[simp] theorem prob_false (μ : Law α) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

 theorem prob_congr (μ : Law α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    μ.prob p = μ.prob q := by
  classical
  simp only [prob, h]

 theorem prob_mono (μ : Law α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    μ.prob p ≤ μ.prob q := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases hp : p a
  · simp [hp, h a hp]
  · simp only [hp, ↓reduceIte]
    split_ifs <;> simp [μ.nonneg]

 theorem prob_le_one (μ : Law α) (p : α → Prop) : μ.prob p ≤ 1 := by
  simpa using μ.prob_mono (p := p) (q := fun _ => True) (fun _ _ => trivial)

 theorem mass_le_prob (μ : Law α) (p : α → Prop) (a : α) (ha : p a) :
    μ.mass a ≤ μ.prob p := by
  classical
  calc
    μ.mass a = (if p a then μ.mass a else 0) := by simp [ha]
    _ ≤ ∑ b, if p b then μ.mass b else 0 := by
      apply Finset.single_le_sum (f := fun b => if p b then μ.mass b else 0)
      · intro b _
        split_ifs <;> simp [μ.nonneg]
      · exact Finset.mem_univ a

 theorem mass_le_one (μ : Law α) (a : α) : μ.mass a ≤ 1 := by
  exact (μ.mass_le_prob (fun _ => True) a trivial).trans (μ.prob_le_one _)

 theorem prob_eq_zero_iff (μ : Law α) (p : α → Prop) :
    μ.prob p = 0 ↔ ∀ a, p a → μ.mass a = 0 := by
  classical
  rw [prob, Finset.sum_eq_zero_iff_of_nonneg]
  · simp only [Finset.mem_univ, forall_const]
    constructor
    · intro h a ha
      simpa [ha] using h a
    · intro h a
      split_ifs with ha
      · exact h a ha
      · rfl
  · intro a _
    split_ifs <;> simp [μ.nonneg]

 theorem prob_compl (μ : Law α) (p : α → Prop) :
    μ.prob (fun a => ¬ p a) = 1 - μ.prob p := by
  classical
  have : μ.prob (fun a => ¬ p a) + μ.prob p = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib]
    convert μ.total using 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : p a <;> simp [h]
  linarith

 theorem prob_eq_one_iff (μ : Law α) (p : α → Prop) :
    μ.prob p = 1 ↔ ∀ a, ¬ p a → μ.mass a = 0 := by
  rw [← μ.prob_eq_zero_iff (fun a => ¬ p a), μ.prob_compl]
  constructor <;> intro h <;> linarith

/-- Push a finite law forward along a function; marginalization is a special case. -/
noncomputable def map (f : α → β) (μ : Law α) : Law β where
  mass b := ∑ a, if f a = b then μ.mass a else 0
  nonneg b := Finset.sum_nonneg fun a _ => by split_ifs <;> simp [μ.nonneg]
  total := by
    classical
    rw [Finset.sum_comm]
    simpa using μ.total

@[simp] theorem map_mass (f : α → β) (μ : Law α) (b : β) :
    (μ.map f).mass b = μ.prob (fun a => f a = b) := rfl

 theorem mass_le_map_mass (f : α → β) (μ : Law α) (a : α) :
    μ.mass a ≤ (μ.map f).mass (f a) :=
  μ.mass_le_prob (fun b => f b = f a) a rfl

 theorem prob_map (f : α → β) (μ : Law α) (p : β → Prop) :
    (μ.map f).prob p = μ.prob (fun a => p (f a)) := by
  classical
  simp only [prob, map]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (f a)]
  · simp
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

@[simp] theorem map_id (μ : Law α) : μ.map id = μ := by
  classical
  ext a
  simp [map]

@[simp] theorem map_map (f : α → β) (g : β → γ) (μ : Law α) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  ext c
  simp only [map_mass, prob_map, Function.comp_apply]

/-- A deterministic law. -/
noncomputable def dirac (a : α) : Law α where
  mass b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  total := by
    classical
    simp

@[simp] theorem prob_dirac (a : α) (p : α → Prop) :
    (dirac a).prob p = if p a then 1 else 0 := by
  classical
  rw [prob, Finset.sum_eq_single a]
  · simp [dirac]
  · intro b _ hba
    simp [dirac, hba]
  · simp

end Law
end AlphaCycle
