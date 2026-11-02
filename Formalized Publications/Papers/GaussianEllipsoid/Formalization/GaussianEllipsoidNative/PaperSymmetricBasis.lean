import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-! Reconstructed basis support. `PaperSymmetricDirections` is a transitive
missing namespace, not a claimed recovered original module. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace PaperSymmetricDirections
variable {d : ℕ}

def frobInner (A B : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def Q (a b : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if a = b then (if i = a ∧ j = a then 1 else 0)
  else (if i = a ∧ j = b then 1 / Real.sqrt 2 else 0) +
    (if i = b ∧ j = a then 1 / Real.sqrt 2 else 0)

end PaperSymmetricDirections
namespace PaperSymmetricBasis
open PaperSymmetricDirections
variable {d : ℕ}

theorem Q_transpose (a b : Fin d) : (Q a b).transpose = Q a b := by
  ext i j
  by_cases hab : a = b <;> simp [Q, hab, Matrix.transpose_apply, and_comm, add_comm]

lemma frobInner_Q (A : Matrix (Fin d) (Fin d) ℝ) (a b : Fin d) :
    frobInner A (Q a b) =
      if a = b then A a a else (A a b + A b a) / Real.sqrt 2 := by
  by_cases hab : a = b
  · simp [frobInner, Q, hab, mul_ite, ite_and]
  · simp only [frobInner, Q, if_neg hab, mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_zero, ite_and]
    simp [Finset.sum_ite_irrel, add_div, div_eq_mul_inv]
    ring

theorem Q_gram (a b c e : Fin d) (hab : a ≤ b) (hce : c ≤ e) :
    frobInner (Q a b) (Q c e) = if a = c ∧ b = e then 1 else 0 := by
  rw [frobInner_Q]
  have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  by_cases heq : c = e
  · subst e
    by_cases hab' : a = b
    · subst b
      simp [Q, eq_comm, and_self]
    · have hnot : ¬ (c = a ∧ c = b) := by rintro ⟨rfl, h⟩; exact hab' h
      have hnot' : ¬ (a = c ∧ b = c) := by tauto
      simp [Q, hab', hnot, hnot', and_comm, eq_comm]
  · rw [if_neg heq]
    by_cases hab' : a = b
    · subst b
      have hnot : ¬ (c = a ∧ e = a) := by rintro ⟨rfl, rfl⟩; exact heq rfl
      have hnot' : ¬ (a = c ∧ a = e) := by tauto
      simp [Q, hnot, hnot', and_comm, eq_comm]
    · have hswap : ¬ (c = b ∧ e = a) := by
        rintro ⟨rfl, rfl⟩
        exact hab' (le_antisymm hab hce)
      simp only [Q, if_neg hab']
      simp only [hswap, if_false]
      by_cases hmatch : a = c ∧ b = e
      · rcases hmatch with ⟨rfl, rfl⟩
        simp only [true_and, and_true, if_true, eq_self, if_false,
          show ¬ (b = a ∧ a = b) by tauto]
        field_simp
        nlinarith
      · have hmatch' : ¬ (c = a ∧ e = b) := by tauto
        simp [hmatch, hmatch', and_comm]
        tauto

lemma coefficient_entry (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose=A)
    (a b i j : Fin d) :
    frobInner A (Q a b) * Q a b i j =
      if a=b then (if i=a ∧ j=a then A i j else 0)
      else (if i=a ∧ j=b then A i j else 0) + (if i=b ∧ j=a then A i j else 0) := by
  have hsym (k l : Fin d) : A l k=A k l := congrFun (congrFun hA k) l
  have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
  rw [frobInner_Q]
  by_cases hab : a=b
  · subst b
    simp only [Q, ite_true, mul_ite, mul_one, mul_zero]
    split_ifs <;> simp_all
  · simp only [Q, if_neg hab, mul_add, mul_ite, mul_zero]
    have hm : (A a b + A b a) / Real.sqrt 2 * (1 / Real.sqrt 2) = A a b := by
      rw [hsym, div_mul_div_comm, ← pow_two, hs]
      ring
    rw [hm]
    split_ifs <;> simp_all [hsym]

theorem Q_expansion (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.transpose = A) :
    A = ∑ a : Fin d, ∑ b : Fin d,
      if a ≤ b then frobInner A (Q a b) • Q a b else 0 := by
  ext i j
  simp only [Matrix.sum_apply]
  change A i j = ∑ a : Fin d, ∑ b : Fin d,
    (if a ≤ b then frobInner A (Q a b) • Q a b else 0) i j
  simp only [apply_ite (fun M : Matrix (Fin d) (Fin d) ℝ => M i j), Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul,
    coefficient_entry A hA]
  clear hA
  generalize A i j = z
  clear A
  have he (a b : Fin d) :
      (if a ≤ b then
        (if a=b then (if i=a ∧ j=a then z else 0)
        else (if i=a ∧ j=b then z else 0) + (if i=b ∧ j=a then z else 0))
        else 0) = if a=min i j ∧ b=max i j then z else 0 := by
    by_cases hij : i ≤ j
    · simp only [min_eq_left hij, max_eq_right hij]
      split_ifs <;> (try ring) <;> exfalso <;> omega
    · have hji : j ≤ i := le_of_not_ge hij
      simp only [min_eq_right hji, max_eq_left hji]
      split_ifs <;> (try ring) <;> exfalso <;> omega
  simp_rw [he]
  simp [ite_and]

#print axioms Q_transpose
#print axioms Q_gram
#print axioms Q_expansion
end PaperSymmetricBasis
