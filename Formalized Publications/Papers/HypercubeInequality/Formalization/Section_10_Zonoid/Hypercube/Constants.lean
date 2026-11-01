import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Arithmetic interfaces only. No geometric or probabilistic premise is hidden here. -/

noncomputable section

namespace Hypercube.Constants

def mainCoefficient (d : Nat) : Real := ((d + 1 : Nat) : Real) / (2 : Real) ^ d

def oneStepCoefficient (d : Nat) : Real := ((d + 1 : Nat) : Real) / (2 * (d : Real))

theorem mainCoefficient_one : mainCoefficient 1 = 1 := by
  norm_num [mainCoefficient]

theorem mainCoefficient_succ (d : Nat) :
    mainCoefficient (d + 1) =
      oneStepCoefficient (d + 1) * mainCoefficient d := by
  simp only [mainCoefficient, oneStepCoefficient, Nat.cast_add, Nat.cast_one,
    pow_succ]
  field_simp

/-- The paper's product from k=2 to d, represented by a range of d-1 terms. -/
def iterationCoefficient (d : Nat) : Real :=
  (Finset.range (d - 1)).prod (fun j => oneStepCoefficient (j + 2))

theorem iterationCoefficient_succ (d : Nat) (hd : 1 <= d) :
    iterationCoefficient (d + 1) =
      iterationCoefficient d * oneStepCoefficient (d + 1) := by
  have hsub : d + 1 - 1 = (d - 1) + 1 := by omega
  have hindex : d - 1 + 2 = d + 1 := by omega
  simp only [iterationCoefficient, hsub, Finset.prod_range_succ, hindex]

theorem iterationCoefficient_eq_mainCoefficient (d : Nat) (hd : 1 <= d) :
    iterationCoefficient d = mainCoefficient d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [iterationCoefficient, mainCoefficient]
  | succ d hd ih =>
    rw [iterationCoefficient_succ d hd, mainCoefficient_succ d, ih]
    ring

/-- The coefficient conversion n! L <= 2p(1-p) (n!/2) D. -/
theorem bernoulli_normalization (F L D p : Real)
    (hF : 0 <= F) (hLD : L <= p * (1 - p) * D) :
    F * L <= 2 * p * (1 - p) * (F / 2 * D) := by
  have h := mul_le_mul_of_nonneg_left hLD hF
  nlinarith

end Hypercube.Constants
