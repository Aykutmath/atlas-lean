import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
The scalar normalization in the proof of Corollary 10.1.

This module proves only the algebraic step. The hypotheses identifying actual
geometric volumes must be proved separately; they are not axioms or definitions
of volume. All quantities here are real numbers, and no finiteness assertion
about geometric measures is hidden in this lemma.
-/

noncomputable section

namespace Cor101

/-- Cancellation of the simplex normalization `(d+1)` in the sharp bound. -/
theorem normalized_simplex_bound (d : Nat) (S : Real) (D : Fin d -> Real)
    (h : S <= ((d + 1 : Nat) : Real) / (2 : Real) ^ d *
      Finset.prod Finset.univ D) :
    S / ((d + 1 : Nat) : Real) <=
      Finset.prod Finset.univ (fun j => D j / 2) := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  apply (div_le_iff₀ (by positivity : (0 : Real) < ((d + 1 : Nat) : Real))).2
  calc
    S <= ((d + 1 : Nat) : Real) / (2 : Real) ^ d *
        Finset.prod Finset.univ D := h
    _ = (Finset.prod Finset.univ D / (2 : Real) ^ d) *
        ((d + 1 : Nat) : Real) := by ring

/-- The homogeneous scaling step, valid at zero scale as well. -/
theorem homogeneous_projection_bound (d : Nat) (hd : 1 <= d)
    (H V : Real) (A : Fin d -> Real) (hH : 0 <= H)
    (h : V <= Finset.prod Finset.univ A) :
    (H ^ (d + 1) * V) * H ^ (d - 1) <=
      Finset.prod Finset.univ (fun j => H ^ 2 * A j) := by
  have hexp : d + 1 + (d - 1) = 2 * d := by omega
  have hleft : (H ^ (d + 1) * V) * H ^ (d - 1) = H ^ (2 * d) * V := by
    calc
      _ = (H ^ (d + 1) * H ^ (d - 1)) * V := by ring
      _ = H ^ (2 * d) * V := by rw [<- pow_add, hexp]
  rw [hleft, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [<- pow_mul]
  exact mul_le_mul_of_nonneg_left h (pow_nonneg hH _)

/--
The complete numerical step in the paper's normalized-zonotope argument.
The three displayed normalization identities are explicit hypotheses.
This is not the all-zonoid endpoint theorem.
-/
theorem projection_bound_of_normalization (d : Nat) (hd : 1 <= d)
    (H S V L : Real) (D A : Fin d -> Real) (hH : 0 <= H)
    (hS : S <= ((d + 1 : Nat) : Real) / (2 : Real) ^ d *
      Finset.prod Finset.univ D)
    (hV : V = H ^ (d + 1) * (S / ((d + 1 : Nat) : Real)))
    (hL : L = H)
    (hA : forall j, A j = H ^ 2 * (D j / 2)) :
    V * L ^ (d - 1) <= Finset.prod Finset.univ A := by
  rw [hV, hL]
  have hfun : A = fun j => H ^ 2 * (D j / 2) := funext hA
  rw [hfun]
  exact homogeneous_projection_bound d hd H _ _ hH
    (normalized_simplex_bound d S D hS)

end Cor101
