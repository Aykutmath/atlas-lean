module

/-
# Corollary 10.1: reduction of the zonoid projection inequality

The geometric content of Corollary 10.1 is the pair of determinant
volume identities for the lifted zonotope `Kν` of a finite law `ν`:

* `vol_{d+1}(Kν) = S_d(ν) / (d + 1)`,
* `vol_1(P_L Kν) = 1`,
* `vol_2(P_{E_j} Kν) = D_j(ν) / 2`,

together with the extension from zonotopes to all zonoids by
Hausdorff approximation (including horizontal generators) and the
optimality of the constant `1` from boxes.

This module formalizes, kernel-checked, everything that follows
once those geometric identities are available:

* `zonoid_projection_of_identities`: for any quantities `A, B, E_j`
  satisfying the three identities above (in `ℝ≥0∞` form), the
  projection inequality `A * B^m ≤ ∏ E_j` follows from `main_full`
  with exact constant `1`;
* `zonoid_box_equality`: coordinate boxes give equality, which is
  the optimality half of Corollary 10.1 at the level of the
  volume identities.

What remains open (recorded as HI-ZONOID, UNRESOLVED): constructing
`Kν` as a Minkowski sum of segments in Lean, proving the three
zonotope determinant-volume identities, orienting arbitrary
zonotope generators, perturbing horizontal generators, and the
Hausdorff-limit extension with continuity of volume and of
projected volumes.  No faithful Lean statement of Corollary 10.1
itself is claimed yet.
-/

public import Section_7_Approximation.Approx

namespace HypercubeInequality

open MeasureTheory Measure Finset
open scoped ENNReal NNReal BigOperators Nat

/-- Projection inequality from the zonotope volume identities:
if `(m+2) * A = S_{m+1}(ν)`, `B = 1`, and `2 * E_j = D_j(ν)`,
then `A * B^m ≤ ∏ E_j` with constant `1`. -/
public theorem zonoid_projection_of_identities {m : ℕ}
    (ν : Measure (EuclideanSpace ℝ (Fin (m + 1)))) [IsProbabilityMeasure ν]
    (A B : ℝ≥0∞) (E : Fin (m + 1) → ℝ≥0∞)
    (hA : ((m + 2 : ℕ) : ℝ≥0∞) * A = S (m + 1) ν)
    (hB : B = 1)
    (hE : ∀ j, (2 : ℝ≥0∞) * E j = gap j ν) :
    A * B ^ m ≤ ∏ j, E j := by
  have hmain := main_full m ν
  have hprod : ∏ j, gap j ν = (2 : ℝ≥0∞) ^ (m + 1) * ∏ j, E j := by
    rw [Finset.prod_congr rfl (fun j _ => (hE j).symm : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
        gap j ν = (2 : ℝ≥0∞) * E j), Finset.prod_mul_distrib]
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hcoef : ENNReal.ofReal ((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1))
        * ((2 : ℝ≥0∞) ^ (m + 1)) = ((m + 2 : ℕ) : ℝ≥0∞) := by
    have h2 : ((2 : ℝ≥0∞) ^ (m + 1)) = ENNReal.ofReal ((2 : ℝ) ^ (m + 1)) := by
      have hbase : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
        norm_num [ENNReal.ofReal_ofNat]
      rw [← hbase, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
    congr 1
    field_simp
  have hstep : ((m + 2 : ℕ) : ℝ≥0∞) * A ≤ ((m + 2 : ℕ) : ℝ≥0∞) * ∏ j, E j := by
    rw [hA]
    calc S (m + 1) ν
        ≤ ENNReal.ofReal ((((m + 2 : ℕ)) : ℝ) / 2 ^ (m + 1)) * ∏ j, gap j ν :=
          hmain
      _ = ((m + 2 : ℕ) : ℝ≥0∞) * ∏ j, E j := by
          rw [hprod, ← mul_assoc, hcoef]
  have hfin : A ≤ ∏ j, E j := by
    have h0 : (((m + 2 : ℕ)) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (m + 1)
    have ht : (((m + 2 : ℕ)) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    have hA' : A = ((m + 2 : ℕ) : ℝ≥0∞) * A / ((m + 2 : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.eq_div_iff h0 ht, mul_comm]
    have hP' : (∏ j, E j)
        = ((m + 2 : ℕ) : ℝ≥0∞) * (∏ j, E j) / ((m + 2 : ℕ) : ℝ≥0∞) := by
      rw [ENNReal.eq_div_iff h0 ht, mul_comm]
    rw [hA', hP']
    exact ENNReal.div_le_div_right hstep _
  rw [hB, one_pow, mul_one]
  exact hfin

/-- Boxes give equality in the projection inequality: with
`vol_{d+1} = h * ∏ a_j`, `vol_1 = h`, `vol_2^{(j)} = a_j * h`,
both sides agree.  This is the optimality of the constant `1`. -/
public theorem zonoid_box_equality {m : ℕ} (a : Fin (m + 1) → ℝ) (h : ℝ) :
    (h * ∏ j, a j) * h ^ m = ∏ j, (a j * h) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

end HypercubeInequality
