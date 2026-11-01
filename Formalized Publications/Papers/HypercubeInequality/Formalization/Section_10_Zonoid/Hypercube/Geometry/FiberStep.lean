import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
The finite minimum-ratio step in the source barycentric-fiber argument.
It uses no geometric positivity assumption and no signed-cocycle premise.
-/

namespace Hypercube.FiberStep

theorem exists_forward_boundary {Index : Type*} [Fintype Index] [DecidableEq Index]
    (a c : Index -> Real) (i : Index)
    (hsum : Finset.sum Finset.univ c = 0) (hci : 0 < c i)
    (hai : a i = 0) (ha : forall k, Not (k = i) -> 0 < a k) :
    Exists (fun t : Real => Exists (fun j : Index =>
      And (0 < t) (And (c j < 0)
        (And (a j + t * c j = 0)
          (And (0 < a i + t * c i) (forall k, 0 <= a k + t * c k)))))) := by
  classical
  have hneg : Exists (fun j => c j < 0) := by
    by_contra hn
    have hc : forall j, 0 <= c j := by
      intro j
      apply le_of_not_gt
      intro hj
      exact hn (Exists.intro j hj)
    have hsingle := Finset.single_le_sum (fun j _ => hc j) (Finset.mem_univ i)
    rw [hsum] at hsingle
    linarith
  let S := Finset.univ.filter (fun j => c j < 0)
  have hS : S.Nonempty := by
    cases hneg with
    | intro j hj =>
      exact Exists.intro j (Finset.mem_filter.mpr (And.intro (Finset.mem_univ j) hj))
  obtain hmin := Finset.exists_min_image S (fun j => a j / (-c j)) hS
  cases hmin with
  | intro j hj =>
    have hcj : c j < 0 := (Finset.mem_filter.mp hj.1).2
    have hji : Not (j = i) := by
      intro h
      subst j
      linarith
    have haj : 0 < a j := ha j hji
    let t := a j / (-c j)
    have ht : 0 < t := div_pos haj (by linarith)
    have hcancel : t * (-c j) = a j := by
      have hcn : Not (c j = 0) := by linarith
      dsimp [t]
      field_simp [hcn]
    have hz : a j + t * c j = 0 := by nlinarith
    have hi : 0 < a i + t * c i := by
      rw [hai, zero_add]
      exact mul_pos ht hci
    refine Exists.intro t (Exists.intro j
      (And.intro ht (And.intro hcj (And.intro hz (And.intro hi ?_)))))
    intro k
    by_cases hck : c k < 0
    case pos =>
      have hkS : Membership.mem S k :=
        Finset.mem_filter.mpr (And.intro (Finset.mem_univ k) hck)
      have hratio : t <= a k / (-c k) := hj.2 k hkS
      have hkn : Not (c k = 0) := by linarith
      have hcancelk : (a k / (-c k)) * (-c k) = a k := by field_simp [hkn]
      have hmul := mul_le_mul_of_nonneg_right hratio (show 0 <= -c k by linarith)
      rw [hcancelk] at hmul
      nlinarith
    case neg =>
      have hak : 0 <= a k := by
        by_cases hki : k = i
        case pos => simp [hki, hai]
        case neg => exact le_of_lt (ha k hki)
      exact add_nonneg hak (mul_nonneg (le_of_lt ht) (le_of_not_gt hck))

end Hypercube.FiberStep
