import Section_10_Zonoid.Hypercube.Statements
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Exact weighted-to-probability algebra from Section 1.1. This file proves
normalization and endpoint equivalences, not the geometric inequality.
-/

noncomputable section

namespace Hypercube.CubeNormalization

open Paper

theorem totalWeight_scaled {d : Nat} (x : Cube d -> Real) (c : Real) :
    totalWeight (fun v => c * x v) = c * totalWeight x := by
  simp only [totalWeight, Finset.mul_sum]

theorem facetWeight_scaled {d : Nat} (x : Cube d -> Real) (c : Real)
    (j : Fin d) (b : Bool) :
    facetWeight (fun v => c * x v) j b = c * facetWeight x j b := by
  simp only [facetWeight, Finset.mul_sum]

theorem cubeSimplexSum_scaled {d : Nat} (x : Cube d -> Real) (c : Real) :
    cubeSimplexSum (fun v => c * x v) = c ^ (d + 1) * cubeSimplexSum x := by
  unfold cubeSimplexSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard := (Finset.mem_powersetCard.mp hs).2
  rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  ring

theorem facet_product_scaled {d : Nat} (x : Cube d -> Real) (c : Real) :
    Finset.prod Finset.univ (fun j =>
      facetWeight (fun v => c * x v) j false * facetWeight (fun v => c * x v) j true) =
      c ^ (2 * d) * Finset.prod Finset.univ
        (fun j => facetWeight x j false * facetWeight x j true) := by
  simp only [facetWeight_scaled]
  have heq (j : Fin d) :
      c * facetWeight x j false * (c * facetWeight x j true) =
        c ^ 2 * (facetWeight x j false * facetWeight x j true) := by ring
  simp_rw [heq]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin, <- pow_mul]

theorem weightedCube_scaled_iff {d : Nat} (hd : 1 <= d)
    (x : Cube d -> Real) (c : Real) (hc : 0 < c) :
    weightedCubeClaim d (fun v => c * x v) <-> weightedCubeClaim d x := by
  unfold weightedCubeClaim
  rw [cubeSimplexSum_scaled, totalWeight_scaled, facet_product_scaled, mul_pow]
  have hexp : d + 1 + (d - 1) = 2 * d := by omega
  have hlhs : c ^ (d + 1) * cubeSimplexSum x * (c ^ (d - 1) * totalWeight x ^ (d - 1)) =
      c ^ (2 * d) * (cubeSimplexSum x * totalWeight x ^ (d - 1)) := by
    rw [<- hexp, pow_add]
    ring
  rw [hlhs]
  constructor
  case mp => exact fun h => le_of_mul_le_mul_left h (pow_pos hc _)
  case mpr => exact fun h => mul_le_mul_of_nonneg_left h (le_of_lt (pow_pos hc _))

theorem facets_split_total {d : Nat} (x : Cube d -> Real) (j : Fin d) :
    facetWeight x j false + facetWeight x j true = totalWeight x := by
  unfold facetWeight totalWeight
  rw [Finset.sum_filter, Finset.sum_filter, <- Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  cases v j
  all_goals simp

theorem totalWeight_nonneg {d : Nat} (x : Cube d -> Real)
    (hx : forall v, 0 <= x v) : 0 <= totalWeight x :=
  Finset.sum_nonneg (fun v _ => hx v)

theorem zero_total_forces_zero_weights {d : Nat} (x : Cube d -> Real)
    (hx : forall v, 0 <= x v) (hQ : totalWeight x = 0) : forall v, x v = 0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hx v)).mp hQ
  exact fun v => h v (Finset.mem_univ v)

theorem cubeSimplexSum_zero (d : Nat) : cubeSimplexSum (fun _ : Cube d => 0) = 0 := by
  unfold cubeSimplexSum
  apply Finset.sum_eq_zero
  intro s hs
  have hcard := (Finset.mem_powersetCard.mp hs).2
  simp [Finset.prod_const, hcard]

theorem weightedCube_zero_total {d : Nat} (x : Cube d -> Real)
    (hx : forall v, 0 <= x v) (hQ : totalWeight x = 0) : weightedCubeClaim d x := by
  have hzero := zero_total_forces_zero_weights x hx hQ
  have heq : x = (fun _ : Cube d => 0) := funext hzero
  rw [heq]
  unfold weightedCubeClaim
  rw [cubeSimplexSum_zero, zero_mul]
  apply Finset.prod_nonneg
  intro j _
  simp [facetWeight]

theorem normalized_total {d : Nat} (x : Cube d -> Real) (hQ : 0 < totalWeight x) :
    totalWeight (fun v => x v / totalWeight x) = 1 := by
  unfold totalWeight
  rw [<- Finset.sum_div]
  exact div_self (ne_of_gt hQ)

theorem normalized_nonneg {d : Nat} (x : Cube d -> Real)
    (hx : forall v, 0 <= x v) (hQ : 0 < totalWeight x) :
    forall v, 0 <= x v / totalWeight x :=
  fun v => div_nonneg (hx v) (le_of_lt hQ)

theorem normalization_equivalence {d : Nat} (hd : 1 <= d)
    (x : Cube d -> Real) (hQ : 0 < totalWeight x) :
    weightedCubeClaim d (fun v => x v / totalWeight x) <-> weightedCubeClaim d x := by
  have hscaled := weightedCube_scaled_iff hd x (Inv.inv (totalWeight x)) (inv_pos.mpr hQ)
  simpa only [div_eq_mul_inv, mul_comm] using hscaled

theorem probability_form_equivalence {d : Nat} (q : Cube d -> Real)
    (hqsum : totalWeight q = 1) :
    weightedCubeClaim d q <->
      cubeSimplexSum q <= Finset.prod Finset.univ
        (fun j => facetWeight q j true * (1 - facetWeight q j true)) := by
  have hfacet (j : Fin d) : facetWeight q j false = 1 - facetWeight q j true := by
    have h := facets_split_total q j
    rw [hqsum] at h
    linarith
  unfold weightedCubeClaim
  rw [hqsum]
  simp only [one_pow, one_mul, hfacet, mul_comm]

end Hypercube.CubeNormalization
