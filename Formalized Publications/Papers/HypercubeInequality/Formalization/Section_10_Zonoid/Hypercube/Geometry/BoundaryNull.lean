import Section_10_Zonoid.Hypercube.Geometry.NullFaces
import Section_10_Zonoid.Hypercube.Geometry.Cocycle
import Mathlib.Data.Fintype.Sum

/-!
The union of codimension-one faces removed in the cocycle argument is null.
The complement of two sample labels contains exactly m labels, even when
their projected locations coincide.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.Geometry.Cocycle

theorem pairHull_volume_zero {m : Nat} (hm : 0 < m)
    (w : Fin (m + 2) -> Geometry.Point m) (i j : Fin (m + 2))
    (hij : Not (i = j)) : volume (pairHull w i j) = 0 := by
  classical
  let K := Subtype (fun k : Fin (m + 2) => And (Not (k = i)) (Not (k = j)))
  have hcard : Fintype.card K = m := by
    let e : Equiv K
        (Subtype (fun k : Fin (m + 2) => Not (Or (k = i) (k = j)))) :=
      Equiv.subtypeEquivRight (fun k => not_or.symm)
    calc
      Fintype.card K =
          Fintype.card (Subtype (fun k : Fin (m + 2) => Not (Or (k = i) (k = j)))) :=
        Fintype.card_congr e
      _ = (m + 2) - 2 := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin,
          Fintype.card_subtype_eq_or_eq_of_ne hij]
      _ = m := by omega
  let e : Equiv (Fin m) K := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, hcard])
  let v : Fin m -> Geometry.Point m := fun r => w (e r).val
  have hrange : Set.range v = w '' Set.ofPred
      (fun k : Fin (m + 2) => And (Not (k = i)) (Not (k = j))) := by
    ext x
    constructor
    next =>
      intro hx
      cases hx with
      | intro r hr =>
          exact Exists.intro (e r).val (And.intro (e r).property hr)
    next =>
      intro hx
      cases hx with
      | intro k hk =>
          cases hk with
          | intro hmem hkx =>
              refine Exists.intro (e.symm (Subtype.mk k hmem)) ?_
              simpa only [v, Equiv.apply_symm_apply] using hkx
  unfold pairHull
  rw [<- hrange]
  exact Geometry.volume_finite_hull_zero hm v

theorem signedCocycleSum_dimension_zero
    (w : Fin 2 -> Geometry.Point 0) (x : Geometry.Point 0) :
    signedCocycleSum w x = 0 := by
  have hw : forall i : Fin 2, omitted w i = omitted w 0 := by
    intro i
    funext r j
    exact Fin.elim0 j
  unfold signedCocycleSum
  simp only [hw]
  rw [<- Finset.sum_mul]
  norm_num [Fin.sum_univ_succ]

theorem ae_avoids_pairHull {m : Nat} (hm : 0 < m)
    (w : Fin (m + 2) -> Geometry.Point m) :
    Filter.Eventually
      (fun x => forall i j, Not (i = j) -> Not (Membership.mem (pairHull w i j) x))
      (ae volume) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  next =>
    exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hij))
  next =>
    have h := measure_eq_zero_iff_ae_notMem.mp (pairHull_volume_zero hm w i j hij)
    exact h.mono (fun _ hx _ => hx)

/-- The exact signed-simplex cocycle, including degeneracies and repeats. -/
theorem signed_simplex_cocycle_ae {m : Nat}
    (w : Fin (m + 2) -> Geometry.Point m) :
    Filter.Eventually (fun x => signedCocycleSum w x = 0) (ae volume) := by
  by_cases hm : 0 < m
  next =>
    exact (ae_avoids_pairHull hm w).mono
      (fun x hx => signedCocycleSum_outside_pairHulls w x hx)
  next =>
    have hm0 : m = 0 := by omega
    subst m
    exact Filter.Eventually.of_forall (signedCocycleSum_dimension_zero w)

end Hypercube.Geometry.Cocycle
