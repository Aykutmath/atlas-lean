import Section_10_Zonoid.Hypercube.Geometry.Cocycle
import Section_10_Zonoid.Hypercube.Geometry.BoundaryNull
import Section_10_Zonoid.Hypercube.Sampling

/-!
The exact increasing-label bridge for the source simplex cocycle.
Bernoulli.subsetSignedSimplex uses the source ordering on each finite subset.
-/

noncomputable section

namespace Hypercube.Geometry.FiniteCocycle

theorem subsetSignedSimplex_erase {N m : Nat} (w : Fin N -> Geometry.Point m)
    (J : Finset (Fin N)) (hJ : J.card = m + 2) (r : Fin (m + 2)) :
    Bernoulli.subsetSignedSimplex w (J.erase (J.orderEmbOfFin hJ r)) =
      Geometry.signedSimplex (fun j => w (J.orderEmbOfFin hJ (r.succAbove j))) := by
  have hmem := J.orderEmbOfFin_mem hJ r
  have hI : (J.erase (J.orderEmbOfFin hJ r)).card = m + 1 := by
    have hcard := Finset.card_erase_add_one hmem
    rw [hJ] at hcard
    omega
  rw [Bernoulli.subsetSignedSimplex_of_card w _ hI]
  congr 1
  funext j
  rw [Sampling.orderEmb_erase_succAbove J hJ r hI j]

theorem increasing_signed_sum_eq_cocycleSum {N m : Nat}
    (w : Fin N -> Geometry.Point m) (x : Geometry.Point m)
    (J : Finset (Fin N)) (hJ : J.card = m + 2) :
    BinaryCocycle.increasingAlternatingSum (fun _ => 1)
      (fun I => Bernoulli.subsetSignedSimplex w I x) J =
      Cocycle.signedCocycleSum (fun r => w (J.orderEmbOfFin hJ r)) x := by
  unfold BinaryCocycle.increasingAlternatingSum Cocycle.signedCocycleSum
  apply Fintype.sum_equiv (Fin.castOrderIso hJ).toEquiv
  intro r
  let i := (Fin.castOrderIso hJ).toEquiv r
  have he : J.orderEmbOfFin rfl r = J.orderEmbOfFin hJ i := by
    apply Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr
    rfl
  change (-1 : Real) ^ r.val * 1 *
      Bernoulli.subsetSignedSimplex w (J.erase (J.orderEmbOfFin rfl r)) x =
    (-1 : Real) ^ i.val *
      Geometry.signedSimplex (Cocycle.omitted (fun a => w (J.orderEmbOfFin hJ a)) i) x
  rw [he, subsetSignedSimplex_erase w J hJ i]
  have hi : i.val = r.val := rfl
  rw [hi, mul_one]
  rfl

theorem increasing_signed_simplex_cocycle_ae {N m : Nat}
    (w : Fin N -> Geometry.Point m) (J : Finset (Fin N))
    (hJ : J.card = m + 2) :
    Filter.Eventually
      (fun x => BinaryCocycle.increasingAlternatingSum (fun _ => 1)
        (fun I => Bernoulli.subsetSignedSimplex w I x) J = 0)
      (MeasureTheory.ae MeasureTheory.volume) := by
  have hc := Cocycle.signed_simplex_cocycle_ae (fun r => w (J.orderEmbOfFin hJ r))
  exact hc.mono (fun x hx => by
    rw [increasing_signed_sum_eq_cocycleSum w x J hJ]
    exact hx)

/-- One common full-measure set for every increasing (m+2)-subset of labels. -/
theorem finite_signed_simplex_cocycle_common_ae {N m : Nat}
    (w : Fin N -> Geometry.Point m) :
    Filter.Eventually
      (fun x => forall J : Finset (Fin N), J.card = m + 2 ->
        BinaryCocycle.increasingAlternatingSum (fun _ => 1)
          (fun I => Bernoulli.subsetSignedSimplex w I x) J = 0)
      (MeasureTheory.ae MeasureTheory.volume) := by
  apply MeasureTheory.ae_all_iff.mpr
  intro J
  by_cases hJ : J.card = m + 2
  next =>
    exact (increasing_signed_simplex_cocycle_ae w J hJ).mono (fun _ hx _ => hx)
  next => exact Filter.Eventually.of_forall (fun _ hx => False.elim (hJ hx))

end Hypercube.Geometry.FiniteCocycle
