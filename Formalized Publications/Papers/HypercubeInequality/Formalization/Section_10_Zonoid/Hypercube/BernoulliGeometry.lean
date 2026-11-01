import Section_10_Zonoid.Hypercube.Bernoulli
import Section_10_Zonoid.Hypercube.Geometry.AffineVolume
import Section_10_Zonoid.Hypercube.Geometry.FiniteCocycle

/- The actual geometric determinant data satisfy both integral identities.
The remaining premise in the first gate below is exactly its a.e. cocycle. -/

noncomputable section

namespace Hypercube.Bernoulli

open MeasureTheory
open Hypercube.BinaryCocycle

theorem subsetAffineDet_integral {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) (hI : I.card = m + 1) :
    subsetAffineDet w I = (m.factorial : Real) *
      integral volume (subsetSignedSimplex w I) := by
  rw [subsetAffineDet_of_card w I hI, subsetSignedSimplex_of_card w I hI]
  exact (Geometry.signedSimplex_integral_factorial _).symm

theorem subsetAffineDet_abs_integral {N m : Nat} (w : Fin N -> Geometry.Point m)
    (I : Finset (Fin N)) (hI : I.card = m + 1) :
    |subsetAffineDet w I| = (m.factorial : Real) *
      integral volume (fun x => |subsetSignedSimplex w I x|) := by
  rw [subsetAffineDet_of_card w I hI, subsetSignedSimplex_of_card w I hI]
  exact (Geometry.signedSimplex_abs_integral_factorial _).symm

theorem finite_support_bound_of_cocycle {N m : Nat}
    (w : Fin N -> Geometry.Point m) (q f : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1))
    (hcycle : Filter.Eventually
      (fun x => forall J, J.card = m + 2 ->
        increasingAlternatingSum (fun _ => 1) (fun I => subsetSignedSimplex w I x) J = 0)
      (ae volume)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    finiteL q f (subsetAffineDet w) m <=
      p * (1 - p) * finiteD q (subsetAffineDet w) m := by
  exact finite_support_geometric_bound_of_cocycle_and_volume w q f hq hqsum hbinary
    (subsetAffineDet_integral w) (subsetAffineDet_abs_integral w) hcycle

/-- The unconditional finite-support Bernoulli gate for actual signed simplices. -/
theorem finite_support_geometric_bound {N m : Nat}
    (w : Fin N -> Geometry.Point m) (q f : Fin N -> Real)
    (hq : forall i, 0 <= q i) (hqsum : Finset.sum Finset.univ q = 1)
    (hbinary : forall i, Or (f i = 0) (f i = 1)) :
    let p := Finset.sum Finset.univ (fun i => q i * f i)
    finiteL q f (subsetAffineDet w) m <=
      p * (1 - p) * finiteD q (subsetAffineDet w) m := by
  exact finite_support_bound_of_cocycle w q f hq hqsum hbinary
    (Geometry.FiniteCocycle.finite_signed_simplex_cocycle_common_ae w)

end Hypercube.Bernoulli
