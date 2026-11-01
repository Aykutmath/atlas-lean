import Section_10_Zonoid.Hypercube.Geometry.BoundaryNull
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/- Appendix A's test-function consequence of the actual a.e. signed-simplex
cocycle. No Stokes theorem is assumed; this follows from the checked cocycle. -/

noncomputable section

namespace Hypercube.Geometry.TestFunctionBridge

open MeasureTheory
open Hypercube.Geometry
open Hypercube.Geometry.Cocycle

theorem testFunction_signedSimplex_integrable {m : Nat}
    (w : Fin (m + 1) -> Point m) (phi : Point m -> Real) (hphi : Continuous phi) :
    Integrable (fun x => phi x * signedSimplex w x) volume := by
  classical
  have heq : (fun x => phi x * signedSimplex w x) =
      (simplexHull w).indicator (fun x => phi x * orientation (affineDet w)) := by
    funext x
    by_cases hx : Membership.mem (simplexHull w) x
    all_goals simp only [signedSimplex, Set.indicator_apply, hx]
    all_goals simp
  rw [heq]
  apply (integrable_indicator_iff (simplexHull_measurable w)).mpr
  exact (hphi.mul continuous_const).continuousOn.integrableOn_compact (simplexHull_compact w)

theorem testFunction_integral_cocycle_zero {m : Nat}
    (w : Fin (m + 2) -> Point m) (phi : Point m -> Real) :
    integral volume (fun x => phi x * signedCocycleSum w x) = 0 := by
  calc
    _ = integral volume (fun _ : Point m => (0 : Real)) := by
      apply integral_congr_ae
      exact (signed_simplex_cocycle_ae w).mono (fun x hx => by
        dsimp only
        rw [hx, mul_zero])
    _ = 0 := integral_zero _ _

theorem signed_simplex_testFunction_identity {m : Nat}
    (w : Fin (m + 2) -> Point m) (phi : Point m -> Real) (hphi : Continuous phi) :
    Finset.sum Finset.univ (fun i => (-1 : Real) ^ i.val *
      integral volume (fun x => phi x * signedSimplex (omitted w i) x)) = 0 := by
  have hint (i : Fin (m + 2)) :
      Integrable (fun x => (-1 : Real) ^ i.val *
        (phi x * signedSimplex (omitted w i) x)) volume :=
    (testFunction_signedSimplex_integrable _ phi hphi).const_mul _
  calc
    _ = integral volume (fun x => Finset.sum Finset.univ
        (fun i => (-1 : Real) ^ i.val * (phi x * signedSimplex (omitted w i) x))) := by
      rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
      simp_rw [integral_const_mul]
    _ = integral volume (fun x => phi x * signedCocycleSum w x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only
        unfold signedCocycleSum
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring)
    _ = 0 := testFunction_integral_cocycle_zero w phi

end Hypercube.Geometry.TestFunctionBridge
