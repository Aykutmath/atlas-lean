import AHHCovarianceRootGeometry
import AHHTensorPhaseDistance

/-! Sharp product-Euclidean square-root covariance bound for the actual sphere observable. -/
noncomputable section
open GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators Matrix.Norms.L2Operator
namespace AHHRadial

/-- The square root of the actual covariance norm is 1-Lipschitz for the full
Euclidean product distance. The sum retains both factors and every sample. -/
theorem unitCovarianceNorm_sqrt_sq_sub_le (n h : ℕ) (d e : Directions n h) :
    (Real.sqrt (unitCovarianceNorm n h d) - Real.sqrt (unitCovarianceNorm n h e)) ^ 2 ≤
      ∑ i, (‖((d i).1 : CE h) - ((e i).1 : CE h)‖ ^ 2 +
        ‖((d i).2 : CE h) - ((e i).2 : CE h)‖ ^ 2) := by
  choose c hc hd using fun i : Fin n =>
    exists_productVector_unit_phase_distance h (d i).1 (d i).2 (e i).1 (e i).2
  have hm := covariance_root_sq_dist_le
    (fun i => productVector h (d i).1 (d i).2)
    (fun i => c i • productVector h (e i).1 (e i).2)
  have he : (∑ i, InnerProductSpace.rankOne ℂ
      (c i • productVector h (e i).1 (e i).2)
      (c i • productVector h (e i).1 (e i).2)) = unitCovariance n h e := by
    unfold unitCovariance
    apply Finset.sum_congr rfl
    intro i _
    rw [rankOne_unit_phase _ _ (hc i), productProjector_eq_rankOne]
  have hh : (∑ i, InnerProductSpace.rankOne ℂ
      (productVector h (d i).1 (d i).2)
      (productVector h (d i).1 (d i).2)) = unitCovariance n h d := by
    unfold unitCovariance
    apply Finset.sum_congr rfl
    intro i _
    rw [productProjector_eq_rankOne]
  rw [he, hh] at hm
  exact hm.trans (Finset.sum_le_sum fun i _ => hd i)

#print axioms unitCovarianceNorm_sqrt_sq_sub_le
end AHHRadial
