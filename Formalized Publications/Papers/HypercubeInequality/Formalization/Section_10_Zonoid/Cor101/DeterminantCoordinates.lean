import Section_10_Zonoid.Cor101.FiniteBridge
import Section_10_Zonoid.Cor101.PlaneVolume

/-! Coordinate identifications for the ordinary zonotope volume formula. -/
open scoped BigOperators
noncomputable section
namespace Cor101

theorem fullDeterminantSum_eq_coordinates {d N : Nat} (v : Fin N → Space d) :
    FiniteBridge.fullDeterminantSum (fun i j => v i j.castSucc)
      (fun i => v i (Fin.last d)) =
      (∑ f : Fin (d + 1) → Fin N, |Matrix.det (fun i j => v (f i) j)|) /
        ((d + 1).factorial : Real) := by
  unfold FiniteBridge.fullDeterminantSum
  congr 1
  apply Finset.sum_congr rfl
  intro f hf
  congr 2
  funext i j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp

theorem planarDeterminantSum_eq_coordinates {d N : Nat} (v : Fin N → Space d)
    (j : Fin d) :
    FiniteBridge.planarDeterminantSum (fun i k => v i k.castSucc)
      (fun i => v i (Fin.last d)) j =
      (∑ f : Fin 2 → Fin N,
        |Matrix.det (fun i k => coordinatePair d j (v (f i)) k)|) /
          ((2 : Nat).factorial : Real) := by
  unfold FiniteBridge.planarDeterminantSum
  norm_num only [Nat.factorial]
  congr 1
  rw [← Equiv.sum_comp (finTwoArrowEquiv (Fin N)).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  simp only [coordinatePair, finTwoArrowEquiv_symm_apply]
  congr 1
  change _ = Matrix.det (Matrix.of (fun r c : Fin 2 =>
    ![v (![i, k] r) j.castSucc, v (![i, k] r) (Fin.last d)] c))
  rw [Matrix.det_fin_two]
  simp
  ring

end Cor101
