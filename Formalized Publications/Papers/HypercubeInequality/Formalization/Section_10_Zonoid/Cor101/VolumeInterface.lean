import Section_10_Zonoid.Cor101.FiniteBridge
import Section_10_Zonoid.Cor101.LineVolume

/-!
The exact remaining finite geometric interface.

The determinant inequalities and the line-volume formula are proved.
The full-volume and plane-area identities are explicit hypotheses of the
theorem below. They have NOT been proved by introducing this interface.
In particular, this is not an unconditional proof of Corollary 10.1.
-/

namespace Cor101

/-- Conditional assembly for an actual finite zonotope. The only additional
hypotheses are the two still-missing determinant-volume formulas. All signs,
zero generators, horizontal generators, and repeated generators are allowed. -/
theorem zonotope_projection_of_volume_formulas {d N : Nat} (hd : 1 <= d)
    (v : Fin N -> Space d)
    (hfull : fullVolume (zonotopeBody v) = ENNReal.ofReal
      (FiniteBridge.fullDeterminantSum
        (fun i j => v i j.castSucc) (fun i => v i (Fin.last d))))
    (hplane : forall j, planeVolume (zonotopeBody v) j = ENNReal.ofReal
      (FiniteBridge.planarDeterminantSum
        (fun i j => v i j.castSucc) (fun i => v i (Fin.last d)) j)) :
    ProjectionInequality (zonotopeBody v) := by
  have h := ENNReal.ofReal_le_ofReal (FiniteBridge.all_generators_determinant_inequality
    hd (fun i j => v i j.castSucc) (fun i => v i (Fin.last d)))
  have hfull_nonneg : 0 <= FiniteBridge.fullDeterminantSum
      (fun i j => v i j.castSucc) (fun i => v i (Fin.last d)) := by
    unfold FiniteBridge.fullDeterminantSum
    positivity
  have hline_nonneg : 0 <= Finset.sum Finset.univ
      (fun i => |v i (Fin.last d)|) := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hplane_nonneg : forall j : Fin d, 0 <= FiniteBridge.planarDeterminantSum
      (fun i j => v i j.castSucc) (fun i => v i (Fin.last d)) j := by
    intro j
    unfold FiniteBridge.planarDeterminantSum
    positivity
  rw [ENNReal.ofReal_mul hfull_nonneg, ENNReal.ofReal_pow hline_nonneg,
    ENNReal.ofReal_prod_of_nonneg (fun j _ => hplane_nonneg j)] at h
  unfold ProjectionInequality
  rw [hfull, lineVolume_zonotopeBody]
  simpa only [hplane] using h

end Cor101
