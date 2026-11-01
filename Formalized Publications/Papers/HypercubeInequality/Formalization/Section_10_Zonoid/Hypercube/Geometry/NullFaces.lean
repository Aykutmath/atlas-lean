import Section_10_Zonoid.Hypercube.Geometry.AffineVolume

/-!
The exceptional faces in the signed-simplex cocycle have actual Lebesgue
measure zero.  Determinant degeneracy is connected to that measure only through
the proved factorial-volume bridge, never through a substitute definition.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.Geometry

theorem simplexHull_volume_zero_of_affineDet_zero {m : Nat}
    (w : Fin (m + 1) -> Point m) (hdet : affineDet w = 0) :
    volume (simplexHull w) = 0 := by
  have hfactor := simplex_volume_factorial w
  rw [hdet, abs_zero] at hfactor
  have hfac : Not ((m.factorial : Real) = 0) := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hreal : (volume (simplexHull w)).toReal = 0 := by
    exact (mul_eq_zero.mp hfactor).resolve_left hfac
  exact ((ENNReal.toReal_eq_zero_iff _).mp hreal).resolve_right
    (simplexHull_compact w).measure_ne_top

theorem volume_finite_hull_zero {m : Nat} (hm : 0 < m)
    (v : Fin m -> Point m) :
    volume (convexHull Real (Set.range v)) = 0 := by
  let r : Fin m := Fin.mk 0 hm
  let w : Fin (m + 1) -> Point m := Fin.cons (v r) v
  have hdup : w 0 = w r.succ := by
    simp only [w, Fin.cons_zero, Fin.cons_succ]
  have hne : Not ((0 : Fin (m + 1)) = r.succ) := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  have hdet : affineDet w = 0 := affineDet_zero_of_repeated_point w hne hdup
  have hrange : Set.range w = Set.range v := by
    change Set.range (Fin.cons (v r) v) = Set.range v
    rw [Fin.range_cons]
    exact Set.insert_eq_of_mem (Set.mem_range_self r)
  have hhull : simplexHull w = convexHull Real (Set.range v) := by
    rw [simplexHull, hrange]
  rw [<- hhull]
  exact simplexHull_volume_zero_of_affineDet_zero w hdet

end Hypercube.Geometry
