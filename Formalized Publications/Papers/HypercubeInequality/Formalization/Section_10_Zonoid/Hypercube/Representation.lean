import Section_10_Zonoid.Hypercube.Statements
import Section_10_Zonoid.Hypercube.Geometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convex.Hull

/-!
The paper uses ordinary Euclidean Lebesgue volume. `Paper.Point d` is the
coordinate function model, whose topology uses the sup norm. The canonical
coordinate map is a continuous linear equivalence, not an isometry, and its
volume preservation is an exact Mathlib theorem. No scale factor is inserted.
These bridges do not prove the random-simplex or Hypercube inequalities.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.Representation

abbrev EuclideanPoint (d : Nat) := EuclideanSpace Real (Fin d)

def coordinateEuclideanEquiv (d : Nat) :
    ContinuousLinearEquiv (RingHom.id Real) (Paper.Point d) (EuclideanPoint d) :=
  (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin d => Real)).symm

theorem coordinate_volume_is_product (d : Nat) :
    (volume : Measure (Paper.Point d)) =
      Measure.pi (fun _ : Fin d => (volume : Measure Real)) := by
  exact volume_pi

theorem coordinateEuclideanEquiv_measurePreserving (d : Nat) :
    MeasurePreserving (coordinateEuclideanEquiv d) volume volume := by
  exact PiLp.volume_preserving_toLp (Fin d)

theorem coordinateEuclideanEquiv_image_convexHull (d : Nat)
    (s : Set (Paper.Point d)) :
    coordinateEuclideanEquiv d '' convexHull Real s =
      convexHull Real (coordinateEuclideanEquiv d '' s) := by
  exact (coordinateEuclideanEquiv d).toLinearMap.image_convexHull s

theorem coordinateEuclideanEquiv_volume_image (d : Nat)
    (s : Set (Paper.Point d)) :
    volume (coordinateEuclideanEquiv d '' s) = volume s := by
  let e : MeasurableEquiv (Paper.Point d) (EuclideanPoint d) :=
    MeasurableEquiv.toLp 2 (Paper.Point d)
  have hmp : MeasurePreserving e.symm volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)
  have hpre := hmp.measure_preimage_equiv s
  have hset : Set.preimage e.symm s = coordinateEuclideanEquiv d '' s := by
    ext x
    constructor
    case mp =>
      intro hx
      exact Exists.intro (e.symm x) (And.intro hx (e.apply_symm_apply x))
    case mpr =>
      intro hx
      cases hx with
      | intro y hy =>
        cases hy with
        | intro hys hyx =>
          cases hyx
          exact hys
  rw [hset] at hpre
  exact hpre

theorem coordinateEuclideanEquiv_volume_convexHull (d : Nat)
    (s : Set (Paper.Point d)) :
    volume (convexHull Real (coordinateEuclideanEquiv d '' s)) =
      volume (convexHull Real s) := by
  rw [Eq.symm (coordinateEuclideanEquiv_image_convexHull d s)]
  exact coordinateEuclideanEquiv_volume_image d (convexHull Real s)

def euclideanSimplexVolume {d : Nat}
    (z : Fin (d + 1) -> EuclideanPoint d) : Real :=
  (volume (convexHull Real (Set.range z))).toReal

theorem simplexVolume_eq_euclideanSimplexVolume {d : Nat}
    (z : Fin (d + 1) -> Paper.Point d) :
    Paper.simplexVolume z =
      euclideanSimplexVolume (fun i => coordinateEuclideanEquiv d (z i)) := by
  unfold Paper.simplexVolume euclideanSimplexVolume
  have hrange : Set.range (fun i => coordinateEuclideanEquiv d (z i)) =
      coordinateEuclideanEquiv d '' Set.range z := by
    exact Set.range_comp (coordinateEuclideanEquiv d) z
  rw [hrange, coordinateEuclideanEquiv_volume_convexHull]

theorem paper_simplexVolume_eq_geometry_simplexVolume {d : Nat}
    (z : Fin (d + 1) -> Paper.Point d) :
    Paper.simplexVolume z = Geometry.simplexVolume z := rfl

theorem paper_simplexHull_volume_ne_top {d : Nat}
    (z : Fin (d + 1) -> Paper.Point d) :
    Not (volume (convexHull Real (Set.range z)) = Top.top) := by
  have hfinite : Not (volume (Geometry.simplexHull z) = Top.top) :=
    (Geometry.simplexHull_compact z).measure_ne_top
  exact hfinite

theorem normalizedCubeVolume_eq_euclidean_volume {d : Nat}
    (s : Finset (Paper.Cube d)) :
    Paper.normalizedCubeVolume s = (Nat.factorial d : Real) *
      (volume (convexHull Real
        (coordinateEuclideanEquiv d '' (Paper.cubePoint '' (s : Set (Paper.Cube d)))))).toReal := by
  unfold Paper.normalizedCubeVolume
  rw [coordinateEuclideanEquiv_volume_convexHull]

theorem paper_cubeHull_volume_ne_top {d : Nat}
    (s : Finset (Paper.Cube d)) :
    Not (volume (convexHull Real (Paper.cubePoint '' (s : Set (Paper.Cube d)))) = Top.top) := by
  have hfinite : Not (volume (convexHull Real
      (Paper.cubePoint '' (s : Set (Paper.Cube d)))) = Top.top) :=
    ((s.finite_toSet.image Paper.cubePoint).isCompact_convexHull Real).measure_ne_top
  exact hfinite

end Hypercube.Representation
