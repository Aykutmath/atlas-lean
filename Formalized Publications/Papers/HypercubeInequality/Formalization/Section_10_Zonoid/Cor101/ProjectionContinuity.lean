import Section_10_Zonoid.Cor101.PlaneVolume
import Section_10_Zonoid.Cor101.LineVolume
import Section_10_Zonoid.Cor101.Images
import Section_10_Zonoid.Cor101.VolumeContinuity

/-! Intrinsic projected volumes represented as ordinary volumes of linear images.
These bridges apply to every convex body, not just finite zonotopes. -/
open MeasureTheory
noncomputable section
namespace Cor101

def lastCoordinateLinear (d : Nat) : Space d →ₗ[Real] Real where
  toFun x := x (Fin.last d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lastCoordinateCLM (d : Nat) : Space d →L[Real] Real :=
  LinearMap.toContinuousLinearMap (lastCoordinateLinear d)

def coordinatePairLinear (d : Nat) (j : Fin d) : Space d →ₗ[Real] Space 1 where
  toFun := coordinatePair d j
  map_add' x y := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  map_smul' c x := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl

def coordinatePairCLM (d : Nat) (j : Fin d) : Space d →L[Real] Space 1 :=
  LinearMap.toContinuousLinearMap (coordinatePairLinear d j)

theorem commonLineProjection_eq_embedding (d : Nat) (x : Space d) :
    commonLineProjection d x = lineEmbeddingLinear d (lastCoordinateCLM d x) := by
  rw [lineEmbeddingLinear_apply]
  apply PiLp.ext
  intro i
  change (coordinateSubspace d {Fin.last d}).starProjection x i = _
  rw [coordinateSubspace_projection_apply]
  by_cases hi : i = Fin.last d <;> simp [hi, lastCoordinateCLM, lastCoordinateLinear]
  rfl

theorem lineVolume_eq_volume_linearImage {d : Nat} (K : ConvexBody (Space d)) :
    lineVolume K = volume (linearImage (lastCoordinateCLM d) K : Set Real) := by
  unfold lineVolume
  have himage : commonLineProjection d '' (K : Set (Space d)) =
      lineEmbeddingLinear d '' (lastCoordinateCLM d '' (K : Set (Space d))) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact commonLineProjection_eq_embedding d x
  rw [himage, (lineEmbeddingLinear_isometry d).euclideanHausdorffMeasure_image]
  have hm : (Measure.euclideanHausdorffMeasure 1 : Measure Real) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Real))
  rw [hm]
  rfl

theorem planeVolume_eq_volume_linearImage {d : Nat} (K : ConvexBody (Space d))
    (j : Fin d) :
    planeVolume K j = volume (linearImage (coordinatePairCLM d j) K : Set (Space 1)) := by
  unfold planeVolume
  have himage : coordinatePlaneProjection d j '' (K : Set (Space d)) =
      planeEmbeddingLinear d j '' (coordinatePairCLM d j '' (K : Set (Space d))) := by
    rw [Set.image_image]
    congr 1
    funext x
    exact coordinatePlaneProjection_eq_embedding d j x
  rw [himage, (planeEmbeddingLinear_isometry d j).euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rfl

theorem fullVolume_ne_top {d : Nat} (K : ConvexBody (Space d)) :
    fullVolume K ≠ ⊤ := K.isCompact.measure_ne_top

theorem lineVolume_ne_top {d : Nat} (K : ConvexBody (Space d)) :
    lineVolume K ≠ ⊤ := by
  rw [lineVolume_eq_volume_linearImage]
  exact (linearImage (lastCoordinateCLM d) K).isCompact.measure_ne_top

theorem planeVolume_ne_top {d : Nat} (K : ConvexBody (Space d)) (j : Fin d) :
    planeVolume K j ≠ ⊤ := by
  rw [planeVolume_eq_volume_linearImage]
  exact (linearImage (coordinatePairCLM d j) K).isCompact.measure_ne_top

/-- Continuity of the intrinsic projected length, including collapsed projections. -/
theorem lineVolume_continuous (d : Nat) : Continuous (lineVolume (d := d)) := by
  change Continuous (fun K : ConvexBody (Space d) => lineVolume K)
  simp_rw [lineVolume_eq_volume_linearImage]
  exact continuous_volume_convexBody.comp (linearImage_continuous (lastCoordinateCLM d))

/-- Continuity of every intrinsic projected area, including collapsed projections. -/
theorem planeVolume_continuous (d : Nat) (j : Fin d) :
    Continuous (fun K : ConvexBody (Space d) => planeVolume K j) := by
  simp_rw [planeVolume_eq_volume_linearImage]
  exact continuous_volume_convexBody.comp (linearImage_continuous (coordinatePairCLM d j))

end Cor101
