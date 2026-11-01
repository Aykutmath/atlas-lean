import Section_10_Zonoid.Cor101.Definitions

/-! Translation invariance for the actual geometric volumes in Corollary 10.1. -/

namespace Cor101

noncomputable def translate {d : Nat} (a : Space d)
    (K : ConvexBody (Space d)) : ConvexBody (Space d) where
  carrier := (fun x => a + x) '' (K : Set (Space d))
  convex' := K.convex.translate a
  isCompact' := K.isCompact.image (continuous_const.add continuous_id)
  nonempty' := K.nonempty.image _

theorem linear_image_translate {d : Nat} (f : Space d →L[Real] Space d)
    (a : Space d) (K : ConvexBody (Space d)) :
    f '' (translate a K : Set (Space d)) =
      (fun x => f a + x) '' (f '' (K : Set (Space d))) := by
  change f '' ((fun x => a + x) '' (K : Set (Space d))) = _
  simp only [Set.image_image, map_add]

theorem fullVolume_translate {d : Nat} (a : Space d)
    (K : ConvexBody (Space d)) : fullVolume (translate a K) = fullVolume K := by
  unfold fullVolume
  rw [<- EuclideanSpace.euclideanHausdorffMeasure_eq_volume (d + 1)]
  exact (isometry_add_left a).euclideanHausdorffMeasure_image (K : Set (Space d))

theorem lineVolume_translate {d : Nat} (a : Space d)
    (K : ConvexBody (Space d)) : lineVolume (translate a K) = lineVolume K := by
  unfold lineVolume
  rw [linear_image_translate]
  exact (isometry_add_left (commonLineProjection d a)).euclideanHausdorffMeasure_image _

theorem planeVolume_translate {d : Nat} (a : Space d)
    (K : ConvexBody (Space d)) (j : Fin d) :
    planeVolume (translate a K) j = planeVolume K j := by
  unfold planeVolume
  rw [linear_image_translate]
  exact (isometry_add_left (coordinatePlaneProjection d j a)).euclideanHausdorffMeasure_image _

theorem projectionInequality_translate_iff {d : Nat} (a : Space d)
    (K : ConvexBody (Space d)) :
    ProjectionInequality (translate a K) <-> ProjectionInequality K := by
  simp only [ProjectionInequality, fullVolume_translate, lineVolume_translate,
    planeVolume_translate]

theorem translate_isometry {d : Nat} (a : Space d) : Isometry (translate a) := by
  apply Isometry.of_dist_eq
  intro K L
  exact Metric.hausdorffDist_image (isometry_add_left a)

theorem IsZonotope.translate {d : Nat} {K : ConvexBody (Space d)}
    (hK : IsZonotope K) (a : Space d) : IsZonotope (translate a K) := by
  obtain ⟨N, b, v, hv⟩ := hK
  refine ⟨N, a + b, v, ?_⟩
  change (fun x => a + x) '' (K : Set (Space d)) = _
  rw [hv, Set.image_image]
  simp only [add_assoc]

end Cor101
