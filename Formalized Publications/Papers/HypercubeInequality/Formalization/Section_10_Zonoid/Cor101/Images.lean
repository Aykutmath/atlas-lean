import Section_10_Zonoid.Cor101.Definitions

/-!
# Hausdorff continuity of the projection operation

This file concerns the sets being projected. It does not assume or prove
continuity of their volumes.
-/

namespace Cor101

section LinearImages

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

/-- A continuous linear image of a nonempty compact convex set, with the
actual image as its carrier. -/
noncomputable def linearImage (f : E →L[Real] F)
    (K : ConvexBody E) : ConvexBody F where
  carrier := f '' (K : Set E)
  convex' := K.convex.linear_image f.toLinearMap
  isCompact' := K.isCompact.image f.continuous
  nonempty' := K.nonempty.image f

@[simp] theorem coe_linearImage (f : E →L[Real] F)
    (K : ConvexBody E) :
    (linearImage f K : Set F) = f '' (K : Set E) := rfl

/-- A c-Lipschitz linear map induces a c-Lipschitz map on convex bodies
equipped with their Hausdorff metrics. -/
theorem linearImage_lipschitz (f : E →L[Real] F)
    {c : NNReal} (hf : LipschitzWith c f) :
    LipschitzWith c (linearImage f) := by
  have directed (A B : ConvexBody E) (x : E) (hx : x ∈ A) :
      ∃ y ∈ B, dist (f x) (f y) <= (c : Real) * dist A B := by
    obtain ⟨y, hy, hxy⟩ := B.isCompact.exists_infDist_eq_dist B.nonempty x
    refine ⟨y, hy, ?_⟩
    calc
      dist (f x) (f y) <= (c : Real) * dist x y := hf.dist_le_mul x y
      _ = (c : Real) * Metric.infDist x (B : Set E) := by rw [hxy]
      _ <= (c : Real) * Metric.hausdorffDist (A : Set E) (B : Set E) :=
        mul_le_mul_of_nonneg_left
          (Metric.infDist_le_hausdorffDist_of_mem hx
            ConvexBody.hausdorffEDist_ne_top) c.coe_nonneg
      _ = (c : Real) * dist A B := rfl
  apply LipschitzWith.of_dist_le_mul
  intro A B
  change Metric.hausdorffDist (f '' (A : Set E)) (f '' (B : Set E)) <=
    (c : Real) * dist A B
  apply Metric.hausdorffDist_le_of_mem_dist
    (mul_nonneg c.coe_nonneg dist_nonneg)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := directed A B x hx
    exact ⟨f y, Set.mem_image_of_mem f hy, hxy⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := directed B A y hy
    refine ⟨f x, Set.mem_image_of_mem f hx, ?_⟩
    simpa only [dist_comm B A] using hyx

/-- Every continuous linear map acts continuously on convex bodies in the
Hausdorff topology. -/
theorem linearImage_continuous (f : E →L[Real] F) :
    Continuous (linearImage f) :=
  (linearImage_lipschitz f f.lipschitzWith).continuous

end LinearImages

/-- The common-line projection is nonexpansive for Hausdorff distance. -/
theorem commonLineImage_lipschitz (d : Nat) :
    LipschitzWith 1 (linearImage (commonLineProjection d)) :=
  linearImage_lipschitz _ (commonLine d).lipschitzWith_starProjection

/-- Each coordinate-plane projection is nonexpansive for Hausdorff distance. -/
theorem coordinatePlaneImage_lipschitz (d : Nat) (j : Fin d) :
    LipschitzWith 1 (linearImage (coordinatePlaneProjection d j)) :=
  linearImage_lipschitz _ (coordinatePlane d j).lipschitzWith_starProjection

end Cor101
