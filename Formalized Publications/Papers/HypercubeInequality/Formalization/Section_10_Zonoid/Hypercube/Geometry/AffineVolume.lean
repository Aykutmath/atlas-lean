import Section_10_Zonoid.Hypercube.Geometry.AffineDeterminant

/- Ordinary simplex volume under its explicit affine transport from the
reference chamber simplex. The Haar image theorem includes singular maps. -/

noncomputable section

namespace Hypercube.Geometry

open MeasureTheory

def simplexTransport {m : Nat} (w : Fin (m + 1) -> Point m) :
    AffineMap Real (Point m) (Point m) where
  toFun x := (Matrix.toLin' (edgeMatrix w)) x + w (Fin.last m)
  linear := Matrix.toLin' (edgeMatrix w)
  map_vadd' p v := by
    change (Matrix.toLin' (edgeMatrix w)) (v + p) + w (Fin.last m) =
      (Matrix.toLin' (edgeMatrix w)) v +
        ((Matrix.toLin' (edgeMatrix w)) p + w (Fin.last m))
    rw [map_add, add_assoc]

theorem simplexTransport_vertex {m : Nat} (w : Fin (m + 1) -> Point m)
    (r : Fin (m + 1)) : simplexTransport w (chamberVertex m r) = w r :=
  edgeMatrix_reference_image w r

theorem simplexHull_transport {m : Nat} (w : Fin (m + 1) -> Point m) :
    (simplexTransport w) '' simplexHull (chamberVertex m) = simplexHull w := by
  unfold simplexHull
  rw [AffineMap.image_convexHull]
  congr 1
  ext x
  constructor
  next =>
    intro h
    cases h with
    | intro y hy =>
        cases hy with
        | intro hyr hyx =>
            cases hyr with
            | intro r hry =>
                subst y
                exact Exists.intro r ((simplexTransport_vertex w r).symm.trans hyx)
  next =>
    intro h
    cases h with
    | intro r hr =>
        exact Exists.intro (chamberVertex m r)
          (And.intro (Exists.intro r rfl) ((simplexTransport_vertex w r).trans hr))

theorem volume_translation_image {m : Nat} (a : Point m) (s : Set (Point m)) :
    volume ((fun x => x + a) '' s) = volume s := by
  have hset : (fun x => x + a) '' s = Set.preimage (fun x => x + -a) s := by
    ext x
    constructor
    next =>
      intro h
      cases h with
      | intro y hy =>
          cases hy with
          | intro hys hyx =>
              subst x
              simpa using hys
    next =>
      intro h
      exact Exists.intro (x + -a) (And.intro h (by simp))
  rw [hset]
  exact measure_preimage_add_right volume (-a) s

theorem simplexVolume_edgeMatrix {m : Nat} (w : Fin (m + 1) -> Point m) :
    simplexVolume w = |(edgeMatrix w).det| * simplexVolume (chamberVertex m) := by
  have himage : (simplexTransport w) '' simplexHull (chamberVertex m) =
      (fun x => x + w (Fin.last m)) ''
        ((Matrix.toLin' (edgeMatrix w)) '' simplexHull (chamberVertex m)) := by
    rw [Set.image_image]
    rfl
  unfold simplexVolume
  rw [<- simplexHull_transport w, himage, volume_translation_image]
  rw [Measure.addHaar_image_linearMap, LinearMap.det_toLin']
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- Exact factorial normalization for ordinary Lebesgue simplex volume,
including dimension zero and determinant-zero simplices. -/
theorem simplex_volume_factorial {m : Nat} (w : Fin (m + 1) -> Point m) :
    (m.factorial : Real) * simplexVolume w = |affineDet w| := by
  rw [simplexVolume_edgeMatrix, <- affineDet_eq_edgeMatrix_det]
  calc
    (m.factorial : Real) * (|affineDet w| * simplexVolume (chamberVertex m)) =
      |affineDet w| * ((m.factorial : Real) * simplexVolume (chamberVertex m)) := by
        ring
    _ = |affineDet w| := by rw [chamber_simplex_volume_factorial, mul_one]

theorem abs_mul_orientation (a : Real) : |a| * orientation a = a := by
  unfold orientation
  split_ifs with hp hn
  next => simp [abs_of_pos hp]
  next => simp [abs_of_neg hn]
  next =>
    have ha : a = 0 := by linarith
    simp [ha]

/-- The source identity a_I = m! integral h_I with its exact orientation. -/
theorem signedSimplex_integral_factorial {m : Nat}
    (w : Fin (m + 1) -> Point m) :
    (m.factorial : Real) * integral volume (signedSimplex w) = affineDet w := by
  rw [signedSimplex_integral, <- mul_assoc, simplex_volume_factorial,
    abs_mul_orientation]

theorem signedSimplex_abs_integral {m : Nat} (w : Fin (m + 1) -> Point m) :
    integral volume (fun x => |signedSimplex w x|) =
      simplexVolume w * |orientation (affineDet w)| := by
  classical
  have heq : (fun x => |signedSimplex w x|) =
      (simplexHull w).indicator (fun _ => |orientation (affineDet w)|) := by
    funext x
    simp only [signedSimplex, Set.indicator_apply]
    split_ifs <;> simp
  rw [heq, integral_indicator_const _ (simplexHull_measurable w)]
  rfl

theorem signedSimplex_abs_integral_factorial {m : Nat}
    (w : Fin (m + 1) -> Point m) :
    (m.factorial : Real) * integral volume (fun x => |signedSimplex w x|) =
      |affineDet w| := by
  rw [signedSimplex_abs_integral, <- mul_assoc, simplex_volume_factorial]
  simpa only [abs_mul, abs_abs] using congrArg abs (abs_mul_orientation (affineDet w))

end Hypercube.Geometry
