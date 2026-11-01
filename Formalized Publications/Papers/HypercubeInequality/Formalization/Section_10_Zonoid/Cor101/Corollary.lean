import Section_10_Zonoid.Cor101.ZonotopeVolume
import Section_10_Zonoid.Cor101.ZonotopeDeterminants
import Section_10_Zonoid.Cor101.DeterminantCoordinates
import Section_10_Zonoid.Cor101.LimitAssembly
import Section_10_Zonoid.Cor101.VolumeInterface

/-!
# Corollary 10.1: the zonoid projection inequality

All volumes are the actual measures in `Cor101.Definitions`. The finite
volume formula is proved by geometric extrusion and dimension induction.
The extension to zonoids uses proved Hausdorff continuity of those measures.
-/
open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Cor101

/-- Ordinary Euclidean volume of an arbitrary finite-generator zonotope,
expressed as the ordered absolute maximal-minor sum divided by the factorial. -/
theorem volume_parallelepiped_ordered {n N : Nat}
    (v : Fin N → EuclideanSpace Real (Fin n)) :
    volume (parallelepiped v) = ENNReal.ofReal
      ((∑ f : Fin n → Fin N, |Matrix.det (fun i j => v (f i) j)|) /
        (n.factorial : Real)) := by
  have h := Zonotope.volume_finiteZonotope_subsets (Finset.univ : Finset (Fin N)) v
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h
  have hset : Zonotope.finiteZonotope Finset.univ v = parallelepiped v := by
    simp [Zonotope.finiteZonotope, parallelepiped_eq_sum_segment]
  rw [hset] at h
  exact h.trans (Zonotope.sum_subsets_volume_eq_ordered_determinant v)

/-- The full-volume identity required by the finite probability bridge. -/
theorem fullVolume_zonotopeBody {d N : Nat} (v : Fin N → Space d) :
    fullVolume (zonotopeBody v) = ENNReal.ofReal
      (FiniteBridge.fullDeterminantSum (fun i j => v i j.castSucc)
        (fun i => v i (Fin.last d))) := by
  rw [fullDeterminantSum_eq_coordinates]
  exact volume_parallelepiped_ordered v

/-- The planar determinant identity, with ordered-pair factor two. -/
theorem planeVolume_zonotopeBody {d N : Nat} (v : Fin N → Space d) (j : Fin d) :
    planeVolume (zonotopeBody v) j = ENNReal.ofReal
      (FiniteBridge.planarDeterminantSum (fun i k => v i k.castSucc)
        (fun i => v i (Fin.last d)) j) := by
  rw [planeVolume_zonotopeBody_eq_fullVolume, planarDeterminantSum_eq_coordinates]
  exact volume_parallelepiped_ordered (fun i => coordinatePair d j (v i))

/-- The projection inequality for every finite family, including zero,
horizontal, repeated and linearly dependent generators. -/
theorem projectionInequality_zonotopeBody {d N : Nat} (hd : 1 ≤ d)
    (v : Fin N → Space d) : ProjectionInequality (zonotopeBody v) :=
  zonotope_projection_of_volume_formulas hd v (fullVolume_zonotopeBody v)
    (planeVolume_zonotopeBody v)

/-- Translated zonotopes satisfy the literal geometric inequality. -/
theorem projectionInequality_of_isZonotope {d : Nat} (hd : 1 ≤ d)
    (K : ConvexBody (Space d)) (hK : IsZonotope K) : ProjectionInequality K :=
  zonotope_projection_of_generators (fun _ v => projectionInequality_zonotopeBody hd v) K hK

/-- Corollary 10.1, for all zonoids and every dimension d ≥ 1. -/
theorem corollary10_1 : Corollary10_1 := by
  intro d hd K hK
  exact zonoid_projection_of_zonotope (projectionInequality_of_isZonotope hd) K hK

/-- Validity together with optimality of the coefficient one. -/
theorem corollary10_1_with_sharpness :
    Corollary10_1 ∧ ∀ d : Nat, 1 ≤ d → SharpProjectionConstant d :=
  ⟨corollary10_1, fun d _ => sharpProjectionConstant d⟩

end Cor101
