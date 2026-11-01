import Section_10_Zonoid.Cor101.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Sharpness and the coordinate unit box

This file uses actual Euclidean convex bodies and canonical measures.
The unit box is the parallelepiped of the standard orthonormal basis.
-/

open MeasureTheory
open scoped ENNReal

namespace Cor101

/-- The coefficient in Corollary 10.1 cannot be reduced below one. -/
def SharpProjectionConstant (d : Nat) : Prop :=
  forall C : ENNReal,
    (forall K : ConvexBody (Space d), IsZonoid K ->
      fullVolume K * lineVolume K ^ (d - 1) <=
        C * ∏ j : Fin d, planeVolume K j) -> 1 <= C

/-- A unit box, defined geometrically using the standard orthonormal basis. -/
noncomputable def unitBox (d : Nat) : ConvexBody (Space d) where
  carrier := parallelepiped (EuclideanSpace.basisFun (Fin (d + 1)) Real)
  convex' := convex_parallelepiped _
  isCompact' := (EuclideanSpace.basisFun (Fin (d + 1)) Real).toBasis.parallelepiped.isCompact
  nonempty' := (EuclideanSpace.basisFun (Fin (d + 1)) Real).toBasis.parallelepiped.nonempty

/-- The coordinate unit box is a zonotope, with its standard generators. -/
theorem unitBox_isZonotope (d : Nat) : IsZonotope (unitBox d) := by
  refine ⟨d + 1, 0, EuclideanSpace.basisFun (Fin (d + 1)) Real, ?_⟩
  change parallelepiped (EuclideanSpace.basisFun (Fin (d + 1)) Real) =
    (fun x : Space d => 0 + x) '' parallelepiped (EuclideanSpace.basisFun (Fin (d + 1)) Real)
  simp

/-- Consequently, the unit box is among the zonoids quantified in the paper. -/
theorem unitBox_isZonoid (d : Nat) : IsZonoid (unitBox d) :=
  (unitBox_isZonotope d).isZonoid

/-- Its ambient Euclidean volume is one. -/
theorem fullVolume_unitBox (d : Nat) : fullVolume (unitBox d) = 1 := by
  exact (EuclideanSpace.basisFun (Fin (d + 1)) Real).volume_parallelepiped

/-- The standard-basis parallelepiped has precisely the usual coordinate bounds. -/
theorem mem_unitBox_iff (d : Nat) (x : Space d) :
    x ∈ unitBox d ↔ forall i, 0 <= x i ∧ x i <= 1 := by
  change x ∈ parallelepiped (EuclideanSpace.basisFun (Fin (d + 1)) Real) ↔ _
  rw [show parallelepiped (EuclideanSpace.basisFun (Fin (d + 1)) Real) =
      parallelepiped (EuclideanSpace.basisFun (Fin (d + 1)) Real).toBasis by rfl]
  rw [parallelepiped_basis_eq]
  simp only [Set.mem_ofPred_eq, Set.mem_Icc,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

/-- Orthogonal projection onto a coordinate subspace deletes exactly the
coordinates outside that subspace. -/
theorem coordinateSubspace_projection_apply (d : Nat)
    (s : Finset (Fin (d + 1))) (x : Space d) (i : Fin (d + 1)) :
    (coordinateSubspace d s).starProjection x i = if i ∈ s then x i else 0 := by
  classical
  by_cases hi : i ∈ s
  · rw [ite_eq_left hi]
    have hv : EuclideanSpace.single i (1 : Real) ∈ coordinateSubspace d s := by
      intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hj hi
      simp [hji]
    have hz := (coordinateSubspace d s).starProjection_inner_eq_zero
      x (EuclideanSpace.single i (1 : Real)) hv
    have heq : x i - (coordinateSubspace d s).starProjection x i = 0 := by
      simpa [EuclideanSpace.inner_single_right] using hz
    exact (sub_eq_zero.mp heq).symm
  · rw [ite_eq_right hi]
    exact (coordinateSubspace d s).starProjection_apply_mem x i hi

/-- The common-line projection of the unit box is the unit segment. -/
theorem commonLineProjection_unitBox (d : Nat) :
    commonLineProjection d '' (unitBox d : Set (Space d)) =
      (fun t : Real => EuclideanSpace.single (Fin.last d) t) '' Set.Icc 0 1 := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x (Fin.last d), (mem_unitBox_iff d x).mp hx (Fin.last d), ?_⟩
    apply PiLp.ext
    intro i
    change _ = (coordinateSubspace d {Fin.last d}).starProjection x i
    rw [coordinateSubspace_projection_apply]
    by_cases hi : i = Fin.last d <;> simp [hi]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨EuclideanSpace.single (Fin.last d) t, ?_, ?_⟩
    · apply (mem_unitBox_iff d _).mpr
      intro i
      by_cases hi : i = Fin.last d
      · simpa [PiLp.single_apply, hi] using ht
      · simp [hi]
    · apply PiLp.ext
      intro i
      change (coordinateSubspace d {Fin.last d}).starProjection _ i = _
      rw [coordinateSubspace_projection_apply]
      by_cases hi : i = Fin.last d <;> simp [hi]

/-- The common-line projection has its ordinary intrinsic length one. -/
theorem lineVolume_unitBox (d : Nat) : lineVolume (unitBox d) = 1 := by
  unfold lineVolume
  rw [commonLineProjection_unitBox]
  have hi : Isometry (fun t : Real => EuclideanSpace.single (Fin.last d) t) := by
    rw [isometry_iff_dist_eq]
    intro x y
    exact PiLp.dist_single_same (p := 2) (β := fun _ : Fin (d + 1) => Real)
      (Fin.last d) x y
  rw [hi.euclideanHausdorffMeasure_image]
  have hmeasure : (Measure.euclideanHausdorffMeasure 1 : Measure Real) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Real))
  rw [hmeasure]
  simp [Real.volume_Icc]

/-- The standard isometric inclusion of the two coordinate axes of E_j. -/
noncomputable def planeEmbeddingLinear (d : Nat) (j : Fin d) :
    Space 1 →ₗ[Real] Space d :=
  (EuclideanSpace.basisFun (Fin 2) Real).toBasis.constr Real
    (fun i : Fin 2 => (EuclideanSpace.basisFun (Fin (d + 1)) Real)
      (if i = 0 then j.castSucc else Fin.last d))

theorem planeEmbeddingLinear_apply (d : Nat) (j : Fin d) (x : Space 1) :
    planeEmbeddingLinear d j x =
      EuclideanSpace.single j.castSucc (x 0) + EuclideanSpace.single (Fin.last d) (x 1) := by
  simp [planeEmbeddingLinear, Module.Basis.constr_apply_fintype,
    EuclideanSpace.basisFun_repr, Fin.sum_univ_two, EuclideanSpace.basisFun_apply]
  apply PiLp.ext
  intro i
  by_cases hij : i = j.castSucc <;> by_cases hil : i = Fin.last d <;>
    simp [hij, hil]

/-- The plane inclusion preserves the actual Euclidean metric. -/
theorem planeEmbeddingLinear_isometry (d : Nat) (j : Fin d) :
    Isometry (planeEmbeddingLinear d j) := by
  have hinner : forall x y : Space 1,
      inner Real (planeEmbeddingLinear d j x) (planeEmbeddingLinear d j y) =
        inner Real x y := by
    intro x y
    rw [planeEmbeddingLinear_apply, planeEmbeddingLinear_apply]
    simp [inner_add_left, inner_add_right,
      PiLp.single_apply, PiLp.inner_apply, Fin.sum_univ_two,
      Ne.symm (Fin.castSucc_ne_last j)]
  exact ((planeEmbeddingLinear d j).isometryOfInner hinner).isometry

/-- Every coordinate-plane projection of the unit box is an isometric unit square. -/
theorem coordinatePlaneProjection_unitBox (d : Nat) (j : Fin d) :
    coordinatePlaneProjection d j '' (unitBox d : Set (Space d)) =
      planeEmbeddingLinear d j '' (unitBox 1 : Set (Space 1)) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let z : Space 1 := WithLp.toLp 2 ![x j.castSucc, x (Fin.last d)]
    refine ⟨z, ?_, ?_⟩
    · apply (mem_unitBox_iff 1 z).mpr
      intro i
      fin_cases i
      · exact (mem_unitBox_iff d x).mp hx j.castSucc
      · exact (mem_unitBox_iff d x).mp hx (Fin.last d)
    · rw [planeEmbeddingLinear_apply]
      apply PiLp.ext
      intro i
      change _ = (coordinateSubspace d {j.castSucc, Fin.last d}).starProjection x i
      rw [coordinateSubspace_projection_apply]
      by_cases hi : i = j.castSucc
      · subst i
        simp [z]
      · by_cases hil : i = Fin.last d
        · subst i
          simp [z]
        · simp [z, hi, hil]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨planeEmbeddingLinear d j z, ?_, ?_⟩
    · apply (mem_unitBox_iff d _).mpr
      intro i
      rw [planeEmbeddingLinear_apply]
      by_cases hi : i = j.castSucc
      · subst i
        simpa [PiLp.single_apply] using (mem_unitBox_iff 1 z).mp hz (0 : Fin 2)
      · by_cases hil : i = Fin.last d
        · subst i
          simpa [PiLp.single_apply] using (mem_unitBox_iff 1 z).mp hz (1 : Fin 2)
        · simp [hi, hil]
    · apply (coordinatePlane d j).starProjection_eq_self_iff.mpr
      intro i hi
      rw [planeEmbeddingLinear_apply]
      have hij : i ≠ j.castSucc := by
        intro h
        apply hi
        simp [h]
      have hil : i ≠ Fin.last d := by
        intro h
        apply hi
        simp [h]
      simp [hij, hil]

/-- Every coordinate-plane projection has its ordinary Euclidean area one. -/
theorem planeVolume_unitBox (d : Nat) (j : Fin d) : planeVolume (unitBox d) j = 1 := by
  unfold planeVolume
  rw [coordinatePlaneProjection_unitBox,
    (planeEmbeddingLinear_isometry d j).euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  exact fullVolume_unitBox 1

/-- The geometric coordinate unit box attains equality. -/
theorem unitBox_projectionEquality (d : Nat) :
    fullVolume (unitBox d) * lineVolume (unitBox d) ^ (d - 1) =
      ∏ j : Fin d, planeVolume (unitBox d) j := by
  simp [fullVolume_unitBox, lineVolume_unitBox, planeVolume_unitBox]

/-- A genuine unit-volume equality witness proves the sharpness assertion.
The three measure identities are explicit hypotheses, not hidden assumptions. -/
theorem sharpProjectionConstant_of_unit_witness {d : Nat}
    (K : ConvexBody (Space d)) (hK : IsZonoid K)
    (hfull : fullVolume K = 1) (hline : lineVolume K = 1)
    (hplane : forall j, planeVolume K j = 1) : SharpProjectionConstant d := by
  intro C hC
  simpa [hfull, hline, hplane] using hC K hK

/-- At d = 1, the existing geometric endpoint theorem identifies the plane
with the whole ambient space, so the unit box already proves sharpness. -/
theorem sharpProjectionConstant_one : SharpProjectionConstant 1 := by
  intro C hC
  have h := hC (unitBox 1) (unitBox_isZonoid 1)
  simpa [planeVolume_one, fullVolume_unitBox] using h

/-- The constant one is sharp in every dimension from Corollary 10.1. -/
theorem sharpProjectionConstant (d : Nat) : SharpProjectionConstant d :=
  sharpProjectionConstant_of_unit_witness (unitBox d) (unitBox_isZonoid d)
    (fullVolume_unitBox d) (lineVolume_unitBox d) (planeVolume_unitBox d)

end Cor101
