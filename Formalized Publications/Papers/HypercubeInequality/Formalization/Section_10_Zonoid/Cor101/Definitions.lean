import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Sequences

/-!
# Paper-facing definitions for Corollary 10.1

The source is Corollary 10.1 of the final Hypercube manuscript dated
2026-10-29. These definitions use genuine Euclidean sets, canonical Lebesgue
volume, and normalized Euclidean Hausdorff measures of projections.

`IsZonoid` includes translations and lower-dimensional limits. No inequality
or volume identity is built into this definition.

The full assertion `Corollary10_1` is a proposition, not a proved theorem.
The theorem `projectionInequality_one` below proves only the endpoint d = 1.
-/

open MeasureTheory
open scoped ENNReal

namespace Cor101

/-- The paper's ambient space R^(d+1), with its Euclidean metric. -/
abbrev Space (d : Nat) := EuclideanSpace Real (Fin (d + 1))

/-- The coordinate subspace supported on a specified set of coordinate indices. -/
def coordinateSubspace (d : Nat) (s : Finset (Fin (d + 1))) :
    Submodule Real (Space d) where
  carrier := {x | forall i, i ∉ s -> x i = 0}
  zero_mem' := by
    intro i hi
    rfl
  add_mem' := by
    intro x y hx hy i hi
    change x i + y i = 0
    rw [hx i hi, hy i hi, add_zero]
  smul_mem' := by
    intro c x hx i hi
    change c * x i = 0
    rw [hx i hi, mul_zero]

/-- The final coordinate axis L in the manuscript. -/
def commonLine (d : Nat) : Submodule Real (Space d) :=
  coordinateSubspace d {Fin.last d}

/-- The plane E_j spanned by coordinate j and the final coordinate axis.
Lean indexes the first d coordinates by `Fin d`, starting at zero. -/
def coordinatePlane (d : Nat) (j : Fin d) : Submodule Real (Space d) :=
  coordinateSubspace d {j.castSucc, Fin.last d}

/-- Orthogonal projection onto L, regarded as a map into the ambient space. -/
noncomputable def commonLineProjection (d : Nat) :
    Space d →L[Real] Space d :=
  (commonLine d).starProjection

/-- Orthogonal projection onto E_j, regarded as a map into the ambient space. -/
noncomputable def coordinatePlaneProjection (d : Nat) (j : Fin d) :
    Space d →L[Real] Space d :=
  (coordinatePlane d j).starProjection

/-- A translated finite Minkowski sum of segments.
Mathlib's `parallelepiped` accepts any finite number of generators. -/
def IsZonotope {d : Nat} (K : ConvexBody (Space d)) : Prop :=
  exists (m : Nat) (a : Space d) (v : Fin m -> Space d),
    (K : Set (Space d)) = (fun x => a + x) '' parallelepiped v

/-- A Hausdorff limit of zonotopes, using the Hausdorff topology already
carried by Mathlib's `ConvexBody`. This includes degenerate zonoids. -/
def IsZonoid {d : Nat} (K : ConvexBody (Space d)) : Prop :=
  K ∈ closure {Z : ConvexBody (Space d) | IsZonotope Z}

/-- Ambient (d+1)-dimensional Euclidean volume. -/
noncomputable def fullVolume {d : Nat} (K : ConvexBody (Space d)) : ENNReal :=
  volume (K : Set (Space d))

/-- Length of the orthogonal projection onto the common line.
Normalized Euclidean Hausdorff measure gives intrinsic length in the ambient
space; ambient Lebesgue measure of this set would generally be zero. -/
noncomputable def lineVolume {d : Nat} (K : ConvexBody (Space d)) : ENNReal :=
  Measure.euclideanHausdorffMeasure 1
    (commonLineProjection d '' (K : Set (Space d)))

/-- Area of the orthogonal projection onto E_j, with ordinary Euclidean
normalization, including when the projection is lower dimensional. -/
noncomputable def planeVolume {d : Nat} (K : ConvexBody (Space d)) (j : Fin d) :
    ENNReal :=
  Measure.euclideanHausdorffMeasure 2
    (coordinatePlaneProjection d j '' (K : Set (Space d)))

/-- The inequality displayed in Corollary 10.1, in actual geometric volumes.
The power is the natural-number power; in particular x^0 = 1 for x = 0. -/
def ProjectionInequality {d : Nat} (K : ConvexBody (Space d)) : Prop :=
  fullVolume K * lineVolume K ^ (d - 1) <=
    ∏ j : Fin d, planeVolume K j

/-- The universally quantified assertion of Corollary 10.1.
This declaration states the target; it is not a proof of it. -/
def Corollary10_1 : Prop :=
  forall (d : Nat), 1 <= d -> forall (K : ConvexBody (Space d)),
    IsZonoid K -> ProjectionInequality K

/-- Every finite zonotope is a zonoid, directly from the closure definition. -/
theorem IsZonotope.isZonoid {d : Nat} {K : ConvexBody (Space d)}
    (hK : IsZonotope K) : IsZonoid K :=
  subset_closure hK

/-- Bridge to the paper's formulation: a zonoid is precisely the Hausdorff
limit of a sequence of finite zonotopes. `ConvexBody` uses the Hausdorff metric. -/
theorem isZonoid_iff_exists_zonotope_sequence {d : Nat}
    (K : ConvexBody (Space d)) :
    IsZonoid K ↔ ∃ Z : Nat -> ConvexBody (Space d),
      (forall n, IsZonotope (Z n)) ∧
        Filter.Tendsto Z Filter.atTop (nhds K) :=
  mem_closure_iff_seq_limit

/-- For d = 1 the sole coordinate plane is the entire ambient R^2. -/
theorem coordinatePlane_one_eq_top (j : Fin 1) :
    coordinatePlane 1 j = (⊤ : Submodule Real (Space 1)) := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  apply top_unique
  intro x hx
  change forall i : Fin 2, i ∉ {(0 : Fin 1).castSucc, Fin.last 1} -> x i = 0
  intro i hi
  fin_cases i <;> simp at hi

/-- At d = 1 the sole projected area is the ambient area. -/
theorem planeVolume_one (K : ConvexBody (Space 1)) (j : Fin 1) :
    planeVolume K j = fullVolume K := by
  unfold planeVolume coordinatePlaneProjection
  simp only [coordinatePlane_one_eq_top, Submodule.starProjection_top]
  change Measure.euclideanHausdorffMeasure 2
      ((fun x : Space 1 => x) '' (K : Set (Space 1))) = fullVolume K
  rw [Set.image_id']
  rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rfl

/-- The d = 1 case of Corollary 10.1, valid for every convex body.
No zonoid hypothesis is needed in this endpoint case. -/
theorem projectionInequality_one (K : ConvexBody (Space 1)) :
    ProjectionInequality K := by
  simp [ProjectionInequality, planeVolume_one]

end Cor101
