import Section_10_Zonoid.Hypercube.Constants
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Powerset

/-!
Paper-facing definitions for `source/hypercube_readable.tex`.
These declarations encode statements; they do not prove the conjecture.
`Point d` uses the coordinate model of R^d. Its Mathlib `volume` is the
product Lebesgue measure. Sample independence is represented by `Measure.pi`.
The bridge to arbitrary iid random variables is a separate proof obligation.
-/

noncomputable section

open MeasureTheory

namespace Hypercube.Paper

abbrev Point (d : Nat) := Fin d -> Real
abbrev Cube (d : Nat) := Fin d -> Bool

def cubePoint {d : Nat} (v : Cube d) : Point d :=
  fun j => if v j then 1 else 0

/-- Ordinary volume, without a factorial; source lines 109-112. -/
def simplexVolume {d : Nat} (z : Fin (d + 1) -> Point d) : Real :=
  (volume (convexHull Real (Set.range z))).toReal

def expectedSimplexVolume {d : Nat} (nu : Measure (Point d)) : Real :=
  integral (Measure.pi (fun _ : Fin (d + 1) => nu))
    (fun z => simplexVolume z)

/-- Two separate samples, with unrestricted dependence inside each point. -/
def coordinateGap {d : Nat} (nu : Measure (Point d)) (j : Fin d) : Real :=
  integral (nu.prod nu) (fun zz => abs (zz.1 j - zz.2 j))

/-- Exactly the finite first absolute coordinate moments in Theorem 1.2. -/
def finiteCoordinateFirstMoments {d : Nat} (nu : Measure (Point d)) : Prop :=
  forall j : Fin d, Integrable (fun z => abs (z j)) nu

abbrev mainCoefficient := Hypercube.Constants.mainCoefficient

def randomSimplexClaim (d : Nat) (nu : Measure (Point d)) : Prop :=
  expectedSimplexVolume nu <= mainCoefficient d *
    Finset.univ.prod (fun j => coordinateGap nu j)

/-- A proposition recording the main endpoint, not an assumed theorem. -/
def allDimensionsRandomSimplex : Prop :=
  forall (d : Nat), 1 <= d ->
    forall (nu : Measure (Point d)), IsProbabilityMeasure nu ->
      finiteCoordinateFirstMoments nu -> randomSimplexClaim d nu

def projectLast {m : Nat} (z : Point (m + 1)) : Point m :=
  fun j => z j.castSucc

/-- Theorem 1.3, with d=m+1 and the last coordinate indexed by Fin.last m. -/
def oneStepClaim (m : Nat) (nu : Measure (Point (m + 1))) : Prop :=
  expectedSimplexVolume nu <=
    ((m + 2 : Nat) : Real) / (2 * ((m + 1 : Nat) : Real)) *
      coordinateGap nu (Fin.last m) *
        expectedSimplexVolume (Measure.map projectLast nu)

def allDimensionsOneStep : Prop :=
  forall (m : Nat), 1 <= m ->
    forall (nu : Measure (Point (m + 1))), IsProbabilityMeasure nu ->
      finiteCoordinateFirstMoments nu -> oneStepClaim m nu

def totalWeight {d : Nat} (x : Cube d -> Real) : Real :=
  Finset.univ.sum x

def facetWeight {d : Nat} (x : Cube d -> Real) (j : Fin d) (b : Bool) : Real :=
  (Finset.univ.filter (fun v => v j = b)).sum x

/-- Capitalized Vol in the paper: factorial times ordinary volume. -/
def normalizedCubeVolume {d : Nat} (s : Finset (Cube d)) : Real :=
  (Nat.factorial d : Real) *
    (volume (convexHull Real (cubePoint '' (s : Set (Cube d))))).toReal

def cubeSimplexSum {d : Nat} (x : Cube d -> Real) : Real :=
  (Finset.univ.powersetCard (d + 1)).sum
    (fun s => normalizedCubeVolume s * s.prod x)

/-- The weighted vertex inequality, preserving the all-zero endpoint. -/
def weightedCubeClaim (d : Nat) (x : Cube d -> Real) : Prop :=
  cubeSimplexSum x * totalWeight x ^ (d - 1) <=
    Finset.univ.prod (fun j => facetWeight x j false * facetWeight x j true)

def allDimensionsHypercube : Prop :=
  forall (d : Nat), 1 <= d ->
    forall (x : Cube d -> Real), (forall v, 0 <= x v) -> weightedCubeClaim d x

/-- Sharpness must also be proved; this records its quantifiers explicitly. -/
def mainCoefficientIsOptimal (d : Nat) : Prop :=
  forall (K : Real),
    (forall (nu : Measure (Point d)), IsProbabilityMeasure nu ->
      finiteCoordinateFirstMoments nu ->
      expectedSimplexVolume nu <= K *
        Finset.univ.prod (fun j => coordinateGap nu j)) -> mainCoefficient d <= K

/-- The stronger paper assertion: sharpness within cube-supported laws.
The map from Boolean vertices to coordinate points is explicit. Finite first
moments of this pushforward must be proved as a separate bridge. -/
def mainCoefficientIsOptimalForCubeLaws (d : Nat) : Prop :=
  forall (K : Real),
    (forall (q : Measure (Cube d)), IsProbabilityMeasure q ->
      let nu := Measure.map cubePoint q
      expectedSimplexVolume nu <= K *
        Finset.univ.prod (fun j => coordinateGap nu j)) -> mainCoefficient d <= K

def allDimensionsCubeSharpness : Prop :=
  forall (d : Nat), 1 <= d -> mainCoefficientIsOptimalForCubeLaws d

/-- The separate sharpness assertion in Theorem 1.3, with d=m+1. -/
def oneStepCoefficientIsOptimal (m : Nat) : Prop :=
  forall (K : Real),
    (forall (nu : Measure (Point (m + 1))), IsProbabilityMeasure nu ->
      finiteCoordinateFirstMoments nu ->
      expectedSimplexVolume nu <= K * coordinateGap nu (Fin.last m) *
        expectedSimplexVolume (Measure.map projectLast nu)) ->
      ((m + 2 : Nat) : Real) / (2 * ((m + 1 : Nat) : Real)) <= K

def allDimensionsOneStepSharpness : Prop :=
  forall (m : Nat), 1 <= m -> oneStepCoefficientIsOptimal m

end Hypercube.Paper
