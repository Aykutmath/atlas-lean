import Section_10_Zonoid.Hypercube.Main
import Section_10_Zonoid.Hypercube.SpikeLaw.Optimality

/-!
The source theorems include optimality as well as an inequality. These
paper-facing endpoints combine those two checked assertions; the stronger
cube-supported optimality quantifier is retained for the random-simplex result.
-/

noncomputable section

namespace Hypercube.PaperTheorems

open MeasureTheory

/-- Source Theorem 1.2, including its cube-supported sharpness assertion. -/
theorem random_simplex (d : Nat) (hd : 1 <= d) :
    And (forall (nu : Measure (Paper.Point d)), IsProbabilityMeasure nu ->
      Paper.finiteCoordinateFirstMoments nu ->
        Paper.expectedSimplexVolume nu <=
          ((d + 1 : Nat) : Real) / (2 : Real) ^ d *
            Finset.prod Finset.univ (fun j => Paper.coordinateGap nu j))
      (Paper.mainCoefficientIsOptimalForCubeLaws d) := by
  constructor
  next =>
    intro nu hprob hfirst
    let _ := hprob
    exact Main.random_simplex d hd nu hfirst
  next => exact SpikeLaw.mainCoefficientIsOptimalForCubeLaws d hd

/-- Source Theorem 1.3, with the explicit dimension bridge d=m+1. -/
theorem one_step (m : Nat) (hm : 1 <= m) :
    And (forall (nu : Measure (Paper.Point (m + 1))), IsProbabilityMeasure nu ->
      Paper.finiteCoordinateFirstMoments nu ->
        Paper.expectedSimplexVolume nu <=
          ((m + 2 : Nat) : Real) / (2 * ((m + 1 : Nat) : Real)) *
            Paper.coordinateGap nu (Fin.last m) *
              Paper.expectedSimplexVolume (nu.map Paper.projectLast))
      (Paper.oneStepCoefficientIsOptimal m) := by
  constructor
  next =>
    intro nu hprob hfirst
    let _ := hprob
    exact Main.one_step hm nu hfirst
  next => exact SpikeLaw.oneStepCoefficientIsOptimal m

/-- All three source inequalities and both source optimality assertions. -/
theorem all_main_results :
    And Paper.allDimensionsHypercube
      (And Paper.allDimensionsRandomSimplex
        (And Paper.allDimensionsOneStep
          (And Paper.allDimensionsCubeSharpness Paper.allDimensionsOneStepSharpness))) :=
  And.intro Main.all_dimensions_hypercube
    (And.intro Main.all_dimensions_random_simplex
      (And.intro Main.all_dimensions_one_step
        (And.intro SpikeLaw.allDimensionsMainSharpness SpikeLaw.allDimensionsOneStepSharpness)))

end Hypercube.PaperTheorems
