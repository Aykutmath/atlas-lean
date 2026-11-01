import Section_10_Zonoid.Hypercube.EndpointAssembly
import Section_10_Zonoid.Hypercube.Approximation
import Section_10_Zonoid.Hypercube.CubeEndpoint

/-!
Paper-facing endpoint theorems for `source/hypercube_readable.tex`.
Every premise is a premise of the corresponding source theorem. The signed
simplex, binary label, arbitrary-height and approximation arguments are proved
in the imported modules; no gate or geometric identity is assumed here.
Sharpness is a separate assertion, covered by the sharpness modules.
-/

noncomputable section

namespace Hypercube.Main

open MeasureTheory

/-- The source universal levelwise gate, with all mathematical premises discharged. -/
theorem levelwiseBernoulli {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    EndpointAssembly.levelwiseBernoulliClaim nu := by
  intro t
  exact Approximation.global_levelwise_bernoulli_gate nu hfirst t

/-- The arbitrary-height estimate of source equation (OTgate). -/
theorem height_cost_chain {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    And (EndpointAssembly.sampledHeightObjective nu <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => EndpointAssembly.sampledThresholdCost z))
      (integral (Measure.pi (fun _ : Fin (m + 2) => nu))
          (fun z => EndpointAssembly.sampledThresholdCost z) <=
        EndpointAssembly.expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m)) :=
  EndpointAssembly.sampled_height_cost_chain_of_levelwise nu hfirst (levelwiseBernoulli nu hfirst)

/-- The exact source one-step theorem, dimension d=m+1. -/
theorem one_step {m : Nat} (hm : 1 <= m)
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.expectedSimplexVolume nu <=
      ((m + 2 : Nat) : Real) / (2 * ((m + 1 : Nat) : Real)) *
        Paper.coordinateGap nu (Fin.last m) *
          Paper.expectedSimplexVolume (nu.map Paper.projectLast) := by
  have hdimension : 1 <= m := hm
  exact EndpointAssembly.oneStep_of_levelwise nu hfirst (levelwiseBernoulli nu hfirst)

/-- Explicit indexing bridge to the source quantifier d>=2 and projection R^d -> R^(d-1). -/
theorem one_step_dimension (d : Nat) (hd : 2 <= d)
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.expectedSimplexVolume nu <=
      ((d + 1 : Nat) : Real) / (2 * (d : Real)) *
        Paper.coordinateGap nu (Fin.mk (d - 1) (by omega)) *
          Paper.expectedSimplexVolume (nu.map (fun z : Paper.Point d =>
            fun j : Fin (d - 1) => z (Fin.mk j.val (by omega)))) := by
  revert nu
  cases d with
  | zero => omega
  | succ d =>
      cases d with
      | zero => omega
      | succ m =>
          intro nu hprob hfirst
          change Paper.expectedSimplexVolume nu <=
            ((m + 3 : Nat) : Real) / (2 * ((m + 2 : Nat) : Real)) *
              Paper.coordinateGap nu (Fin.last (m + 1)) *
                Paper.expectedSimplexVolume (nu.map Paper.projectLast)
          exact one_step (m := m + 1) (by omega) nu hfirst

/-- Source Theorem 1.3 in the governed paper representation. -/
theorem all_dimensions_one_step : Paper.allDimensionsOneStep := by
  intro m hm nu hprob hfirst
  let _ := hprob
  exact one_step hm nu hfirst

/-- Source Theorem 1.2, in its governed paper representation. -/
theorem all_dimensions_random_simplex : Paper.allDimensionsRandomSimplex :=
  EndpointAssembly.all_dimensions_random_simplex_of_oneStep all_dimensions_one_step

/-- The literal source random-simplex inequality for an arbitrary probability law. -/
theorem random_simplex (d : Nat) (hd : 1 <= d)
    (nu : Measure (Paper.Point d)) [IsProbabilityMeasure nu]
    (hfirst : Paper.finiteCoordinateFirstMoments nu) :
    Paper.expectedSimplexVolume nu <=
      ((d + 1 : Nat) : Real) / (2 : Real) ^ d *
        Finset.prod Finset.univ (fun j => Paper.coordinateGap nu j) :=
  all_dimensions_random_simplex d hd nu inferInstance hfirst

/-- The original Hypercube inequality, including nonnegative zero weights. -/
theorem all_dimensions_hypercube : Paper.allDimensionsHypercube :=
  CubeEndpoint.hypercube_of_randomSimplex all_dimensions_random_simplex

/-- The literal weighted-vertex formulation in source equation (cube). -/
theorem hypercube (d : Nat) (hd : 1 <= d) (x : Paper.Cube d -> Real)
    (hx : forall v, 0 <= x v) :
    Paper.cubeSimplexSum x * Paper.totalWeight x ^ (d - 1) <=
      Finset.prod Finset.univ (fun j =>
        Paper.facetWeight x j false * Paper.facetWeight x j true) :=
  all_dimensions_hypercube d hd x hx

end Hypercube.Main
