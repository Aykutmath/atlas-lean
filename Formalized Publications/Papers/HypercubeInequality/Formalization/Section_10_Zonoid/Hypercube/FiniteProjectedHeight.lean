import Section_10_Zonoid.Hypercube.EndpointAssembly
import Section_10_Zonoid.Hypercube.Approximation

/- The literal finite projected-law height statement assumes only the first
height moment. The projected coordinate moments follow from finite support;
they are proved here rather than imposed as additional hypotheses. -/

noncomputable section

namespace Hypercube.FiniteProjectedHeight

open MeasureTheory

theorem projected_coordinate_integrable_of_finite_law {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (s : Set (Paper.Point m)) (hfinite : Set.Finite s)
    (hsupport : (nu.map Paper.projectLast) s = 1) (j : Fin m) :
    Integrable (fun z => |z j.castSucc|) nu := by
  classical
  have hproject : Measurable (Paper.projectLast : Paper.Point (m + 1) -> Paper.Point m) :=
    Moments.projectLast_continuous.measurable
  have : IsProbabilityMeasure (nu.map Paper.projectLast) :=
    (Measure.isProbabilityMeasure_map_iff hproject.aemeasurable).mpr inferInstance
  have hmem : Membership.mem (ae (nu.map Paper.projectLast)) s :=
    (mem_ae_iff_prob_eq_one hfinite.measurableSet).mpr hsupport
  have hpoint : Filter.Eventually (fun z => Membership.mem s (Paper.projectLast z)) (ae nu) :=
    (Measure.tendsto_ae_map hproject.aemeasurable).eventually hmem
  let bound : Real := Finset.sum hfinite.toFinset (fun w => |w j|)
  have hcoord : Measurable (fun z : Paper.Point (m + 1) => |z j.castSucc|) :=
    continuous_abs.measurable.comp (measurable_pi_apply j.castSucc)
  apply (integrable_const bound).mono_nonneg hcoord.aestronglyMeasurable
  next => exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
  next =>
    apply hpoint.mono
    intro z hz
    change |Paper.projectLast z j| <= bound
    exact Finset.single_le_sum (fun w _ => abs_nonneg (w j))
      (hfinite.mem_toFinset.mpr hz)

theorem firstMoments_of_finite_projected_law {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (s : Set (Paper.Point m)) (hfinite : Set.Finite s)
    (hsupport : (nu.map Paper.projectLast) s = 1)
    (hheight : Integrable (fun z => z (Fin.last m)) nu) :
    Paper.finiteCoordinateFirstMoments nu := by
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  next => exact hheight.abs
  next j => exact projected_coordinate_integrable_of_finite_law nu s hfinite hsupport j

/-- Source finite projected-law lifting: there is no extra projected moment assumption. -/
theorem finite_projected_law_height_cost_chain {m : Nat}
    (nu : Measure (Paper.Point (m + 1))) [IsProbabilityMeasure nu]
    (s : Set (Paper.Point m)) (hfinite : Set.Finite s)
    (hsupport : (nu.map Paper.projectLast) s = 1)
    (hheight : Integrable (fun z => z (Fin.last m)) nu) :
    And (EndpointAssembly.sampledHeightObjective nu <=
      integral (Measure.pi (fun _ : Fin (m + 2) => nu))
        (fun z => EndpointAssembly.sampledThresholdCost z))
      (integral (Measure.pi (fun _ : Fin (m + 2) => nu))
          (fun z => EndpointAssembly.sampledThresholdCost z) <=
        EndpointAssembly.expectedRadonMass nu * Paper.coordinateGap nu (Fin.last m)) := by
  have hfirst := firstMoments_of_finite_projected_law nu s hfinite hsupport hheight
  exact EndpointAssembly.sampled_height_cost_chain_of_levelwise nu hfirst
    (fun t => Approximation.global_levelwise_bernoulli_gate nu hfirst t)

end Hypercube.FiniteProjectedHeight
