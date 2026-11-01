import Section_10_Zonoid.Hypercube.Sharpness
import Mathlib.Topology.Order.DenselyOrdered

/-!
Source Section 7.3: passing from ratios on the admissible positive epsilon
interval to a lower bound for every universal coefficient. The interval is
explicit, so continuity at zero does not silently include inadmissible laws.
-/

noncomputable section

open Filter Topology

namespace Hypercube.Optimality

theorem eventually_positive_lt (delta : Real) (hdelta : 0 < delta) :
    Filter.Eventually (fun eps : Real => And (0 < eps) (eps < delta))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  have hlt : Filter.Eventually (fun eps : Real => eps < delta)
      (nhdsWithin 0 (Set.Ioi 0)) :=
    (eventually_lt_nhds hdelta).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with eps hpositive hsmall
  exact And.intro hpositive hsmall

theorem limit_le_of_admissible_bound (ratio : Real -> Real)
    (L K delta : Real) (hdelta : 0 < delta)
    (hlimit : Tendsto ratio (nhdsWithin 0 (Set.Ioi 0)) (nhds L))
    (hbound : forall eps, 0 < eps -> eps < delta -> ratio eps <= K) :
    L <= K := by
  apply le_of_tendsto hlimit
  exact (eventually_positive_lt delta hdelta).mono
    (fun eps h => hbound eps h.1 h.2)

theorem mainCoefficient_le_of_admissible_ratios (d : Nat) (hd : 1 <= d)
    (K : Real)
    (hbound : forall eps : Real, 0 < eps -> eps < 1 / (d : Real) ->
      Sharpness.mainSpikeRatio d eps <= K) :
    Constants.mainCoefficient d <= K := by
  have hpositive : 0 < (d : Real) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  exact limit_le_of_admissible_bound (Sharpness.mainSpikeRatio d)
    (Constants.mainCoefficient d) K (1 / (d : Real))
    (one_div_pos.mpr hpositive) (Sharpness.mainSpikeRatio_limit_from_right d) hbound

theorem oneStepCoefficient_le_of_admissible_ratios (m : Nat) (K : Real)
    (hbound : forall eps : Real, 0 < eps -> eps < 1 / ((m + 1 : Nat) : Real) ->
      Sharpness.oneStepSpikeRatio m eps <= K) :
    Constants.oneStepCoefficient (m + 1) <= K := by
  have hpositive : 0 < ((m + 1 : Nat) : Real) := by positivity
  exact limit_le_of_admissible_bound (Sharpness.oneStepSpikeRatio m)
    (Constants.oneStepCoefficient (m + 1)) K (1 / ((m + 1 : Nat) : Real))
    (one_div_pos.mpr hpositive) (Sharpness.oneStepSpikeRatio_limit_from_right m) hbound

end Hypercube.Optimality
