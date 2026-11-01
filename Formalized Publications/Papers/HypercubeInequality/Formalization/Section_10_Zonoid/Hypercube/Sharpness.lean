import Section_10_Zonoid.Hypercube.Constants
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Source: Section 7.3. These are exact arithmetic and limit interfaces for
the displayed spike ratios. They do not prove the discrete-law expectations
or optimality of either universal probability inequality.
-/

noncomputable section

open Filter Topology

namespace Hypercube.Sharpness

def mainSpikeRatio (d : Nat) (eps : Real) : Real :=
  Constants.mainCoefficient d * (1 - (d : Real) * eps) / (1 - eps) ^ d

def oneStepSpikeRatio (m : Nat) (eps : Real) : Real :=
  Constants.oneStepCoefficient (m + 1) * (1 - ((m + 1 : Nat) : Real) * eps) /
    ((1 - eps) * (1 - (m : Real) * eps))

theorem mainSpikeRatio_at_zero (d : Nat) :
    mainSpikeRatio d 0 = Constants.mainCoefficient d := by
  simp [mainSpikeRatio]

theorem oneStepSpikeRatio_at_zero (m : Nat) :
    oneStepSpikeRatio m 0 = Constants.oneStepCoefficient (m + 1) := by
  simp [oneStepSpikeRatio]

theorem mainSpikeRatio_continuousAt_zero (d : Nat) :
    ContinuousAt (mainSpikeRatio d) 0 := by
  unfold mainSpikeRatio
  fun_prop (disch := norm_num)

theorem oneStepSpikeRatio_continuousAt_zero (m : Nat) :
    ContinuousAt (oneStepSpikeRatio m) 0 := by
  unfold oneStepSpikeRatio
  fun_prop (disch := norm_num)

theorem mainSpikeRatio_limit_from_right (d : Nat) :
    Tendsto (mainSpikeRatio d) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Constants.mainCoefficient d)) := by
  have h := (mainSpikeRatio_continuousAt_zero d).tendsto
  rw [mainSpikeRatio_at_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem oneStepSpikeRatio_limit_from_right (m : Nat) :
    Tendsto (oneStepSpikeRatio m) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Constants.oneStepCoefficient (m + 1))) := by
  have h := (oneStepSpikeRatio_continuousAt_zero m).tendsto
  rw [oneStepSpikeRatio_at_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem main_spike_quotient (d : Nat) (eps : Real)
    (heps : Not (eps = 0)) (hone : Not (1 - eps = 0)) :
    (((d + 1 : Nat) : Real) * (1 - (d : Real) * eps) * eps ^ d) /
        (2 * eps * (1 - eps)) ^ d = mainSpikeRatio d eps := by
  have hpow : Not (eps ^ d = 0) := pow_ne_zero d heps
  have hden : Not ((1 - eps) ^ d = 0) := pow_ne_zero d hone
  have htwo : Not ((2 : Real) ^ d = 0) := by positivity
  simp only [mainSpikeRatio, Constants.mainCoefficient, mul_pow]
  field_simp

end Hypercube.Sharpness
