import Section_10_Zonoid.Hypercube.SpikeLaw.Gaps
import Section_10_Zonoid.Hypercube.SpikeLaw.Volume
import Section_10_Zonoid.Hypercube.SpikeLaw.Projection
import Section_10_Zonoid.Hypercube.SpikeLaw.Cube
import Section_10_Zonoid.Hypercube.Optimality

/- Source Section 7.3. Every ratio in this file refers to the actual atomic
probability law and the paper's geometric simplex volume and coordinate
gap. The positive epsilon guard excludes division by a zero sharpness
denominator; limits use eventual equality only on admissible laws. -/

noncomputable section

open MeasureTheory Filter Topology

namespace Hypercube.SpikeLaw

theorem admissible_eps_product (d : Nat) (hd : 1 <= d) (eps : Real)
    (hsmall : eps < 1 / (d : Real)) : (d : Real) * eps < 1 := by
  have hdpos : 0 < (d : Real) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have h := mul_lt_mul_of_pos_left hsmall hdpos
  have hid : (d : Real) * (1 / (d : Real)) = 1 := by field_simp
  simpa only [hid] using h

theorem admissible_eps_lt_one (d : Nat) (hd : 1 <= d) (eps : Real)
    (_heps : 0 < eps) (hsmall : eps < 1 / (d : Real)) : eps < 1 := by
  have hp := admissible_eps_product d hd eps hsmall
  have hd' : (1 : Real) <= (d : Real) := by exact_mod_cast hd
  nlinarith

theorem spike_main_ratio (d : Nat) (hd : 1 <= d) (eps : Real)
    (heps : 0 < eps) (hsmall : eps < 1 / (d : Real)) :
    Paper.expectedSimplexVolume (spikeLaw d eps) /
      Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j) =
      Sharpness.mainSpikeRatio d eps := by
  have hprod := (admissible_eps_product d hd eps hsmall).le
  have hlt := admissible_eps_lt_one d hd eps heps hsmall
  have hone : 0 < 1 - eps := sub_pos.mpr hlt
  rw [spike_expectedSimplexVolume d eps heps.le hprod,
    spike_coordinateGap_product d eps heps.le hprod]
  exact Sharpness.main_spike_quotient d eps heps.ne' (sub_pos.mpr hlt).ne'

theorem spike_main_ratio_limit (d : Nat) (hd : 1 <= d) :
    Tendsto (fun eps : Real => Paper.expectedSimplexVolume (spikeLaw d eps) /
      Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Constants.mainCoefficient d)) := by
  have hdpos : 0 < (d : Real) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  apply (Sharpness.mainSpikeRatio_limit_from_right d).congr'
  apply (Optimality.eventually_positive_lt (1 / (d : Real)) (one_div_pos.mpr hdpos)).mono
  intro eps heps
  exact (spike_main_ratio d hd eps heps.1 heps.2).symm

theorem main_coefficient_bound_of_spike_comparisons (d : Nat) (hd : 1 <= d) (K : Real)
    (hbound : forall eps : Real, 0 < eps -> eps < 1 / (d : Real) ->
      Paper.expectedSimplexVolume (spikeLaw d eps) <=
        K * Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j)) :
    Constants.mainCoefficient d <= K := by
  apply Optimality.mainCoefficient_le_of_admissible_ratios d hd K
  intro eps heps hsmall
  have hprod := (admissible_eps_product d hd eps hsmall).le
  have hlt := admissible_eps_lt_one d hd eps heps hsmall
  have hden : 0 < Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j) := by
    rw [spike_coordinateGap_product d eps heps.le hprod]
    positivity
  have hdiv := div_le_div_of_nonneg_right (hbound eps heps hsmall) hden.le
  have hid :
      (K * Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j)) /
        Finset.prod Finset.univ (fun j => Paper.coordinateGap (spikeLaw d eps) j) = K := by
    field_simp
  rw [hid, spike_main_ratio d hd eps heps hsmall] at hdiv
  exact hdiv

theorem mainCoefficientIsOptimal (d : Nat) (hd : 1 <= d) :
    Paper.mainCoefficientIsOptimal d := by
  intro K hK
  apply main_coefficient_bound_of_spike_comparisons d hd K
  intro eps heps hsmall
  have hprod := (admissible_eps_product d hd eps hsmall).le
  exact hK (spikeLaw d eps) (spikeLaw_isProbability d eps heps.le hprod)
    (spikeLaw_firstMoments d eps)

theorem mainCoefficientIsOptimalForCubeLaws (d : Nat) (hd : 1 <= d) :
    Paper.mainCoefficientIsOptimalForCubeLaws d := by
  intro K hK
  apply main_coefficient_bound_of_spike_comparisons d hd K
  intro eps heps hsmall
  have hprod := (admissible_eps_product d hd eps hsmall).le
  have h := hK (spikeCubeLaw d eps) (spikeCubeLaw_isProbability d eps heps.le hprod)
  simpa only [spikeCubeLaw_pushforward] using h

theorem allDimensionsMainSharpness : Paper.allDimensionsCubeSharpness :=
  fun d hd => mainCoefficientIsOptimalForCubeLaws d hd

theorem oneStep_spike_quotient (m : Nat) (eps : Real)
    (heps : Not (eps = 0)) (hone : Not (1 - eps = 0))
    (hm : Not (1 - (m : Real) * eps = 0)) :
    (((m + 2 : Nat) : Real) * (1 - ((m + 1 : Nat) : Real) * eps) * eps ^ (m + 1)) /
      ((2 * eps * (1 - eps)) * (((m + 1 : Nat) : Real) *
        (1 - (m : Real) * eps) * eps ^ m)) = Sharpness.oneStepSpikeRatio m eps := by
  have hpow : Not (eps ^ m = 0) := pow_ne_zero m heps
  have hmpos : 0 < ((m + 1 : Nat) : Real) := by positivity
  simp only [Sharpness.oneStepSpikeRatio, Constants.oneStepCoefficient,
    Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

theorem spike_oneStep_ratio (m : Nat) (eps : Real)
    (heps : 0 < eps) (hsmall : eps < 1 / ((m + 1 : Nat) : Real)) :
    Paper.expectedSimplexVolume (spikeLaw (m + 1) eps) /
      (Paper.coordinateGap (spikeLaw (m + 1) eps) (Fin.last m) *
        Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast)) =
      Sharpness.oneStepSpikeRatio m eps := by
  have hd : 1 <= m + 1 := by omega
  have hprod := admissible_eps_product (m + 1) hd eps hsmall
  have hlt := admissible_eps_lt_one (m + 1) hd eps heps hsmall
  have hmpos : 0 < 1 - (m : Real) * eps := by push_cast at hprod; nlinarith
  rw [spike_expectedSimplexVolume (m + 1) eps heps.le hprod.le,
    spike_coordinateGap (m + 1) eps heps.le hprod.le (Fin.last m),
    spike_projected_expectedSimplexVolume m eps heps.le hprod.le]
  exact oneStep_spike_quotient m eps heps.ne' (sub_pos.mpr hlt).ne' hmpos.ne'

theorem spike_oneStep_ratio_limit (m : Nat) :
    Tendsto (fun eps : Real => Paper.expectedSimplexVolume (spikeLaw (m + 1) eps) /
      (Paper.coordinateGap (spikeLaw (m + 1) eps) (Fin.last m) *
        Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Constants.oneStepCoefficient (m + 1))) := by
  have hdpos : 0 < ((m + 1 : Nat) : Real) := by positivity
  apply (Sharpness.oneStepSpikeRatio_limit_from_right m).congr'
  apply (Optimality.eventually_positive_lt (1 / ((m + 1 : Nat) : Real)) (one_div_pos.mpr hdpos)).mono
  intro eps heps
  exact (spike_oneStep_ratio m eps heps.1 heps.2).symm

theorem oneStepCoefficientIsOptimal (m : Nat) : Paper.oneStepCoefficientIsOptimal m := by
  intro K hK
  apply Optimality.oneStepCoefficient_le_of_admissible_ratios m K
  intro eps heps hsmall
  have hd : 1 <= m + 1 := by omega
  have hprod := admissible_eps_product (m + 1) hd eps hsmall
  have hlt := admissible_eps_lt_one (m + 1) hd eps heps hsmall
  have hone : 0 < 1 - eps := sub_pos.mpr hlt
  have hmpos : 0 < 1 - (m : Real) * eps := by push_cast at hprod; nlinarith
  have hden : 0 < Paper.coordinateGap (spikeLaw (m + 1) eps) (Fin.last m) *
      Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast) := by
    rw [spike_coordinateGap (m + 1) eps heps.le hprod.le (Fin.last m),
      spike_projected_expectedSimplexVolume m eps heps.le hprod.le]
    positivity
  have h := hK (spikeLaw (m + 1) eps) (spikeLaw_isProbability (m + 1) eps heps.le hprod.le)
    (spikeLaw_firstMoments (m + 1) eps)
  have h' : Paper.expectedSimplexVolume (spikeLaw (m + 1) eps) <= K *
      (Paper.coordinateGap (spikeLaw (m + 1) eps) (Fin.last m) *
        Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast)) := by
    simpa only [mul_assoc] using h
  have hdiv := div_le_div_of_nonneg_right h' hden.le
  have hid :
      (K * (Paper.coordinateGap (spikeLaw (m + 1) eps) (Fin.last m) *
        Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast))) /
        (Paper.coordinateGap (spikeLaw (m + 1) eps) (Fin.last m) *
          Paper.expectedSimplexVolume ((spikeLaw (m + 1) eps).map Paper.projectLast)) = K := by
    apply (div_eq_iff hden.ne').mpr
    ring
  rw [hid, spike_oneStep_ratio m eps heps hsmall] at hdiv
  exact hdiv

theorem allDimensionsOneStepSharpness : Paper.allDimensionsOneStepSharpness :=
  fun m _ => oneStepCoefficientIsOptimal m

end Hypercube.SpikeLaw
