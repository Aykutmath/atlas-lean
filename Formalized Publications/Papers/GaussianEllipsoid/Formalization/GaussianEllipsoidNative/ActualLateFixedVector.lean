import ActualLateBranch

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- Triangle inequality for the concrete l1 coefficient mass. -/
theorem coefficientMass_le_sub_add {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    coefficientMass u ≤ coefficientMass (u-v) + coefficientMass v := by
  unfold coefficientMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [Pi.sub_apply, sub_add_cancel] using abs_add_le (u i-v i) (v i)

/-- Retention preserves at least one minus its proved omitted mass. -/
theorem retained_mass_ge_one_sub {n : ℕ} (u : Fin n → ℝ) (amp : ℝ)
    (groups : List (List ℕ)) (T : ℕ) (ε : ℝ)
    (hu : coefficientMass u = 1)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ ε) :
    1-ε ≤ coefficientMass (retainedGroupVector u amp groups T) := by
  have hh := coefficientMass_le_sub_add u (retainedGroupVector u amp groups T)
  rw [hu] at hh
  linarith

/-- The explicit Section 7 fixed-vector scale. -/
def multiscaleFixedConstant (K : ℝ) : ℝ :=
  (1/2:ℝ)^29 / (Real.sqrt (max K 1) * (1+Real.log (max K 1)))

/-- The explicit Section 7 uniform scale after a factor-two net extension. -/
def multiscaleConstant (K : ℝ) : ℝ :=
  (1/2:ℝ)^30 / (Real.sqrt (max K 1) * (1+Real.log (max K 1)))

theorem multiscaleFixedConstant_pos (K : ℝ) : 0 < multiscaleFixedConstant K := by
  unfold multiscaleFixedConstant
  exact div_pos (by positivity) (target_denominator_bounds (max K 1) (le_max_right _ _)).1

theorem multiscaleConstant_eq_half (K : ℝ) :
    multiscaleConstant K = multiscaleFixedConstant K / 2 := by
  unfold multiscaleConstant multiscaleFixedConstant
  norm_num
  ring

theorem multiscaleConstant_pos (K : ℝ) : 0 < multiscaleConstant K := by
  rw [multiscaleConstant_eq_half]
  exact div_pos (multiscaleFixedConstant_pos K) (by norm_num)

/-- The complete original-vector late-branch estimate at the target fixed
scale. Its hypotheses concern only the constructed deterministic decomposition;
the Gaussian probability follows from the actual sample law. -/
theorem actual_original_late_fixed_smallball {n d : ℕ}
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (ha : 0 < amp) (groups : List (List ℕ))
    (K : ℝ) (hK : 1 ≤ K) (T : ℕ) (hT : T = 40+4*⌈K⌉₊)
    (hreg : ∀ g ∈ groups, RegularRetainedGroup u amp T g)
    (hchain : groups.IsChain (RecordSuccessor fun t => (dyadicBin u amp t).card))
    (hflat : groups.flatten.Nodup) (hd : 65536*(T:ℝ) ≤ d)
    (hsupp : ((Finset.univ.filter fun i => u i ≠ 0).card:ℝ) ≤ K*d)
    (q : ℕ)
    (hq : SupportCutoff (dyadicGroupSize u amp groups T) groups.length ((d:ℝ)/256) q)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T)
    (hcapt : (∑ r ∈ Finset.range q, dyadicGroupMass u amp groups T r) <
      coefficientMass (retainedGroupVector u amp groups T)/2) :
    (gaussianBilinearSampleLaw (Fin n) (2*(d/4)) (2*(d/4))).real
      {X | spectralNuclearNorm (operatorFrobenius
        ((Real.sqrt (d:ℝ))⁻¹ • bilinearSynthesis u X)) <
        multiscaleFixedConstant K * Real.sqrt d} ≤
      Real.exp (-(d:ℝ)^2/(1048576*T)) := by
  let J := 17*(1+Real.log K)
  let ε := 8*(1/2:ℝ)^T
  let c := (1/2:ℝ)^24 / (Real.sqrt K*J)
  let M := coefficientMass (retainedGroupVector u amp groups T)
  have hTpos : 0 < T := by omega
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hJ : 0 < J := by dsimp [J]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hconstants := common_retained_tail_constants K J hK hJ (by rfl)
  rw [← hT] at hconstants
  change ε ≤ 1/8 ∧ 2*ε ≤ c/8 ∧ 3*c/4 ≤ c*(1-ε)-2*ε ∧
    (1/2:ℝ)^29/(Real.sqrt K*(1+Real.log K)) ≤ 3*c/4 ∧
    (1/2:ℝ)^29/(Real.sqrt K*(1+Real.log K)) ≤ c*(1-ε)-2*ε at hconstants
  have hM : 1-ε ≤ M := retained_mass_ge_one_sub u amp groups T ε hu herr
  have hMpos : 0 < M := by linarith [hconstants.1]
  have hdpos : (0:ℝ) < d := by
    have hTr : (0:ℝ) < T := by exact_mod_cast hTpos
    linarith
  have hcount := actual_late_group_count_le u amp ha groups K d hK hdpos hsupp T hT hreg hchain q hq
  have hp := actual_original_late_smallball u amp ha groups T hTpos hreg hchain hflat
    K J hK hJ hd hsupp q hq hcount hMpos hcapt
  have hthreshold : multiscaleFixedConstant K * Real.sqrt d ≤ c * Real.sqrt d * M := by
    have hf : multiscaleFixedConstant K ≤ c*M := by
      unfold multiscaleFixedConstant
      rw [max_eq_left hK]
      have hh := mul_le_mul_of_nonneg_left hM hc.le
      linarith [hconstants.2.2.2.2]
    convert! mul_le_mul_of_nonneg_right hf (Real.sqrt_nonneg (d:ℝ)) using 1 <;> ring
  apply (measureReal_mono (fun X (hX : _ < _) => hX.trans_le hthreshold)).trans
  simpa only [c, show (1/2:ℝ)^24 = 1/16777216 by norm_num, M] using! hp

end GaussianEllipsoidCandidate
