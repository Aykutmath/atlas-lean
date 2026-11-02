import ActualLateFixedVector
import ActualUniformExtension
import ProjectedClusterArithmetic

noncomputable section
open MeasureTheory GaussianMixedNormHelpers GaussianEllipsoid
open scoped BigOperators
namespace GaussianEllipsoidCandidate

/-- The atom event and the proved omitted mass reduce original-vector failure
to actual retained-vector failure, with the fixed target unchanged. -/
theorem actual_fixed_failure_subset_retained {n d h : ℕ}
    (u : Fin n → ℝ) (hu : coefficientMass u = 1)
    (amp : ℝ) (groups : List (List ℕ))
    (K J : ℝ) (hK : 1 ≤ K) (hJ : 0 < J) (hJup : J ≤ 17*(1+Real.log K))
    (T : ℕ) (hT : T = 40+4*⌈K⌉₊)
    (herr : coefficientMass (u-retainedGroupVector u amp groups T) ≤ 8*(1/2:ℝ)^T) :
    {X : Fin n → Euclid h × Euclid h |
      scaledBilinearNuclear d u X < multiscaleFixedConstant K * Real.sqrt d} ∩ atomRowsGood d n h ⊆
    {X | scaledBilinearNuclear d (retainedGroupVector u amp groups T) X <
      ((1/2:ℝ)^24/(Real.sqrt K*J))*Real.sqrt d*
        coefficientMass (retainedGroupVector u amp groups T)} := by
  let V := retainedGroupVector u amp groups T
  let M := coefficientMass V
  let ε := 8*(1/2:ℝ)^T
  let c := (1/2:ℝ)^24/(Real.sqrt K*J)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hK0 : 0 < K := by linarith
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hc : 0 < c := by dsimp [c]; positivity
  have hconstants := common_retained_tail_constants K J hK hJ hJup
  rw [← hT] at hconstants
  have hfinal : multiscaleFixedConstant K ≤ c*(1-ε)-2*ε := by
    unfold multiscaleFixedConstant
    rw [max_eq_left hK]
    exact hconstants.2.2.2.2
  have hM : 1-ε ≤ M := retained_mass_ge_one_sub u amp groups T ε hu herr
  rintro X ⟨hbad, hatom⟩
  have herror : scaledBilinearNuclear d (u-V) X ≤ Real.sqrt d*ε :=
    (scaledBilinearNuclear_le_mass hatom (u-V)).trans
      (mul_le_mul_of_nonneg_left herr (Real.sqrt_nonneg _))
  have htri := scaledBilinearNuclear_sub_le (d:=d) u V X
  have hscale : multiscaleFixedConstant K*Real.sqrt d + Real.sqrt d*ε ≤ c*Real.sqrt d*M := by
    have h1 := mul_le_mul_of_nonneg_right hfinal (Real.sqrt_nonneg (d:ℝ))
    have h2 := mul_le_mul_of_nonneg_left hM hc.le
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg (d:ℝ))
    nlinarith [mul_nonneg hε (Real.sqrt_nonneg (d:ℝ))]
  exact lt_of_le_of_lt htri ((add_lt_add_of_lt_of_le hbad herror).trans_le hscale)

/-- Conservative captured-mass arithmetic: measurable half polar witnesses
and the chosen cross threshold still dominate the common retained constant. -/
theorem captured_mass_cross_absorption (K J d M Mc N : ℝ)
    (hK : 1 ≤ K) (hJ : 1 ≤ J) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hcapt : M/2 ≤ Mc)
    (hN : GaussianEllipsoid.ProjectedClusters.projectedConstant/2 * Real.sqrt d * Mc -
      (1/2:ℝ)^24*M*Real.sqrt d ≤ N) :
    ((1/2:ℝ)^24/(Real.sqrt K*J))*Real.sqrt d*M ≤ N := by
  have hsK : 1 ≤ Real.sqrt K := by simpa using Real.sqrt_le_sqrt hK
  have hden : 1 ≤ Real.sqrt K*J := by nlinarith
  have hdenpos : 0 < Real.sqrt K*J := by linarith
  have hc : (1/2:ℝ)^24/(Real.sqrt K*J) ≤ (1/2:ℝ)^24 := by
    apply (div_le_iff₀ hdenpos).mpr
    nlinarith [show (0:ℝ) ≤ (1/2)^24 by positivity]
  have h2 : Real.sqrt (2:ℝ) ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  have h2pos : 0 < Real.sqrt (2:ℝ) := by positivity
  have hp : (1/2:ℝ)^21 ≤ GaussianEllipsoid.ProjectedClusters.projectedConstant/2 := by
    unfold GaussianEllipsoid.ProjectedClusters.projectedConstant
    rw [div_div]
    apply (le_div_iff₀ (by positivity : 0 < (524288*Real.sqrt (2:ℝ))*2)).mpr
    norm_num
    nlinarith
  have hMc : 0 ≤ Mc := by linarith
  have hdiag := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg d)) hMc
  have hcap := mul_le_mul_of_nonneg_left hcapt
    (show 0 ≤ (1/2:ℝ)^21*Real.sqrt d by positivity)
  have hcM := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg d)) hM
  have hsM : 0 ≤ Real.sqrt d*M := by positivity
  norm_num at hdiag hcap hcM ⊢
  nlinarith

end GaussianEllipsoidCandidate
