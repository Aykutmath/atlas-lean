import AHHActualGaussianLogSobolev
import AHHAngularCutoffGradient
import AHHProductCutoffEnergy
import AHHNormalizedAngularIntegral
import AHHSphereEntropyApproximation

/-! Unconditional smooth-angular entropy inequality, obtained from the exact
Gaussian log-Sobolev theorem using the constructed radial cutoffs and their
proved vanishing energy. No log-Sobolev or approximation estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers Filter
open AHHEntropyLimitClosure
open scoped BigOperators ContDiff Topology
namespace AHHRadial

theorem sphereAmbientGaussian_probability (n h : ℕ) (hh : 0 < h) :
    IsProbabilityMeasure (sphereAmbientGaussianLaw n h) := by
  rw [sphereAmbientGaussianLaw_eq_scaled_stdGaussian n h hh]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem smooth_angular_gaussian_entropy_le (n h : ℕ) (hh : 2 ≤ h)
    (g : SphereAmbient n h → ℝ) (hg : ContDiff ℝ ∞ g)
    (hLip : LipschitzWith 1 g) (hlo : ∀ z, 1 ≤ g z)
    (hhi : ∀ z, g z ≤ Real.sqrt n) (p : ℝ) :
    entropy (sphereAmbientGaussianLaw n h)
      (fun z => (g (blockNormalize z)^p)^2) ≤
      (1 / (h : ℝ)) * ∫ z,
        ‖fderiv ℝ (fun y => g (blockNormalize y)^p) z‖^2
          ∂sphereAmbientGaussianLaw n h := by
  letI : NeZero h := ⟨by omega⟩
  have hh0 : 0 < h := by omega
  letI := sphereAmbientGaussian_probability n h hh0
  let P := sphereAmbientGaussianLaw n h
  let H := fun z : SphereAmbient n h => g (blockNormalize z)^p
  let Hk := fun k : ℕ => cutoffAngularPower (ι := Fin n × Bool) (E := CE h) k g p
  let I : ℝ := ∫ z, ‖fderiv ℝ H z‖^2 ∂P
  let J := fun k : ℕ => ∫ z : SphereAmbient n h,
    ‖fderiv ℝ (blockRadialCutoff (ι := Fin n × Bool) (E := CE h) k) z‖^2 ∂P
  let c := Real.exp (-(|Real.log (Real.sqrt n)| * |p|))
  let B := Real.exp (|Real.log (Real.sqrt n)| * |p|)
  let K := (Real.sqrt (n : ℝ))^|p| + 1
  have hc : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hB1 : 1 ≤ B := Real.one_le_exp_iff.mpr (by positivity)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpos : ∀ z, 0 < g z := fun z => lt_of_lt_of_le zero_lt_one (hlo z)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hpbound (z : SphereAmbient n h) : c ≤ g z^p ∧ g z^p ≤ B :=
    rpow_bounds_of_one_le (hlo z) (hhi z) p
  have hkbound (k : ℕ) (z : SphereAmbient n h) : c ≤ Hk k z ∧ Hk k z ≤ B :=
    cutoffAngularPower_bounds k g p c B hc1 hB1
      (fun x => (hpbound x).1) (fun x => (hpbound x).2) z
  have hkc (k : ℕ) : ContDiff ℝ 1 (Hk k) := cutoffAngularPower_contDiff k g hg1 hpos p
  have hlim : ∀ᵐ z ∂P, Tendsto (fun k => Hk k z) atTop (𝓝 (H z)) := by
    filter_upwards [sphereAmbientGaussian_ae_nonzero n h hh0] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [cutoffAngularPower_eventually_eq g p z hz] with k hk
    exact hk.symm
  have hI := integrable_powered_angular_energy n h hh g hg hlo p
  have hJ (k : ℕ) := actual_blockRadialCutoff_energy_integrable n h hh k
  have hJlim : Tendsto J atTop (𝓝 0) := actual_blockRadialCutoff_energy_tendsto n h hh
  have hη (η : ℝ) (hη : 0 < η) :
      entropy P (fun z => (H z)^2) ≤ (1 / (h : ℝ)) * ((1+η)*I) := by
    let A := fun k => (1+η)*I + (1+1/η)*K^2*J k
    have hA : Tendsto A atTop (𝓝 ((1+η)*I)) := by
      simpa only [A, mul_zero, add_zero] using
        (tendsto_const_nhds.add (hJlim.const_mul ((1+1/η)*K^2)))
    apply entropy_sq_le_of_approximation P (fun k => (hkc k).continuous.measurable)
      hc (fun k => ae_of_all _ (hkbound k)) hlim (Ak := A) ?_ hA
    intro k
    obtain ⟨D, hD⟩ := exists_bound_fderiv_cutoffAngularPower k g hg1 hLip hlo hhi p
    have hLSI := sphereAmbientGaussian_logSobolev_sq n h hh0 (Hk k) (hkc k) hc
      (fun z => (hkbound k z).1)
      (fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (hc.trans_le (hkbound k z).1)]
        exact (hkbound k z).2) hD
    change entropy P (fun z => (Hk k z)^2) ≤
      (1 / (h : ℝ)) * ∫ z, ‖fderiv ℝ (Hk k) z‖^2 ∂P at hLSI
    have hdom : Integrable (fun z : SphereAmbient n h =>
        (1+η)*‖fderiv ℝ H z‖^2 + (1+1/η)*K^2*
          ‖fderiv ℝ (blockRadialCutoff (ι := Fin n × Bool) (E := CE h) k) z‖^2) P :=
      (hI.const_mul (1+η)).add ((hJ k).const_mul ((1+1/η)*K^2))
    have he : ∀ᵐ z ∂P, ‖fderiv ℝ (Hk k) z‖^2 ≤
        (1+η)*‖fderiv ℝ H z‖^2 + (1+1/η)*K^2*
          ‖fderiv ℝ (blockRadialCutoff (ι := Fin n × Bool) (E := CE h) k) z‖^2 := by
      filter_upwards [sphereAmbientGaussian_ae_nonzero n h hh0] with z hz
      exact norm_sq_fderiv_cutoffAngularPower_le k g p hg1 hpos hK
        (abs_power_sub_one_uniform g hlo hhi p) hη z hz
    have hik : Integrable (fun z => ‖fderiv ℝ (Hk k) z‖^2) P :=
      hdom.mono_nonneg (((hkc k).continuous_fderiv (by norm_num)).norm.pow 2).aestronglyMeasurable
        (ae_of_all _ fun z => sq_nonneg _) he
    apply hLSI.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hi := integral_mono_ae hik hdom he
    rw [integral_add (hI.const_mul (1+η)) ((hJ k).const_mul ((1+1/η)*K^2)),
      integral_const_mul, integral_const_mul] at hi
    exact hi
  have hseq : Tendsto (fun k : ℕ => (1 / (h : ℝ)) * ((1+1/((k : ℝ)+1))*I))
      atTop (𝓝 ((1 / (h : ℝ))*I)) := by
    simpa only [add_zero, one_mul] using
      ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const I).const_mul
        (1 / (h : ℝ)))
  exact ge_of_tendsto' hseq (fun k => hη (1/((k : ℝ)+1)) (by positivity))

/-- The smooth-angular power-entropy family is now a theorem, not a premise. -/
theorem smoothSpherePowerEntropyBound (n h : ℕ) (hh : 2 ≤ h) :
    SmoothSpherePowerEntropyBound n h := by
  letI : NeZero h := ⟨by omega⟩
  have hh0 : 0 < h := by omega
  letI := sphereAmbientGaussian_probability n h hh0
  letI := directionsLaw_probability n h hh0
  intro g hg hLip hlo hhi p
  have he := smooth_angular_gaussian_entropy_le n h hh g hg hLip hlo hhi p
  have hb := integral_powered_angular_energy_le n h hh g hg hlo hLip p
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 / (h : ℝ) by positivity)
  have hp (x : SphereAmbient n h) : (g x^p)^2 = g x^(2*p) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (zero_le_one.trans (hlo x))]
    congr 1
    ring
  have hφ : Measurable (fun x : SphereAmbient n h => (g x^p)^2) :=
    (hg.continuous.measurable.pow_const p).pow_const 2
  have hφlog : Measurable (fun x : SphereAmbient n h =>
      (g x^p)^2 * Real.log ((g x^p)^2)) := hφ.mul hφ.log
  unfold entropy at he
  rw [integral_comp_blockNormalize n h hh0 _ hφlog,
    integral_comp_blockNormalize n h hh0 _ hφ] at he
  simp_rw [hp] at he
  change entropy (directionsLaw n h) (fun d => g (directionsToEuclidean n h d).val^(2*p)) ≤ _ at he
  apply he.trans
  convert hm using 1
  have hhne : (h : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hh0
  field_simp
  <;> ring

#print axioms sphereAmbientGaussian_probability
#print axioms smooth_angular_gaussian_entropy_le
#print axioms smoothSpherePowerEntropyBound
end AHHRadial
