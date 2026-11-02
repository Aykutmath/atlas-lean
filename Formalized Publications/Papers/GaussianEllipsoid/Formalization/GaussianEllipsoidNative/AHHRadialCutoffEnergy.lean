import AHHGaussianEntropyTransfer
import PaperSmoothCutoffData3

/-! Vanishing scalar radial cutoff energy. The cutoff is the existing genuine
smooth function, and the inverse-square domination is integrable for complex
dimension at least two. This does not yet package the full product cutoff as a
Gaussian smooth test or assert the target sphere entropy inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers Filter
open PaperSmoothCutoff PaperSmoothCutoffData3
open scoped Topology ContDiff
namespace AHHRadial

theorem unit_loss_deriv_eq_zero {t : ℝ} (ht : 1 < t) :
    deriv (loss 1) t = 0 := by
  have he : loss 1 =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact loss_one (by norm_num) (hs.le.trans (le_abs_self s))
  rw [he.deriv_eq, deriv_const]

def radialCutoffDerivative (k : ℕ) (r : ℝ) : ℝ :=
  ((k : ℝ) + 1) * deriv (loss 1) (((k : ℝ) + 1) * r)

theorem hasDerivAt_scaled_radialCutoff (k : ℕ) (r : ℝ) :
    HasDerivAt (fun s => loss 1 (((k : ℝ) + 1) * s))
      (radialCutoffDerivative k r) r := by
  have hd := (((loss_C3 (1 : ℝ)).differentiable (by norm_num))
    (((k : ℝ) + 1) * r)).hasDerivAt
  simpa [radialCutoffDerivative, Function.comp_def, mul_comm] using
    hd.comp r ((hasDerivAt_id r).const_mul ((k : ℝ) + 1))

theorem radialCutoffDerivative_eventually_zero {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k : ℕ in atTop, radialCutoffDerivative k r = 0 := by
  have hl : ∀ᶠ k : ℕ in atTop, 1 / r ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1 / r))
  filter_upwards [hl] with k hk
  have hk' : 1 ≤ (k : ℝ) * r := (div_le_iff₀ hr).mp hk
  have ht : 1 < ((k : ℝ) + 1) * r := by nlinarith
  simp only [radialCutoffDerivative, unit_loss_deriv_eq_zero ht, mul_zero]

theorem radialCutoffDerivative_sq_le {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ t, |deriv (loss 1) t| ≤ M) (k : ℕ) {r : ℝ} (hr : 0 < r) :
    (radialCutoffDerivative k r)^2 ≤ M^2 * (r^2)⁻¹ := by
  by_cases ht : 1 < ((k : ℝ) + 1) * r
  · simp only [radialCutoffDerivative, unit_loss_deriv_eq_zero ht, mul_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    positivity
  · have hk : 0 ≤ (k : ℝ) + 1 := by positivity
    have hkr : ((k : ℝ) + 1) * r ≤ 1 := le_of_not_gt ht
    have hb : |radialCutoffDerivative k r| ≤ M / r := by
      rw [radialCutoffDerivative, abs_mul, abs_of_nonneg hk]
      apply le_trans (mul_le_mul_of_nonneg_left (hbound _) hk)
      apply (le_div_iff₀ hr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hkr hM]
    have hs := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hM hr.le)).mpr hb
    simpa only [sq_abs, div_pow, div_eq_mul_inv, mul_pow, inv_pow] using hs

/-- For any radius measure with a finite inverse-square moment, the exact
derivatives of the shrinking smooth cutoff have energy tending to zero. -/
theorem tendsto_radialCutoffDerivative_energy
    (P : Measure Radius)
    (hP : Integrable (fun r : Radius => ((r : ℝ)^2)⁻¹) P) :
    Tendsto (fun k : ℕ => ∫ r : Radius,
      (radialCutoffDerivative k (r : ℝ))^2 ∂P) atTop (𝓝 0) := by
  obtain ⟨M, M₂, M₃, hM, _, _, hb, _, _⟩ := finite_derivative_bounds 1 (by norm_num)
  have hd : Continuous (deriv (loss 1)) := by
    rw [← rawDerivative_one]
    exact (rawDerivative_contDiff 1 1).continuous
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun r : Radius => (radialCutoffDerivative k (r : ℝ))^2) P := by
    apply Continuous.aestronglyMeasurable
    unfold radialCutoffDerivative
    exact (continuous_const.mul (hd.comp (continuous_const.mul continuous_subtype_val))).pow 2
  have hlim (r : Radius) : Tendsto
      (fun k : ℕ => (radialCutoffDerivative k (r : ℝ))^2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [radialCutoffDerivative_eventually_zero r.property] with k hk
    simp only [hk, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  have hl := tendsto_integral_of_dominated_convergence
    (fun r : Radius => M^2 * ((r : ℝ)^2)⁻¹) hm (hP.const_mul (M^2))
    (fun k => ae_of_all _ fun r => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact radialCutoffDerivative_sq_le hM hb k r.property)
    (ae_of_all _ hlim)
  simpa only [integral_zero] using hl

theorem complex_radius_integrable_inv_sq (h : ℕ) (hh : 2 ≤ h) :
    Integrable (fun r : Radius => ((r : ℝ)^2)⁻¹)
      (radiusLaw (volume : Measure (CE h)) h) := by
  letI : NeZero h := ⟨by omega⟩
  apply Integrable.of_integral_ne_zero
  rw [radiusLaw_integral_inv_sq _ (by exact_mod_cast (show 0 < h by omega))
    (by rw [complex_finrank_real]; omega)]
  apply ne_of_gt
  apply div_pos (by exact_mod_cast (show 0 < h by omega))
  rw [complex_finrank_real]
  push_cast
  have : (2 : ℝ) ≤ h := by exact_mod_cast hh
  linarith

/-- The actual radial measure in the AHH model has vanishing cutoff energy. -/
theorem complex_radialCutoffDerivative_energy (h : ℕ) (hh : 2 ≤ h) :
    Tendsto (fun k : ℕ => ∫ r : Radius,
      (radialCutoffDerivative k (r : ℝ))^2
        ∂radiusLaw (volume : Measure (CE h)) h) atTop (𝓝 0) :=
  tendsto_radialCutoffDerivative_energy _ (complex_radius_integrable_inv_sq h hh)

#print axioms unit_loss_deriv_eq_zero
#print axioms hasDerivAt_scaled_radialCutoff
#print axioms radialCutoffDerivative_eventually_zero
#print axioms radialCutoffDerivative_sq_le
#print axioms tendsto_radialCutoffDerivative_energy
#print axioms complex_radius_integrable_inv_sq
#print axioms complex_radialCutoffDerivative_energy
end AHHRadial
