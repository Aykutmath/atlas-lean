import AHHProductCutoffDerivative
import AHHActualAmbientMarginals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Vanishing energy of the concrete product cutoff, proved by dominated
convergence with an inverse-square radial envelope. -/
noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory Filter PaperSmoothCutoff PaperSmoothCutoffData3
open scoped BigOperators Topology
namespace AHHRadial
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem blockRadialCutoff_energy_eventually_zero
    (z : PiLp 2 (fun _ : ι => E)) (hz : ∀ j, z j ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2 = 0 := by
  have he (j : ι) : ∀ᶠ k : ℕ in atTop, radialCutoffDerivative k ‖z j‖ = 0 :=
    radialCutoffDerivative_eventually_zero (norm_pos_iff.mpr (hz j))
  filter_upwards [Filter.eventually_all.mpr he] with k hk
  have hb := norm_fderiv_blockRadialCutoff_le k z
  simp only [hk, abs_zero, Finset.sum_const_zero] at hb
  have hn : ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖ = 0 :=
    le_antisymm hb (ContinuousLinearMap.opNorm_nonneg _)
  rw [hn, zero_pow (by decide : 2 ≠ 0)]

theorem integrable_blockRadialCutoff_energy
    (P : Measure (PiLp 2 (fun _ : ι => E)))
    (hzero : ∀ᵐ z ∂P, ∀ j, z j ≠ 0)
    (hinv : ∀ j : ι, Integrable (fun z : PiLp 2 (fun _ : ι => E) =>
      (‖z j‖^2)⁻¹) P) (k : ℕ) :
    Integrable (fun z : PiLp 2 (fun _ : ι => E) =>
      ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2) P := by
  obtain ⟨M, M₂, M₃, hM, _, _, hb, _, _⟩ := finite_derivative_bounds 1 (by norm_num)
  have hdom : Integrable (fun z : PiLp 2 (fun _ : ι => E) =>
      (Fintype.card ι : ℝ) * ∑ j, M^2 * (‖z j‖^2)⁻¹) P :=
    (integrable_finsetSum Finset.univ (fun j _ => (hinv j).const_mul (M^2))).const_mul _
  apply hdom.mono_nonneg
  · exact (((blockRadialCutoff_contDiff (ι := ι) (E := E) k).continuous_fderiv
      (by norm_num)).norm.pow 2).aestronglyMeasurable
  · exact ae_of_all _ fun z => sq_nonneg _
  · filter_upwards [hzero] with z hz
    apply (norm_sq_fderiv_blockRadialCutoff_le k z).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    exact radialCutoffDerivative_sq_le hM hb k (norm_pos_iff.mpr (hz j))

/-- A complete energy-limit theorem for the actual product cutoff, with the
only measure hypotheses being null zero blocks and integrable inverse radii. -/
theorem tendsto_blockRadialCutoff_energy
    (P : Measure (PiLp 2 (fun _ : ι => E)))
    (hzero : ∀ᵐ z ∂P, ∀ j, z j ≠ 0)
    (hinv : ∀ j : ι, Integrable (fun z : PiLp 2 (fun _ : ι => E) =>
      (‖z j‖^2)⁻¹) P) :
    Tendsto (fun k : ℕ => ∫ z,
      ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2 ∂P) atTop (𝓝 0) := by
  obtain ⟨M, M₂, M₃, hM, _, _, hb, _, _⟩ := finite_derivative_bounds 1 (by norm_num)
  have hdom : Integrable (fun z : PiLp 2 (fun _ : ι => E) =>
      (Fintype.card ι : ℝ) * ∑ j, M^2 * (‖z j‖^2)⁻¹) P :=
    (integrable_finsetSum Finset.univ (fun j _ => (hinv j).const_mul (M^2))).const_mul _
  have hm (k : ℕ) : AEStronglyMeasurable (fun z : PiLp 2 (fun _ : ι => E) =>
      ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2) P :=
    (((blockRadialCutoff_contDiff (ι := ι) (E := E) k).continuous_fderiv
      (by norm_num)).norm.pow 2).aestronglyMeasurable
  have hbound (k : ℕ) : ∀ᵐ z ∂P,
      ‖‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2‖ ≤
        (Fintype.card ι : ℝ) * ∑ j, M^2 * (‖z j‖^2)⁻¹ := by
    filter_upwards [hzero] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply (norm_sq_fderiv_blockRadialCutoff_le k z).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro j _
    exact radialCutoffDerivative_sq_le hM hb k (norm_pos_iff.mpr (hz j))
  have hlim : ∀ᵐ z ∂P, Tendsto (fun k : ℕ =>
      ‖fderiv ℝ (blockRadialCutoff (ι := ι) (E := E) k) z‖^2) atTop (𝓝 0) := by
    filter_upwards [hzero] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [blockRadialCutoff_energy_eventually_zero z hz] with k hk
    exact hk.symm
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence _ hm hdom hbound hlim

#print axioms blockRadialCutoff_energy_eventually_zero
#print axioms integrable_blockRadialCutoff_energy
#print axioms tendsto_blockRadialCutoff_energy

theorem actual_blockRadialCutoff_energy_integrable (n h : ℕ) (hh : 2 ≤ h) (k : ℕ) :
    Integrable (fun z : SphereAmbient n h =>
      ‖fderiv ℝ (blockRadialCutoff (ι := Fin n × Bool) (E := CE h) k) z‖^2)
      (sphereAmbientGaussianLaw n h) :=
  integrable_blockRadialCutoff_energy _ (sphereAmbientGaussian_ae_nonzero n h (by omega))
    (sphereAmbient_integrable_inv_norm_sq n h hh) k

theorem actual_blockRadialCutoff_energy_tendsto (n h : ℕ) (hh : 2 ≤ h) :
    Tendsto (fun k : ℕ => ∫ z : SphereAmbient n h,
      ‖fderiv ℝ (blockRadialCutoff (ι := Fin n × Bool) (E := CE h) k) z‖^2
        ∂sphereAmbientGaussianLaw n h) atTop (𝓝 0) :=
  tendsto_blockRadialCutoff_energy _ (sphereAmbientGaussian_ae_nonzero n h (by omega))
    (sphereAmbient_integrable_inv_norm_sq n h hh)

#print axioms actual_blockRadialCutoff_energy_integrable
#print axioms actual_blockRadialCutoff_energy_tendsto
end AHHRadial
