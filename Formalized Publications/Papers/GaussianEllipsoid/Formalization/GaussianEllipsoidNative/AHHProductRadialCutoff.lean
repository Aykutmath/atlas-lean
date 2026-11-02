import AHHRadialCutoffEnergy
import AHHBlockNormalizationEnergy
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-! Concrete product radial cutoffs for bounded smooth angular functions.
The regularized functions agree with the angular pullback away from shrinking
coordinate balls and are genuinely C¹ even where a block is zero. -/
noncomputable section
open MeasureTheory GaussianMixedNormHelpers Filter PaperSmoothCutoff
open scoped BigOperators Topology ContDiff
namespace AHHRadial
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def blockRadialCutoff (k : ℕ) (z : PiLp 2 (fun _ : ι => E)) : ℝ :=
  ∏ j, loss 1 (((k : ℝ) + 1) * ‖z j‖)

theorem blockRadialCutoff_nonneg (k : ℕ) (z : PiLp 2 (fun _ : ι => E)) :
    0 ≤ blockRadialCutoff k z :=
  Finset.prod_nonneg fun j _ => loss_nonneg _ _

theorem blockRadialCutoff_le_one (k : ℕ) (z : PiLp 2 (fun _ : ι => E)) :
    blockRadialCutoff k z ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _
    exact loss_nonneg _ _
  · intro j _
    exact loss_le_one _ _

theorem blockRadialCutoff_contDiff (k : ℕ) :
    ContDiff ℝ 1 (blockRadialCutoff (ι := ι) (E := E) k) := by
  apply contDiff_prod
  intro j _
  have hc : ContDiff ℝ 1 (fun z : PiLp 2 (fun _ : ι => E) =>
      ((k : ℝ) + 1)^2 * ‖z j‖^2) :=
    contDiff_const.mul ((contDiff_piLp_apply 2).norm_sq ℝ)
  simpa [loss, mul_pow, Function.comp_def] using
    (chi_contDiff (m := 1)).comp hc

theorem blockRadialCutoff_eq_zero_of_small (k : ℕ)
    (z : PiLp 2 (fun _ : ι => E)) (j : ι)
    (hj : ((k : ℝ) + 1) * ‖z j‖ ≤ 1 / 2) :
    blockRadialCutoff k z = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply loss_zero (by norm_num : (0 : ℝ) < 1)
  rw [abs_of_nonneg (by positivity)]
  exact hj

theorem blockRadialCutoff_eventually_zero (k : ℕ)
    (z : PiLp 2 (fun _ : ι => E)) (j : ι) (hj : z j = 0) :
    ∀ᶠ y in 𝓝 z, blockRadialCutoff k y = 0 := by
  have hc : Continuous (fun y : PiLp 2 (fun _ : ι => E) =>
      ((k : ℝ) + 1) * ‖y j‖) := continuous_const.mul (PiLp.continuous_apply 2 _ j).norm
  have hb : ((k : ℝ) + 1) * ‖z j‖ < 1 / 2 := by rw [hj, norm_zero, mul_zero]; norm_num
  filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hb)] with y hy
  exact blockRadialCutoff_eq_zero_of_small k y j hy.le

theorem blockRadialCutoff_eventually_one (z : PiLp 2 (fun _ : ι => E))
    (hz : ∀ j, z j ≠ 0) :
    ∀ᶠ k : ℕ in atTop, blockRadialCutoff k z = 1 := by
  have he (j : ι) : ∀ᶠ k : ℕ in atTop, 1 / ‖z j‖ ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [Filter.eventually_all.mpr he] with k hk
  unfold blockRadialCutoff
  apply Finset.prod_eq_one
  intro j _
  apply loss_one (by norm_num : (0 : ℝ) < 1)
  rw [abs_of_nonneg (by positivity)]
  have hp := norm_pos_iff.mpr (hz j)
  have hmul := (div_le_iff₀ hp).mp (hk j)
  nlinarith

theorem blockNormalize_contDiffAt (z : PiLp 2 (fun _ : ι => E))
    (hz : ∀ j, z j ≠ 0) : ContDiffAt ℝ 1 blockNormalize z := by
  apply (contDiffAt_piLp 2).mpr
  intro j
  change ContDiffAt ℝ 1 (fun y : PiLp 2 (fun _ : ι => E) => ‖y j‖⁻¹ • y j) z
  exact (((contDiffAt_piLp_apply 2).norm ℝ (hz j)).inv
    (norm_ne_zero_iff.mpr (hz j))).smul (contDiffAt_piLp_apply 2)

def cutoffAngularPower (k : ℕ) (g : PiLp 2 (fun _ : ι => E) → ℝ)
    (p : ℝ) (z : PiLp 2 (fun _ : ι => E)) : ℝ :=
  1 + blockRadialCutoff k z * ((g (blockNormalize z))^p - 1)

/-- The actual cutoffs remove all singular zero blocks, with no assumed
regularity of normalization at zero. -/
theorem cutoffAngularPower_contDiff (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (hg : ContDiff ℝ 1 g)
    (hpos : ∀ z, 0 < g z) (p : ℝ) : ContDiff ℝ 1 (cutoffAngularPower k g p) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : ∀ j, z j ≠ 0
  · have hpow := ((hg.contDiffAt.comp z (blockNormalize_contDiffAt z hz)).rpow_const_of_ne
      (hpos (blockNormalize z)).ne' (p := p))
    exact contDiffAt_const.add ((blockRadialCutoff_contDiff k).contDiffAt.mul
      (hpow.sub contDiffAt_const))
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    apply (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [blockRadialCutoff_eventually_zero k z j hj] with y hy
    simp only [cutoffAngularPower, hy, zero_mul, add_zero]

theorem cutoffAngularPower_eventually_eq (g : PiLp 2 (fun _ : ι => E) → ℝ)
    (p : ℝ) (z : PiLp 2 (fun _ : ι => E)) (hz : ∀ j, z j ≠ 0) :
    ∀ᶠ k : ℕ in atTop, cutoffAngularPower k g p z = (g (blockNormalize z))^p := by
  filter_upwards [blockRadialCutoff_eventually_one z hz] with k hk
  simp only [cutoffAngularPower, hk, one_mul]
  ring

/-- Blending with one preserves any interval containing one. -/
theorem cutoffAngularPower_bounds (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (p a b : ℝ)
    (ha : a ≤ 1) (hb : 1 ≤ b)
    (hlo : ∀ z, a ≤ (g z)^p) (hhi : ∀ z, (g z)^p ≤ b)
    (z : PiLp 2 (fun _ : ι => E)) :
    a ≤ cutoffAngularPower k g p z ∧ cutoffAngularPower k g p z ≤ b := by
  have hc0 := blockRadialCutoff_nonneg k z
  have hc1 := blockRadialCutoff_le_one k z
  have hl := mul_nonneg hc0 (sub_nonneg.mpr (hlo (blockNormalize z)))
  have hh := mul_nonneg hc0 (sub_nonneg.mpr (hhi (blockNormalize z)))
  have hal := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr ha)
  have hbu := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hb)
  dsimp only [cutoffAngularPower]
  constructor <;> nlinarith

#print axioms blockRadialCutoff_contDiff
#print axioms blockRadialCutoff_eventually_zero
#print axioms blockRadialCutoff_eventually_one
#print axioms blockNormalize_contDiffAt
#print axioms cutoffAngularPower_contDiff
#print axioms cutoffAngularPower_eventually_eq
#print axioms cutoffAngularPower_bounds
end AHHRadial
