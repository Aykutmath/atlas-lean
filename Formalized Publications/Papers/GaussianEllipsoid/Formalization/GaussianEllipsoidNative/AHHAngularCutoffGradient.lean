import AHHProductCutoffDerivative

/-! Derivative bounds for the concrete regularized angular powers. -/
noncomputable section
set_option maxHeartbeats 2000000
open Filter PaperSmoothCutoff PaperSmoothCutoffData3
open scoped BigOperators Topology
namespace AHHRadial
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem fderiv_cutoffAngularPower (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (p : ℝ)
    (hg : ContDiff ℝ 1 g) (hpos : ∀ z, 0 < g z)
    (z : PiLp 2 (fun _ : ι => E)) (hz : ∀ j, z j ≠ 0) :
    fderiv ℝ (cutoffAngularPower k g p) z =
      blockRadialCutoff k z • fderiv ℝ (fun y => (g (blockNormalize y))^p) z +
        ((g (blockNormalize z))^p - 1) • fderiv ℝ (blockRadialCutoff k) z := by
  have ha : DifferentiableAt ℝ (fun y => (g (blockNormalize y))^p) z :=
    (((hg.differentiable (by norm_num)) _).comp z
      (hasFDerivAt_blockNormalize z hz).differentiableAt).rpow_const
        (Or.inl (hpos _).ne')
  have hc := ((blockRadialCutoff_contDiff (ι := ι) (E := E) k).differentiable (by norm_num) z).hasFDerivAt
  simpa only [cutoffAngularPower] using! ((hc.mul (ha.hasFDerivAt.sub_const 1)).const_add 1).fderiv

theorem scalar_sq_add_young (x y : ℝ) {η : ℝ} (hη : 0 < η) :
    (x+y)^2 ≤ (1+η)*x^2 + (1+1/η)*y^2 := by
  have hy : 2*x*y ≤ η*x^2 + y^2/η := by
    have h' : 0 ≤ (η*x-y)^2/η := div_nonneg (sq_nonneg _) hη.le
    have he : (η*x-y)^2/η = η*x^2 - 2*x*y + y^2/η := by
      field_simp
      ring
    rw [he] at h'
    linarith
  simp only [div_eq_mul_inv, one_mul] at hy ⊢
  nlinarith

/-- Young splitting keeps the angular coefficient arbitrarily close to one. -/
theorem norm_sq_fderiv_cutoffAngularPower_le (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (p : ℝ)
    (hg : ContDiff ℝ 1 g) (hpos : ∀ z, 0 < g z)
    {B η : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |(g x)^p - 1| ≤ B) (hη : 0 < η)
    (z : PiLp 2 (fun _ : ι => E)) (hz : ∀ j, z j ≠ 0) :
    ‖fderiv ℝ (cutoffAngularPower k g p) z‖^2 ≤
      (1+η)*‖fderiv ℝ (fun y => (g (blockNormalize y))^p) z‖^2 +
      (1+1/η)*B^2*‖fderiv ℝ (blockRadialCutoff k) z‖^2 := by
  rw [fderiv_cutoffAngularPower k g p hg hpos z hz]
  let A := fderiv ℝ (fun y => (g (blockNormalize y))^p) z
  let C := fderiv ℝ (blockRadialCutoff k) z
  have ha : ‖blockRadialCutoff k z • A‖ ≤ ‖A‖ := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_of_nonneg (blockRadialCutoff_nonneg k z)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (blockRadialCutoff_le_one k z) A.opNorm_nonneg
  have hc : ‖((g (blockNormalize z))^p-1) • C‖ ≤ B*‖C‖ := by
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb _) C.opNorm_nonneg
  have hh := (ContinuousLinearMap.opNorm_add_le
    (blockRadialCutoff k z • A) (((g (blockNormalize z))^p-1) • C)).trans (add_le_add ha hc)
  have hs := pow_le_pow_left₀
    (ContinuousLinearMap.opNorm_nonneg (blockRadialCutoff k z • A + ((g (blockNormalize z))^p-1) • C)) hh 2
  have hy := scalar_sq_add_young ‖A‖ (B*‖C‖) hη
  have hfinal := hs.trans hy
  simpa only [A, C, mul_pow, mul_assoc] using hfinal

theorem cutoff_nonzero_inv_radius_le (k : ℕ)
    (z : PiLp 2 (fun _ : ι => E)) (hc : blockRadialCutoff k z ≠ 0) (j : ι) :
    ‖z j‖⁻¹ ≤ 2 * ((k : ℝ)+1) := by
  have hj : 1/2 < ((k : ℝ)+1)*‖z j‖ := lt_of_not_ge fun hn =>
    hc (blockRadialCutoff_eq_zero_of_small k z j hn)
  have hp : 0 < ‖z j‖ := by nlinarith [norm_nonneg (z j), Nat.cast_nonneg (α := ℝ) k]
  rw [← one_div, div_le_iff₀ hp]
  nlinarith

theorem norm_fderiv_angular_of_cutoff_nonzero (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (p : ℝ)
    (hg : ContDiff ℝ 1 g) (hpos : ∀ z, 0 < g z)
    {D : ℝ} (hD : 0 ≤ D) (hd : ∀ x, ‖fderiv ℝ (fun y => (g y)^p) x‖ ≤ D)
    (z : PiLp 2 (fun _ : ι => E)) (hz : ∀ j, z j ≠ 0)
    (hc : blockRadialCutoff k z ≠ 0) :
    ‖fderiv ℝ (fun y => (g (blockNormalize y))^p) z‖ ≤ 2*((k : ℝ)+1)*D := by
  have hpow : DifferentiableAt ℝ (fun y => (g y)^p) (blockNormalize z) :=
    ((hg.differentiable (by norm_num)) _).rpow_const (Or.inl (hpos _).ne')
  have hs := norm_sq_fderiv_comp_blockNormalize_le (fun y => (g y)^p) z hpow hz
  have hb : (∑ j, ‖blockPartial (fderiv ℝ (fun y => (g y)^p) (blockNormalize z)) j‖^2 /
      ‖z j‖^2) ≤ (2*((k : ℝ)+1))^2 * D^2 := by
    calc
      _ ≤ ∑ j, (2*((k : ℝ)+1))^2 *
          ‖blockPartial (fderiv ℝ (fun y => (g y)^p) (blockNormalize z)) j‖^2 := by
        apply Finset.sum_le_sum
        intro j _
        have hr := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg (z j)))
          (cutoff_nonzero_inv_radius_le k z hc j) 2
        simpa only [inv_pow, div_eq_mul_inv, mul_comm] using
          mul_le_mul_of_nonneg_left hr
            (sq_nonneg ‖blockPartial (fderiv ℝ (fun y => (g y)^p) (blockNormalize z)) j‖)
      _ = (2*((k : ℝ)+1))^2 * ‖fderiv ℝ (fun y => (g y)^p) (blockNormalize z)‖^2 := by
        rw [norm_sq_eq_sum_blockPartial, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (ContinuousLinearMap.opNorm_nonneg _) (hd _) 2) (sq_nonneg _)
  apply (sq_le_sq₀ (ContinuousLinearMap.opNorm_nonneg _) (by positivity)).mp
  simpa only [Function.comp_def, mul_pow] using hs.trans hb

/-- Each cutoff has a genuine global derivative bound, including zero blocks. -/
theorem norm_fderiv_cutoffAngularPower_uniform (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (p : ℝ)
    (hg : ContDiff ℝ 1 g) (hpos : ∀ z, 0 < g z)
    {B D M : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |(g x)^p - 1| ≤ B)
    (hD : 0 ≤ D) (hd : ∀ x, ‖fderiv ℝ (fun y => (g y)^p) x‖ ≤ D)
    (hM : 0 ≤ M) (hm : ∀ t, |deriv (loss 1) t| ≤ M)
    (z : PiLp 2 (fun _ : ι => E)) :
    ‖fderiv ℝ (cutoffAngularPower k g p) z‖ ≤
      2*((k : ℝ)+1)*D + B*(Fintype.card ι : ℝ)*(((k : ℝ)+1)*M) := by
  by_cases hz : ∀ j, z j ≠ 0
  · rw [fderiv_cutoffAngularPower k g p hg hpos z hz]
    let A := fderiv ℝ (fun y => (g (blockNormalize y))^p) z
    let C := fderiv ℝ (blockRadialCutoff k) z
    have ha : ‖blockRadialCutoff k z • A‖ ≤ 2*((k : ℝ)+1)*D := by
      by_cases hc : blockRadialCutoff k z = 0
      · rw [hc, zero_smul, ContinuousLinearMap.opNorm_zero]
        positivity
      · apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
        rw [Real.norm_of_nonneg (blockRadialCutoff_nonneg k z)]
        calc
          _ ≤ 1*‖A‖ := mul_le_mul_of_nonneg_right (blockRadialCutoff_le_one k z) A.opNorm_nonneg
          _ ≤ _ := by simpa only [one_mul] using norm_fderiv_angular_of_cutoff_nonzero k g p hg hpos hD hd z hz hc
    have hc : ‖((g (blockNormalize z))^p-1) • C‖ ≤
        B*((Fintype.card ι : ℝ)*(((k : ℝ)+1)*M)) := by
      apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
      rw [Real.norm_eq_abs]
      exact mul_le_mul (hb _) (norm_fderiv_blockRadialCutoff_uniform k hM hm z)
        C.opNorm_nonneg hB
    have hh := (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add ha hc)
    simpa only [A, C, mul_assoc] using hh
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    have he : cutoffAngularPower k g p =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
      filter_upwards [blockRadialCutoff_eventually_zero k z j hj] with y hy
      simp only [cutoffAngularPower, hy, zero_mul, add_zero]
    rw [he.fderiv_eq, fderiv_const_apply, ContinuousLinearMap.opNorm_zero]
    positivity

theorem rpow_le_uniform_of_one_le (g : PiLp 2 (fun _ : ι => E) → ℝ)
    {R : ℝ} (hlo : ∀ z, 1 ≤ g z) (hhi : ∀ z, g z ≤ R) (p : ℝ)
    (z : PiLp 2 (fun _ : ι => E)) : (g z)^p ≤ R^|p| := by
  exact (Real.rpow_le_rpow_of_exponent_le (hlo z) (le_abs_self p)).trans
    (Real.rpow_le_rpow (le_trans zero_le_one (hlo z)) (hhi z) (abs_nonneg p))

theorem abs_power_sub_one_uniform (g : PiLp 2 (fun _ : ι => E) → ℝ)
    {R : ℝ} (hlo : ∀ z, 1 ≤ g z) (hhi : ∀ z, g z ≤ R) (p : ℝ)
    (z : PiLp 2 (fun _ : ι => E)) : |(g z)^p-1| ≤ R^|p| + 1 := by
  have hp : 0 < (g z)^p := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hlo z)) _
  have hb := rpow_le_uniform_of_one_le g hlo hhi p z
  apply abs_le.mpr
  constructor <;> linarith

theorem norm_fderiv_power_uniform (g : PiLp 2 (fun _ : ι => E) → ℝ)
    (hg : ContDiff ℝ 1 g) (hlip : LipschitzWith 1 g)
    {R : ℝ} (hlo : ∀ z, 1 ≤ g z) (hhi : ∀ z, g z ≤ R) (p : ℝ)
    (z : PiLp 2 (fun _ : ι => E)) :
    ‖fderiv ℝ (fun y => (g y)^p) z‖ ≤ |p| *R^|p-1| := by
  have hpos : 0 < g z := lt_of_lt_of_le zero_lt_one (hlo z)
  have hp := ((hg.differentiable (by norm_num)) z).hasFDerivAt.rpow_const
    (p := p) (Or.inl hpos.ne')
  rw [hp.fderiv]
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  have hDg : ‖fderiv ℝ g z‖ ≤ 1 := by
    simpa only [NNReal.coe_one] using norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := z)
  calc
    _ ≤ |p| *(g z)^(p-1)*1 := mul_le_mul_of_nonneg_left hDg (by positivity)
    _ ≤ _ := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (rpow_le_uniform_of_one_le g hlo hhi (p-1) z) (abs_nonneg p)

/-- Smooth bounded positive 1-Lipschitz angular observables satisfy every
bounded-C¹ Gaussian-test requirement after the actual radial cutoff. -/
theorem exists_bound_fderiv_cutoffAngularPower (k : ℕ)
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (hg : ContDiff ℝ 1 g) (hlip : LipschitzWith 1 g)
    {R : ℝ} (hlo : ∀ z, 1 ≤ g z) (hhi : ∀ z, g z ≤ R) (p : ℝ) :
    ∃ D : ℝ, ∀ z, ‖fderiv ℝ (cutoffAngularPower k g p) z‖ ≤ D := by
  obtain ⟨M, M₂, M₃, hM, _, _, hm, _, _⟩ := finite_derivative_bounds 1 (by norm_num)
  have hR : 0 ≤ R := (zero_le_one.trans (hlo 0)).trans (hhi 0)
  refine ⟨2*((k : ℝ)+1)*(|p| *R^|p-1|) + (R^|p| + 1)*(Fintype.card ι : ℝ)*(((k : ℝ)+1)*M), ?_⟩
  intro z
  exact norm_fderiv_cutoffAngularPower_uniform k g p hg
    (fun x => lt_of_lt_of_le zero_lt_one (hlo x)) (by positivity)
    (abs_power_sub_one_uniform g hlo hhi p) (by positivity)
    (norm_fderiv_power_uniform g hg hlip hlo hhi p) hM hm z

#print axioms exists_bound_fderiv_cutoffAngularPower
#print axioms norm_fderiv_cutoffAngularPower_uniform
#print axioms norm_sq_fderiv_cutoffAngularPower_le
#print axioms norm_fderiv_angular_of_cutoff_nonzero
end AHHRadial
