import AHHNormalizationDerivative
import AHHBlockDualEnergy
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Exact blockwise angular energy bound for smooth functions after radial normalization. -/
noncomputable section
open scoped BigOperators
namespace AHHRadial
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Normalize every Hilbert block separately. -/
def blockNormalize (z : PiLp 2 (fun _ : ι => E)) : PiLp 2 (fun _ : ι => E) :=
  WithLp.toLp 2 (fun j => radialNormalize (z j))

@[simp] theorem blockNormalize_apply (z : PiLp 2 (fun _ : ι => E)) (j : ι) :
    blockNormalize z j = radialNormalize (z j) := rfl

theorem hasFDerivAt_blockNormalize (z : PiLp 2 (fun _ : ι => E)) (hz : ∀ j, z j ≠ 0) :
    HasFDerivAt blockNormalize (blockMap (fun j => normalizationDerivative (z j))) z := by
  rw [← hasFDerivWithinAt_univ]
  apply (hasFDerivWithinAt_piLp 2).mpr
  intro j
  have hp : HasFDerivAt (fun q : PiLp 2 (fun _ : ι => E) => q j)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) j) z :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => E) j).hasFDerivAt
  have hd := (hasFDerivAt_radialNormalize (hz j)).comp z hp
  convert hd.hasFDerivWithinAt using 1
  · rfl
  · ext v
    rfl

/-- The sharp reciprocal-square radius factor is kept for each separate block. -/
theorem norm_sq_fderiv_comp_blockNormalize_le
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (z : PiLp 2 (fun _ : ι => E))
    (hg : DifferentiableAt ℝ g (blockNormalize z)) (hz : ∀ j, z j ≠ 0) :
    ‖fderiv ℝ (g ∘ blockNormalize) z‖ ^ 2 ≤
      ∑ j, ‖blockPartial (fderiv ℝ g (blockNormalize z)) j‖ ^ 2 / ‖z j‖ ^ 2 := by
  rw [(hg.hasFDerivAt.comp z (hasFDerivAt_blockNormalize z hz)).fderiv]
  have hb := norm_sq_comp_blockMap_le_of_norm_le
    (fderiv ℝ g (blockNormalize z)) (fun j => normalizationDerivative (z j))
    (fun j => ‖z j‖⁻¹) (fun j => norm_normalizationDerivative_le (hz j))
  simpa only [inv_pow, div_eq_mul_inv] using hb

/-- A 1-Lipschitz smooth function has total angular dual energy at most one. -/
theorem sum_blockPartial_sq_le_one
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (hg : LipschitzWith 1 g)
    (z : PiLp 2 (fun _ : ι => E)) :
    ∑ j, ‖blockPartial (fderiv ℝ g z) j‖ ^ 2 ≤ 1 := by
  rw [← norm_sq_eq_sum_blockPartial]
  have hb : ‖fderiv ℝ g z‖ ≤ 1 := by simpa using norm_fderiv_le_of_lipschitz ℝ hg
  nlinarith [norm_nonneg (fderiv ℝ g z)]

@[simp] theorem blockPartial_smul (c : ℝ)
    (L : PiLp 2 (fun _ : ι => E) →L[ℝ] ℝ) (j : ι) :
    blockPartial (c • L) j = c • blockPartial L j := by
  ext v
  rfl

/-- The real power chain rule retains the sharp angular energy for every real power. -/
theorem norm_sq_fderiv_rpow_comp_blockNormalize_le
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (z : PiLp 2 (fun _ : ι => E)) (p : ℝ)
    (hg : DifferentiableAt ℝ g (blockNormalize z)) (hpos : 0 < g (blockNormalize z))
    (hz : ∀ j, z j ≠ 0) :
    ‖fderiv ℝ (fun y => (g (blockNormalize y)) ^ p) z‖ ^ 2 ≤
      ∑ j, p ^ 2 * ((g (blockNormalize z)) ^ 2) ^ (p - 1) *
        ‖blockPartial (fderiv ℝ g (blockNormalize z)) j‖ ^ 2 / ‖z j‖ ^ 2 := by
  have hp := hg.hasFDerivAt.rpow_const (p := p) (Or.inl hpos.ne')
  have hb := norm_sq_fderiv_comp_blockNormalize_le (fun y => g y ^ p) z
    hp.differentiableAt hz
  rw [hp.fderiv] at hb
  simp only [blockPartial_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hb
  have he : (g (blockNormalize z) ^ (p - 1)) ^ 2 =
      ((g (blockNormalize z)) ^ 2) ^ (p - 1) := by
    rw [← Real.rpow_mul_natCast hpos.le, ← Real.rpow_natCast_mul hpos.le]
    congr 1
    ring
  simpa only [he, Function.comp_def, mul_assoc] using hb

/-- Total powered angular energy is bounded independently of the number of blocks. -/
theorem sum_powered_blockPartial_sq_le
    (g : PiLp 2 (fun _ : ι => E) → ℝ) (hg : LipschitzWith 1 g)
    (z : PiLp 2 (fun _ : ι => E)) (p : ℝ) :
    ∑ j, p ^ 2 * ((g z) ^ 2) ^ (p - 1) *
      ‖blockPartial (fderiv ℝ g z) j‖ ^ 2 ≤ p ^ 2 * ((g z) ^ 2) ^ (p - 1) := by
  rw [← Finset.mul_sum]
  have hc : 0 ≤ p ^ 2 * ((g z) ^ 2) ^ (p - 1) := by positivity
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (sum_blockPartial_sq_le_one g hg z) hc

#print axioms hasFDerivAt_blockNormalize
#print axioms norm_sq_fderiv_comp_blockNormalize_le
#print axioms sum_blockPartial_sq_le_one
#print axioms norm_sq_fderiv_rpow_comp_blockNormalize_le
#print axioms sum_powered_blockPartial_sq_le
end AHHRadial
