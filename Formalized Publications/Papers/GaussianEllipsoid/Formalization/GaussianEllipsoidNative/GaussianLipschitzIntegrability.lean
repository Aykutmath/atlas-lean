import GaussianLinearMoments
import Mathlib.Analysis.Calculus.Rademacher

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers
open scoped BigOperators InnerProductSpace
namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

abbrev γ (ι : Type*) [Fintype ι] := euclideanGaussianLaw ι
abbrev γ₂ (ι : Type*) [Fintype ι] := (γ ι).prod (γ ι)

theorem lipschitz_sq_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    Integrable (fun x => (f x)^2) (γ ι) := by
  apply ((integrable_const (2*(f 0)^2)).add
    (euclidean_integrable_norm_sq.const_mul 2)).mono'
    (hf.continuous.pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := hf.norm_sub_le x 0
  simp only [NNReal.coe_one, one_mul, sub_zero, Real.norm_eq_abs] at h
  change (f x)^2 ≤ 2*(f 0)^2+2*‖x‖^2
  have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
  simp only [sq_abs] at hs
  nlinarith [sq_nonneg (f x-2*f 0)]

theorem lipschitz_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    Integrable f (γ ι) :=
  ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
    (lipschitz_sq_integrable hf)).integrable (by norm_num)

theorem pair_fst_sq_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    Integrable (fun z : E ι × E ι => (f z.1)^2) (γ₂ ι) := by
  simpa only [mul_one] using (lipschitz_sq_integrable hf).mul_prod
    (integrable_const (1 : ℝ) : Integrable (fun _ : E ι => (1 : ℝ)) (γ ι))

theorem first_preserves_integral (f : E ι → ℝ) (t : ℝ) :
    (∫ z, f (first t z) ∂γ₂ ι) = ∫ x, f x ∂γ ι := by
  have h := (pairRotation_preserving (ι := ι) t).integral_comp' (fun z => f z.1)
  have hp := integral_prod_mul (μ := γ ι) (ν := γ ι) f (fun _ => (1 : ℝ))
  simpa only [pairRotation_apply, first, mul_one, integral_const, probReal_univ,
    smul_eq_mul] using! h.trans (by simpa only [mul_one, integral_const,
      probReal_univ, smul_eq_mul] using! hp)

theorem pair_first_sq_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) (t : ℝ) :
    Integrable (fun z => (f (first t z))^2) (γ₂ ι) := by
  have h := ((pairRotation_preserving (ι := ι) t).integrable_comp
    ((hf.continuous.comp continuous_fst).pow 2).aestronglyMeasurable).mpr
      (pair_fst_sq_integrable hf)
  simpa only [Function.comp_def, pairRotation_apply, first] using! h

theorem pair_increment_sq_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) (t s : ℝ) :
    Integrable (fun z => (f (first t z)-f (first s z))^2) (γ₂ ι) := by
  have h1 := (memLp_two_iff_integrable_sq
    ((hf.continuous.comp (continuous_first t)).aestronglyMeasurable)).mpr
      (pair_first_sq_integrable hf t)
  have h2 := (memLp_two_iff_integrable_sq
    ((hf.continuous.comp (continuous_first s)).aestronglyMeasurable)).mpr
      (pair_first_sq_integrable hf s)
  exact (h1.sub h2).integrable_sq

theorem pair_diff_sq_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) (t : ℝ) :
    Integrable (fun z => (f (first t z)-f z.1)^2) (γ₂ ι) := by
  simpa only [first_zero] using pair_increment_sq_integrable hf t 0

theorem lipschitz_rotation_slope_bound {f : E ι → ℝ} (hf : LipschitzWith 1 f)
    (t : ℝ) (z : E ι × E ι) :
    ((f (first t z)-f z.1)/t)^2 ≤ 2*(‖z.1‖^2+‖z.2‖^2) := by
  by_cases ht : t = 0
  · subst t; simp; positivity
  have h1 := hf.norm_sub_le (first t z) z.1
  simp only [NNReal.coe_one, one_mul, Real.norm_eq_abs] at h1
  have h2 := h1.trans (first_sub_bound t z)
  have h3 : |(f (first t z)-f z.1)/t| ≤ ‖z.1‖+‖z.2‖ := by
    rw [abs_div]
    exact (div_le_iff₀ (abs_pos.mpr ht)).mpr (by simpa only [mul_comm] using h2)
  have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  simp only [sq_abs] at h4
  nlinarith [sq_nonneg (‖z.1‖-‖z.2‖)]

theorem gaussian_ae_differentiable {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    ∀ᵐ x ∂γ ι, DifferentiableAt ℝ f x := by
  rw [γ, euclideanGaussianLaw_eq_withDensity]
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (hf.ae_differentiableAt (μ := volume))

end GaussianVariance
