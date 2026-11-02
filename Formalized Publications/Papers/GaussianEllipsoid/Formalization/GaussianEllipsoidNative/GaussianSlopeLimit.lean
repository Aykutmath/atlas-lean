import GaussianLipschitzIntegrability

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers Filter
open scoped BigOperators InnerProductSpace Topology
namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

def tangent (f : E ι → ℝ) (z : E ι × E ι) : ℝ := fderiv ℝ f z.1 z.2

theorem tangent_measurable (f : E ι → ℝ) : Measurable (tangent f) := by
  unfold tangent
  have h : Continuous (fun p : (E ι →L[ℝ] ℝ) × E ι => p.1 p.2) := by fun_prop
  exact h.measurable.comp (((measurable_fderiv ℝ f).comp measurable_fst).prodMk measurable_snd)

theorem tangent_sq_integrable {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    Integrable (fun z => (tangent f z)^2) (γ₂ ι) := by
  apply pair_norm_snd_sq_integrable.mono' ((tangent_measurable f).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h : |tangent f z| ≤ ‖z.2‖ := by
    have h1 := (fderiv ℝ f z.1).le_opNorm z.2
    have h2 := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := z.1)
    change ‖tangent f z‖ ≤ _ at h1
    simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using h1.trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg z.2))
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2

theorem integral_tangent_sq {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    (∫ z, (tangent f z)^2 ∂γ₂ ι) = ∫ x, ‖fderiv ℝ f x‖^2 ∂γ ι := by
  rw [integral_prod _ (tangent_sq_integrable hf)]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  exact euclidean_integral_linear_sq (fderiv ℝ f x)

theorem integral_tangent_sq_le_one {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    (∫ z, (tangent f z)^2 ∂γ₂ ι) ≤ 1 := by
  rw [integral_tangent_sq hf]
  have hm : Measurable (fun x => ‖fderiv ℝ f x‖^2) := (measurable_fderiv ℝ f).norm.pow_const 2
  have hb (x : E ι) : ‖fderiv ℝ f x‖^2 ≤ (1 : ℝ) := by
    have h := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
    simpa only [NNReal.coe_one, one_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hi : Integrable (fun x => ‖fderiv ℝ f x‖^2) (γ ι) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖fderiv ℝ f x‖)]
      exact hb x)
  simpa using integral_mono hi (integrable_const (1:ℝ)) hb

def angleStep (n : ℕ) : ℝ := (Real.pi/2)/(n+1)

theorem angleStep_pos (n : ℕ) : 0 < angleStep n := by
  unfold angleStep
  positivity

theorem angleStep_tendsto : Tendsto angleStep atTop (𝓝[Set.Ioi (0:ℝ)] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall angleStep_pos⟩
  exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem slope_sq_limit {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    Tendsto (fun n => ∫ z, ((f (first (angleStep n) z)-f z.1)/(angleStep n))^2 ∂γ₂ ι)
      atTop (𝓝 (∫ z, (tangent f z)^2 ∂γ₂ ι)) := by
  apply tendsto_integral_of_dominated_convergence (fun z : E ι × E ι => 2*(‖z.1‖^2+‖z.2‖^2))
  · intro n
    exact ((((hf.continuous.comp (continuous_first _)).sub
      (hf.continuous.comp continuous_fst)).div_const _).pow 2).aestronglyMeasurable
  · exact pair_energy_integrable
  · intro n
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact lipschitz_rotation_slope_bound hf _ z
  · have hd : ∀ᵐ z ∂γ₂ ι, DifferentiableAt ℝ f z.1 :=
      Measure.quasiMeasurePreserving_fst.ae (gaussian_ae_differentiable hf)
    filter_upwards [hd] with z hz
    have hz' : HasFDerivAt f (fderiv ℝ f z.1) (first 0 z) := by
      simpa only [first_zero] using hz.hasFDerivAt
    have h : HasDerivAt (fun t => f (first t z)) (tangent f z) 0 :=
      hz'.comp_hasDerivAt 0 (first_hasDerivAt z)
    have hh := h.tendsto_slope_zero_right.comp angleStep_tendsto
    have hh' : Tendsto (fun n => (f (first (angleStep n) z)-f z.1)/(angleStep n))
        atTop (𝓝 (tangent f z)) := by
      simpa only [Function.comp_def, first_zero, zero_add, smul_eq_mul, div_eq_mul_inv,
        mul_comm] using hh
    exact hh'.pow 2

end GaussianVariance
