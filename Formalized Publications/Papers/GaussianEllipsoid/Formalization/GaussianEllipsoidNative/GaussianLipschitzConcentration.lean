/- Newly reconstructed analytic support, 2026-10-03. Not recovered original bytes.
   Sharp Gaussian negative Laplace bound via bounded smooth approximation. -/
import GaussianSmoothConcentration
import GaussianSmoothTestPackaging
import LipschitzSmoothApproximationSupport

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers Filter
open BMSmoothQuadraticComposition GaussianCovarianceRotation GaussianSmoothTestPackaging
open scoped BigOperators Topology

namespace GaussianLipschitzConcentration
variable {d : ℕ}

/-- The actual Gaussian law in raw coordinates is transported to its Euclidean realization. -/
theorem toEuclid_preserving : MeasurePreserving (toEuclid (d := d))
    (γ d) (euclideanGaussianLaw (Fin d)) := by
  exact BMQuadraticSpectral.coordinates_preserving.symm

/-- Sharp negative centered Laplace transform for every nonnegative Euclidean
1-Lipschitz observable. All concentration input is proved in the imported
covariance interpolation and smooth approximation modules. -/
theorem nonnegative_lipschitz_laplace_fin {f : E d → ℝ}
    (hf : LipschitzWith 1 f) (hpos : ∀ x, 0 ≤ f x) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, Real.exp (t*((∫ y, f y ∂euclideanGaussianLaw (Fin d))-f x))
      ∂euclideanGaussianLaw (Fin d)) ≤ Real.exp (t^2/2) := by
  obtain ⟨g, hc, hl, hp, hcap, henv, hlim⟩ :=
    LipschitzSmoothApproximationSupport.exists_smooth_sequence (μ := volume) hf hpos
  let F : ℕ → SmoothTest (Fin d) := fun n => ofSmooth (g n) (hc n) (hl n) n (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hp n x)]
    exact hcap n x)
  let fr : Raw d → ℝ := fun x => f (toEuclid x)
  have hfr : Integrable fr (γ d) := by
    have hh := (toEuclid_preserving (d := d)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Raw d)).measurableEmbedding (g := f)
    exact hh.mpr (GaussianVariance.lipschitz_integrable hf)
  have hmean : Tendsto (fun n => ∫ x, (F n).value x ∂γ d) atTop
      (𝓝 (∫ x, fr x ∂γ d)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => fr x + 1)
    · intro n
      exact (F n).value.continuous.aestronglyMeasurable
    · exact hfr.add (integrable_const _)
    · intro n
      exact ae_of_all _ fun x => by
        change ‖g n (toEuclid x)‖ ≤ fr x + 1
        rw [Real.norm_eq_abs, abs_of_nonneg (hp n _)]
        exact henv n _
    · exact ae_of_all _ fun x => hlim (toEuclid x)
  have hexp : Tendsto (fun n => ∫ x, Real.exp (-t*(F n).value x) ∂γ d) atTop
      (𝓝 (∫ x, Real.exp (-t*fr x) ∂γ d)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (Real.continuous_exp.comp (continuous_const.mul (F n).value.continuous)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (hp n _)
    · exact ae_of_all _ fun x => Real.continuous_exp.continuousAt.tendsto.comp ((hlim (toEuclid x)).const_mul (-t))
  have heq (v : Raw d → ℝ) :
      (∫ x, Real.exp (t*((∫ y, v y ∂γ d)-v x)) ∂γ d) =
        Real.exp (t*(∫ y, v y ∂γ d)) * ∫ x, Real.exp (-t*v x) ∂γ d := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp only; rw [← Real.exp_add]; congr 1; ring
  have hbound : Real.exp (t*(∫ x, fr x ∂γ d)) *
      (∫ x, Real.exp (-t*fr x) ∂γ d) ≤ Real.exp (t^2/2) := by
    apply le_of_tendsto ((Real.continuous_exp.continuousAt.tendsto.comp (hmean.const_mul t)).mul hexp)
    apply Eventually.of_forall
    intro n
    dsimp only [Function.comp_apply]
    rw [← heq]
    exact GaussianSmoothConcentration.centered_laplace_le (F n)
      (ofSmooth_gradient_bound _ _ _ _ _) ht
  rw [← heq] at hbound
  have hmean_eq : (∫ x, fr x ∂γ d) = ∫ y, f y ∂euclideanGaussianLaw (Fin d) := by
    have hm : AEStronglyMeasurable f (euclideanGaussianLaw (Fin d)) :=
      hf.continuous.aestronglyMeasurable
    have hh := integral_map (toEuclid_preserving (d := d)).measurable.aemeasurable
      (f := f) (by rwa [(toEuclid_preserving (d := d)).map_eq])
    rw [(toEuclid_preserving (d := d)).map_eq] at hh
    exact hh.symm
  rw [hmean_eq] at hbound
  have hm : AEStronglyMeasurable (fun x => Real.exp
      (t*((∫ y, f y ∂euclideanGaussianLaw (Fin d))-f x))) (euclideanGaussianLaw (Fin d)) := by
    exact (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub hf.continuous))).aestronglyMeasurable
  have hh := integral_map (toEuclid_preserving (d := d)).measurable.aemeasurable
    (f := fun x => Real.exp (t*((∫ y, f y ∂euclideanGaussianLaw (Fin d))-f x)))
    (by rwa [(toEuclid_preserving (d := d)).map_eq])
  rw [(toEuclid_preserving (d := d)).map_eq] at hh
  rw [hh]
  exact hbound

#print axioms nonnegative_lipschitz_laplace_fin
end GaussianLipschitzConcentration
