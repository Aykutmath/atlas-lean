import GaussianWeightedBilinearMGF
import ConditionalMGFIteration
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

open MeasureTheory ProbabilityTheory GaussianEllipsoid GaussianMixedNormHelpers
open scoped ENNReal InnerProductSpace

namespace GaussianEllipsoidCandidate

/-- Measurability of a bilinear cluster with an arbitrary Borel past-dependent
operator and fresh Gaussian coordinates. -/
theorem measurable_predictable_bilinear_cluster {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {r q : ℕ}
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable W) (w : ι → ℝ) :
    Measurable (fun p : Ω × (ι → Euclid q × Euclid r) =>
      ∑ i, w i * ⟪W p.1 (p.2 i).1,(p.2 i).2⟫_ℝ) := by
  have happ : Measurable (fun p : (Euclid q →L[ℝ] Euclid r) × Euclid q => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  apply Finset.measurable_sum
  intro i _
  have hA : Measurable (fun p : Ω × (ι → Euclid q × Euclid r) => (p.2 i).1) :=
    measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd)
  have hB : Measurable (fun p : Ω × (ι → Euclid q × Euclid r) => (p.2 i).2) :=
    measurable_snd.comp ((measurable_pi_apply i).comp measurable_snd)
  have hinner : Measurable (fun p : Euclid r × Euclid r => ⟪p.1,p.2⟫_ℝ) :=
    (continuous_fst.inner continuous_snd).measurable
  exact (hinner.comp ((happ.comp ((hW.comp measurable_fst).prodMk hA)).prodMk hB)).const_mul (w i)

/-- The actual predictable Gaussian MGF step. The current sample has its
explicit iid Gaussian product law, and the preceding data may have any law.
No conditional MGF or accumulated integrability estimate is an assumption. -/
theorem predictable_gaussian_bilinear_step {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] {r q : ℕ}
    (μ : Measure Ω) [SFinite μ]
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable W)
    (hWnorm : ∀ ω, ‖W ω‖ ≤ 1) (R : ℝ)
    (hWenergy : ∀ ω, ‖operatorFrobenius (W ω)‖^2 ≤ R)
    (w : ι → ℝ) (t : ℝ) (hcap : ∀ i, (t*w i)^2 ≤ 1/2)
    (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : Ω × (ι → Euclid q × Euclid r), F p.1 *
      ENNReal.ofReal (Real.exp (t * ∑ i, w i * ⟪W p.1 (p.2 i).1,(p.2 i).2⟫_ℝ))
      ∂μ.prod (gaussianBilinearSampleLaw ι q r)) ≤
        ENNReal.ofReal (Real.exp (t^2 * (∑ i, (w i)^2) * R)) * ∫⁻ ω, F ω ∂μ := by
  let G : Ω × (ι → Euclid q × Euclid r) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (t * ∑ i, w i * ⟪W p.1 (p.2 i).1,(p.2 i).2⟫_ℝ))
  have hG : Measurable G := by
    have hh := measurable_predictable_bilinear_cluster W hW w
    exact (hh.const_mul t).exp.ennreal_ofReal
  have hconditional : ∀ ω, (∫⁻ X, G (ω,X) ∂gaussianBilinearSampleLaw ι q r) ≤
      ENNReal.ofReal (Real.exp (t^2 * (∑ i, (w i)^2) * R)) := by
    intro ω
    have hnormsq : ‖W ω‖^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg (W ω)) (hWnorm ω) 2
    have hcap' : ∀ i, (t*w i)^2 * ‖W ω‖^2 ≤ 1/2 := by
      intro i
      exact (mul_le_mul_of_nonneg_left hnormsq (sq_nonneg (t*w i))).trans
        (by simpa using hcap i)
    apply (gaussian_weighted_bilinear_lintegral_le (W ω) w t hcap').trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hWenergy ω)
      (mul_nonneg (sq_nonneg t) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hh := lintegral_predictable_product_le μ
    (Kernel.const Ω (gaussianBilinearSampleLaw ι q r)) F G hF hG
    (ENNReal.ofReal (Real.exp (t^2 * (∑ i, (w i)^2) * R)))
    (Filter.Eventually.of_forall hconditional)
  simpa only [Measure.compProd_const] using hh

/-- Joint Borel dependence for a single fresh row pair. -/
theorem measurable_predictable_bilinear_row {Ω : Type*} [MeasurableSpace Ω] {r q : ℕ}
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable W) :
    Measurable (fun p : Ω × (Euclid q × Euclid r) => ⟪W p.1 p.2.1,p.2.2⟫_ℝ) := by
  have happ : Measurable (fun p : (Euclid q →L[ℝ] Euclid r) × Euclid q => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  have hinner : Measurable (fun p : Euclid r × Euclid r => ⟪p.1,p.2⟫_ℝ) :=
    (continuous_fst.inner continuous_snd).measurable
  exact hinner.comp ((happ.comp ((hW.comp measurable_fst).prodMk
    (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))

/-- One-row version for uniform row-by-row revelation. This avoids changing
finite index types across clusters in the final martingale assembly. -/
theorem predictable_gaussian_bilinear_row_step {Ω : Type*}
    [MeasurableSpace Ω] {r q : ℕ}
    (μ : Measure Ω) [SFinite μ]
    (W : Ω → (Euclid q →L[ℝ] Euclid r)) (hW : Measurable W)
    (hWnorm : ∀ ω, ‖W ω‖ ≤ 1) (R : ℝ)
    (hWenergy : ∀ ω, ‖operatorFrobenius (W ω)‖^2 ≤ R)
    (t : ℝ) (hcap : t^2 ≤ 1/2) (F : Ω → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : Ω × (Euclid q × Euclid r), F p.1 *
      ENNReal.ofReal (Real.exp (t * ⟪W p.1 p.2.1,p.2.2⟫_ℝ))
      ∂μ.prod ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r)))) ≤
        ENNReal.ofReal (Real.exp (t^2 * R)) * ∫⁻ ω, F ω ∂μ := by
  let G : Ω × (Euclid q × Euclid r) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (t * ⟪W p.1 p.2.1,p.2.2⟫_ℝ))
  have hG : Measurable G :=
    ((measurable_predictable_bilinear_row W hW).const_mul t).exp.ennreal_ofReal
  have hconditional : ∀ ω, (∫⁻ X, G (ω,X)
        ∂(euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) ≤
      ENNReal.ofReal (Real.exp (t^2 * R)) := by
    intro ω
    have hnormsq : ‖W ω‖^2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (norm_nonneg (W ω)) (hWnorm ω) 2
    have hcap' : t^2 * ‖W ω‖^2 ≤ 1/2 :=
      (mul_le_mul_of_nonneg_left hnormsq (sq_nonneg t)).trans (by simpa using hcap)
    apply (gaussian_bilinear_lintegral_le (W ω) t hcap').trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hWenergy ω) (sq_nonneg t)
  have hh := lintegral_predictable_product_le μ
    (Kernel.const Ω ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))))
    F G hF hG (ENNReal.ofReal (Real.exp (t^2 * R)))
    (Filter.Eventually.of_forall hconditional)
  simpa only [Measure.compProd_const] using hh

#print axioms measurable_predictable_bilinear_row
#print axioms predictable_gaussian_bilinear_row_step

#print axioms measurable_predictable_bilinear_cluster
#print axioms predictable_gaussian_bilinear_step

end GaussianEllipsoidCandidate
