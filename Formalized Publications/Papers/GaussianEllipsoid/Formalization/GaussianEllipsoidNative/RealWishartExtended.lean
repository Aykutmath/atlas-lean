import RealBartlettMoment

noncomputable section
open Finset MeasureTheory ProbabilityTheory Set Module
open InnerProductSpace
namespace GaussianMixedNormHelpers

/-- Full-rank Gaussian Gram determinants are positive almost surely. -/
theorem gaussianRows_gramDet_pos_ae (r k : ℕ) (hkr : r ≤ k) :
    ∀ᵐ f : Fin r → EuclideanSpace ℝ (Fin k)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k)),
      0 < (realGramMatrix f).det := by
  let ν := fun j : Fin r => gammaMeasure (((k-j.val:ℕ):ℝ)/2) (1/2)
  letI (j : Fin r) : IsProbabilityMeasure (ν j) :=
    isProbabilityMeasure_gammaMeasure (by
      have hj : 0 < k-j.val := by omega
      positivity) (by norm_num)
  have hp : ∀ᵐ x : Fin r → ℝ ∂Measure.pi ν, ∀ j, 0 < x j := by
    apply ae_all_iff.mpr
    intro j
    exact (Measure.tendsto_eval_ae_ae (μ := ν) (i := j)).eventually
      (gammaMeasure_pos_ae _ _)
  have hp' : ∀ᵐ x : Fin r → ℝ ∂(Measure.pi
      (fun _ : Fin r => euclideanGaussianLaw (Fin k))).map
      (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
        fun j => ‖gramSchmidt ℝ f j‖^2), ∀ j, 0 < x j := by
    rw [gaussianRows_map_gramSchmidt_norm_sq r k hkr]
    exact hp
  have hgs := ae_of_ae_map measurable_gramSchmidt_norm_sq.aemeasurable hp'
  filter_upwards [hgs] with f hf
  rw [det_realGramMatrix_eq_prod_gramSchmidt_norm_sq]
  exact Finset.prod_pos (fun j _ => hf j)

/-- Exact finite Wishart inverse moment with the singular=infinity convention. -/
theorem gaussianRows_extended_negative_real_det_moment (r k : ℕ) (hkr : r ≤ k)
    (s : ℝ) (hs : 0 ≤ s) (hshape : ∀ j : Fin r, s < ((k-j.val : ℕ):ℝ)/2) :
    (∫⁻ f : Fin r → EuclideanSpace ℝ (Fin k),
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)
      ∂Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))) =
    ENNReal.ofReal (∏ j : Fin r, (2:ℝ)^(-s) *
      (Real.Gamma (((k-j.val : ℕ):ℝ)/2-s) / Real.Gamma (((k-j.val : ℕ):ℝ)/2))) := by
  let μ := Measure.pi (fun _ : Fin r => euclideanGaussianLaw (Fin k))
  have heq : (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      (ENNReal.ofReal (realGramMatrix f).det)^(-s)) =ᵐ[μ]
      (fun f => ENNReal.ofReal ((realGramMatrix f).det^(-s))) := by
    filter_upwards [gaussianRows_gramDet_pos_ae r k hkr] with f hf
    exact (ENNReal.ofReal_rpow_of_pos hf)
  have hInt : Integrable (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      (realGramMatrix f).det^(-s)) μ := by
    apply Integrable.of_integral_ne_zero
    rw [gaussianRows_negative_real_det_moment r k hkr s hs hshape]
    apply ne_of_gt
    apply Finset.prod_pos
    intro j _
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (div_pos (Real.Gamma_pos_of_pos (sub_pos.mpr (hshape j)))
        (Real.Gamma_pos_of_pos (lt_of_le_of_lt hs (hshape j))))
  have hnn : 0 ≤ᵐ[μ] (fun f : Fin r → EuclideanSpace ℝ (Fin k) =>
      (realGramMatrix f).det^(-s)) := by
    filter_upwards [gaussianRows_gramDet_pos_ae r k hkr] with f hf
    exact Real.rpow_nonneg hf.le _
  rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal hInt hnn,
    gaussianRows_negative_real_det_moment r k hkr s hs hshape]

#print axioms gaussianRows_gramDet_pos_ae
#print axioms gaussianRows_extended_negative_real_det_moment
end GaussianMixedNormHelpers
