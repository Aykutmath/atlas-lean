import GaussianOperatorMGF
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers GaussianEllipsoid
open scoped ENNReal InnerProductSpace

namespace GaussianEllipsoidCandidate

/-- The actual law of finitely many independent rectangular Gaussian pairs. -/
noncomputable def gaussianBilinearSampleLaw (ι : Type*) [Fintype ι] (q r : ℕ) :
    Measure (ι → Euclid q × Euclid r) :=
  Measure.pi fun _ : ι => (euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))

instance gaussianBilinearSampleLaw_probability (ι : Type*) [Fintype ι] (q r : ℕ) :
    IsProbabilityMeasure (gaussianBilinearSampleLaw ι q r) := by
  unfold gaussianBilinearSampleLaw
  infer_instance

/-- Exact factorization of the weighted finite Gaussian bilinear exponential. -/
theorem gaussian_weighted_bilinear_integral_factorization {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (w : ι → ℝ) (t : ℝ) :
    (∫ X : ι → Euclid q × Euclid r, Real.exp (t * ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ)
      ∂gaussianBilinearSampleLaw ι q r) =
      ∏ i, mgf (fun p : Euclid q × Euclid r => ⟪T p.1,p.2⟫_ℝ)
        ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) (t*w i) := by
  classical
  letI : MeasureSpace (Euclid q × Euclid r) :=
    ⟨(euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))⟩
  letI : SigmaFinite (volume : Measure (Euclid q × Euclid r)) :=
    inferInstanceAs (SigmaFinite ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))))
  calc
    (∫ X : ι → Euclid q × Euclid r, Real.exp (t * ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ)
      ∂gaussianBilinearSampleLaw ι q r)
        = ∫ X : ι → Euclid q × Euclid r, ∏ i, Real.exp ((t*w i) * ⟪T (X i).1,(X i).2⟫_ℝ)
          ∂gaussianBilinearSampleLaw ι q r := by
      congr 1
      funext X
      rw [Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    _ = ∏ i, mgf (fun p : Euclid q × Euclid r => ⟪T p.1,p.2⟫_ℝ)
        ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) (t*w i) := by
      simpa only [gaussianBilinearSampleLaw, volume_pi, mgf] using
        integral_fintype_prod_eq_prod (μ := fun _ => (euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r)))
          (fun i (p : Euclid q × Euclid r) => Real.exp ((t*w i) * ⟪T p.1,p.2⟫_ℝ))

/-- Integrability of the weighted exponential under the actual independent-pair law. -/
theorem gaussian_weighted_bilinear_integrable {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ i, (t*w i)^2 * ‖T‖^2 ≤ 1/2) :
    Integrable (fun X : ι → Euclid q × Euclid r =>
      Real.exp (t * ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ)) (gaussianBilinearSampleLaw ι q r) := by
  apply (mgf_pos_iff (X := fun X : ι → Euclid q × Euclid r =>
    ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ) (t := t)).mp
  change 0 < ∫ X : ι → Euclid q × Euclid r,
    Real.exp (t * ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ) ∂gaussianBilinearSampleLaw ι q r
  rw [gaussian_weighted_bilinear_integral_factorization]
  apply Finset.prod_pos
  intro i _
  exact mgf_pos (gaussian_bilinear_exp_integrable T (t*w i) (hcap i))

/-- The exact finite-sample weighted bilinear MGF estimate used by each future
cross-term cluster: the exponent is t² times coefficient energy times Frobenius energy. -/
theorem gaussian_weighted_bilinear_mgf_le {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ i, (t*w i)^2 * ‖T‖^2 ≤ 1/2) :
    mgf (fun X : ι → Euclid q × Euclid r => ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ)
      (gaussianBilinearSampleLaw ι q r) t ≤
        Real.exp (t^2 * (∑ i, (w i)^2) * ‖operatorFrobenius T‖^2) := by
  unfold mgf
  rw [gaussian_weighted_bilinear_integral_factorization]
  calc
    ∏ i, mgf (fun p : Euclid q × Euclid r => ⟪T p.1,p.2⟫_ℝ)
        ((euclideanGaussianLaw (Fin q)).prod (euclideanGaussianLaw (Fin r))) (t*w i)
        ≤ ∏ i, Real.exp ((t*w i)^2 * ‖operatorFrobenius T‖^2) := by
      apply Finset.prod_le_prod
      · intro i _
        exact mgf_nonneg
      · intro i _
        exact gaussian_bilinear_mgf_le T (t*w i) (hcap i)
    _ = Real.exp (t^2 * (∑ i, (w i)^2) * ‖operatorFrobenius T‖^2) := by
      rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Nonnegative-integral form, ready for an independent-current-block kernel. -/
theorem gaussian_weighted_bilinear_lintegral_le {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (w : ι → ℝ) (t : ℝ)
    (hcap : ∀ i, (t*w i)^2 * ‖T‖^2 ≤ 1/2) :
    (∫⁻ X : ι → Euclid q × Euclid r,
      ENNReal.ofReal (Real.exp (t * ∑ i, w i * ⟪T (X i).1,(X i).2⟫_ℝ))
      ∂gaussianBilinearSampleLaw ι q r) ≤
        ENNReal.ofReal (Real.exp (t^2 * (∑ i, (w i)^2) * ‖operatorFrobenius T‖^2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussian_weighted_bilinear_integrable T w t hcap)
    (Filter.Eventually.of_forall fun X => Real.exp_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (gaussian_weighted_bilinear_mgf_le T w t hcap)

#print axioms gaussian_weighted_bilinear_integral_factorization
#print axioms gaussian_weighted_bilinear_integrable
#print axioms gaussian_weighted_bilinear_mgf_le
#print axioms gaussian_weighted_bilinear_lintegral_le

end GaussianEllipsoidCandidate
