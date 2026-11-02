import BMNormalizedStein
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Nonpolynomial Gaussian integration by parts. This file extends the frozen
polynomial core via the actual Gaussian density and improper integration by
parts; no polynomial approximation or formal Stein premise is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Real
open scoped BigOperators

namespace BMGaussianSmoothStein

/-- The derivative of the actual standard Gaussian density. -/
theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    (1 / Real.sqrt (2*Real.pi))
  convert! h using 1
  · funext y
    simp [gaussianPDFReal]
  · simp [gaussianPDFReal]
    ring

/-- Integrability under Gaussian measure is exactly density-weighted Lebesgue
integrability. -/
theorem integrable_gaussian_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    (integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF 0 1) (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top) :
      Integrable f (volume.withDensity (gaussianPDF 0 1)) ↔
        Integrable (fun x => (gaussianPDF 0 1 x).toReal • f x))

/-- Actual Gaussian Stein identity for arbitrary differentiable functions.
The three assumptions are ordinary integrability conditions, not an assumed
Stein identity, normal approximation, or model-comparison premise. -/
theorem standardGaussian_smooth_stein (f f' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hxf : Integrable (fun x => x*f x) (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfρ := (integrable_gaussian_iff f).mp hf
  have hxfρ := (integrable_gaussian_iff (fun x => x*f x)).mp hxf
  have hf'ρ := (integrable_gaussian_iff f').mp hf'
  have hneg : Integrable (fun x => (-x * gaussianPDFReal 0 1 x) * f x) := by
    convert hxfρ.neg using 1
    funext x
    dsimp only [Pi.neg_apply]
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hasDerivAt_standardGaussianPDF x) (fun x _ => hderiv x) hf'ρ hneg hfρ
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  have he : (fun x => -x * gaussianPDFReal 0 1 x * f x) =
      fun x => -(gaussianPDFReal 0 1 x * (x*f x)) := by funext x; ring
  rw [he, integral_neg, neg_neg] at h
  exact h.symm

open GaussianTensorMoments

/-- Split off any designated coordinate of the actual Gaussian product law. -/
theorem integrable_insertNth_iff {n : ℕ} (i : Fin (n+1))
    (f : (Fin (n+1) → ℝ) → ℝ) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => f (i.insertNth z.1 z.2))
      ((gaussianReal 0 1).prod (gaussianProductLaw (Fin n))) ↔
      Integrable f (gaussianProductLaw (Fin (n+1))) := by
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  simpa only [gaussianProductLaw, Function.comp_def,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk] using
    he.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f)

/-- Exact Fubini formula with a designated Gaussian coordinate integrated first. -/
theorem integral_insertNth {n : ℕ} (i : Fin (n+1))
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : Integrable f (gaussianProductLaw (Fin (n+1)))) :
    (∫ x, f x ∂gaussianProductLaw (Fin (n+1))) =
      ∫ y, ∫ t, f (i.insertNth t y) ∂gaussianReal 0 1 ∂gaussianProductLaw (Fin n) := by
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
  have hi := (integrable_insertNth_iff i f).mpr hf
  have heq := he.integral_comp' f
  simp only [gaussianProductLaw, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Equiv.coe_fn_mk] at heq
  exact heq.symm.trans (integral_prod_symm _ hi)

/-- Multivariate Gaussian Stein identity for genuinely differentiable functions,
under the literal finite iid Gaussian law. -/
theorem gaussianProductLaw_smooth_stein {d : ℕ}
    (f f' : (Fin d → ℝ) → ℝ) (i : Fin d)
    (hderiv : ∀ x, HasDerivAt (fun t => f (Function.update x i t)) (f' x) (x i))
    (hf : Integrable f (gaussianProductLaw (Fin d)))
    (hxf : Integrable (fun x => x i*f x) (gaussianProductLaw (Fin d)))
    (hf' : Integrable f' (gaussianProductLaw (Fin d))) :
    (∫ x, x i*f x ∂gaussianProductLaw (Fin d)) =
      ∫ x, f' x ∂gaussianProductLaw (Fin d) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [integral_insertNth i _ hxf, integral_insertNth i _ hf']
    simp only [Fin.insertNth_apply_same]
    apply integral_congr_ae
    have hfS := ((integrable_insertNth_iff i f).mpr hf).prod_left_ae
    have hxfS := ((integrable_insertNth_iff i (fun x => x i*f x)).mpr hxf).prod_left_ae
    have hf'S := ((integrable_insertNth_iff i f').mpr hf').prod_left_ae
    filter_upwards [hfS, hxfS, hf'S] with y hy hxy hy'
    apply standardGaussian_smooth_stein _ _ _ hy _ hy'
    · intro t
      simpa only [Fin.update_insertNth, Fin.insertNth_apply_same] using
        hderiv (i.insertNth t y)
    · simpa only [Fin.insertNth_apply_same] using hxy

/-- The coordinate-update curve has its literal coordinate derivative. -/
theorem hasDerivAt_update_coordinate {d : ℕ} (x : Fin d → ℝ)
    (i j : Fin d) :
    HasDerivAt (fun t => Function.update x i t j) (if i = j then 1 else 0) (x i) := by
  by_cases hij : i = j
  · subst j
    simpa using! hasDerivAt_id (x i)
  · simpa [Function.update_of_ne (Ne.symm hij), hij] using hasDerivAt_const (x i) (x j)

/-- Exact nonpolynomial centered-pair Stein identity. -/
theorem gaussianProductLaw_centered_pair_smooth_stein {d : ℕ}
    (f fi : (Fin d → ℝ) → ℝ) (i j : Fin d)
    (hderiv : ∀ x, HasDerivAt (fun t => f (Function.update x i t)) (fi x) (x i))
    (hf : Integrable f (gaussianProductLaw (Fin d)))
    (hjf : Integrable (fun x => x j*f x) (gaussianProductLaw (Fin d)))
    (hijf : Integrable (fun x => x i*(x j*f x)) (gaussianProductLaw (Fin d)))
    (hjfi : Integrable (fun x => x j*fi x) (gaussianProductLaw (Fin d))) :
    (∫ x, (x i*x j - if i = j then 1 else 0)*f x ∂gaussianProductLaw (Fin d)) =
      ∫ x, x j*fi x ∂gaussianProductLaw (Fin d) := by
  have h := gaussianProductLaw_smooth_stein
    (fun x => x j*f x) (fun x => (if i = j then 1 else 0)*f x + x j*fi x) i
    (fun x => by
      have hh := (hasDerivAt_update_coordinate x i j).mul (hderiv x)
      simpa only [Function.update_eq_self, Function.update_self] using! hh)
    hjf hijf ((hf.const_mul _).add hjfi)
  have hcross : Integrable (fun x => (x i*x j)*f x) (gaussianProductLaw (Fin d)) := by
    simpa only [mul_assoc] using hijf
  simp_rw [sub_mul]
  rw [integral_sub hcross (hf.const_mul _)]
  rw [integral_add (hf.const_mul _) hjfi] at h
  simp only [mul_assoc] at *
  linarith

#print axioms standardGaussian_smooth_stein
end BMGaussianSmoothStein
