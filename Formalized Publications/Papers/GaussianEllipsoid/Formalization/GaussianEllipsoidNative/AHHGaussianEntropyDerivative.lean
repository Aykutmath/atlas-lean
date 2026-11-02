import AHHGaussianSemigroup
import AHHGaussianLogTest
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Differentiation of entropy along Gaussian rotation averaging. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter MvPolynomial
open GaussianTensorMoments BMSmoothQuadraticComposition GaussianCovarianceRotation
open AHHGaussianSemigroup
open scoped BigOperators BoundedContinuousFunction Topology

namespace AHHGaussianEntropyDerivative
variable {d : ℕ}

def velocity (F : SmoothTest (Fin d)) (t : ℝ) (z : Raw d × Raw d) : ℝ :=
  ∑ i, F.gradient i (first t z) * second t z i

def envelope (F : SmoothTest (Fin d)) (z : Raw d × Raw d) : ℝ :=
  ∑ i, ‖F.gradient i‖ * (|z.1 i| + |z.2 i|)

theorem hasDerivAt_first_value (F : SmoothTest (Fin d))
    (t : ℝ) (z : Raw d × Raw d) :
    HasDerivAt (fun s => F.value (first s z)) (velocity F t z) t := by
  have hf : HasDerivAt (fun s => first s z) (second t z) t :=
    ((Real.hasDerivAt_cos t).smul_const z.1).add ((Real.hasDerivAt_sin t).smul_const z.2)
  have hh := (F.hasFDeriv (first t z)).comp_hasDerivAt t hf
  simpa only [velocity, Function.comp_def, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul] using hh

theorem velocity_norm_le (F : SmoothTest (Fin d)) (t : ℝ) (z : Raw d × Raw d) :
    ‖velocity F t z‖ ≤ envelope F z := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  apply mul_le_mul (F.gradient i |>.norm_coe_le_norm _) _ (norm_nonneg _) (norm_nonneg _)
  change |(-Real.sin t) * z.1 i + Real.cos t * z.2 i| ≤ |z.1 i| + |z.2 i|
  calc
    _ ≤ |(-Real.sin t)*z.1 i| + |Real.cos t*z.2 i| := abs_add_le _ _
    _ ≤ |z.1 i| + |z.2 i| := by
      simp only [abs_mul, abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t, abs_nonneg (z.1 i)])
        (by nlinarith [Real.abs_cos_le_one t, abs_nonneg (z.2 i)])

theorem envelope_integrable (F : SmoothTest (Fin d)) : Integrable (envelope F) (γ₂ d) := by
  apply integrable_finset_sum
  intro i hi
  apply Integrable.const_mul
  have h1 := (BMRowInterpolation.integrable_fst_poly (d := d) (m := d) (X i)).norm
  have h2 := (BMRowInterpolation.integrable_snd_poly (d := d) (m := d) (X i)).norm
  simpa only [eval_X, Real.norm_eq_abs] using! h1.add h2

theorem envelope_section_integrable (F : SmoothTest (Fin d)) (x : Raw d) :
    Integrable (fun y => envelope F (x,y)) (γ d) := by
  apply integrable_finset_sum
  intro i hi
  apply Integrable.const_mul
  have h := (gaussianProductLaw_integrable_polynomial (X i : MvPolynomial (Fin d) ℝ)).norm
  simpa only [eval_X, Real.norm_eq_abs] using! (integrable_const |x i|).add h

theorem velocity_integrable (F : SmoothTest (Fin d)) (t : ℝ) :
    Integrable (velocity F t) (γ₂ d) := by
  apply (envelope_integrable F).mono'
  · apply Continuous.aestronglyMeasurable
    unfold velocity first second
    fun_prop
  · exact ae_of_all _ (velocity_norm_le F t)

theorem velocity_section_integrable (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) :
    Integrable (fun y => velocity F t (x,y)) (γ d) := by
  apply (envelope_section_integrable F x).mono'
  · apply Continuous.aestronglyMeasurable
    unfold velocity first second
    fun_prop
  · exact ae_of_all _ fun y => velocity_norm_le F t (x,y)

def averageVelocity (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) : ℝ :=
  ∫ y, velocity F t (x,y) ∂γ d

def averageEnvelope (F : SmoothTest (Fin d)) (x : Raw d) : ℝ :=
  ∫ y, envelope F (x,y) ∂γ d

theorem hasDerivAt_average (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) :
    HasDerivAt (fun s => average F.value s x) (averageVelocity F t x) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (integrable_first F.value s x).aestronglyMeasurable)
    (integrable_first F.value t x) (velocity_section_integrable F t x).aestronglyMeasurable
    (ae_of_all _ fun y s _ => velocity_norm_le F s (x,y))
    (envelope_section_integrable F x)
    (ae_of_all _ fun y s _ => hasDerivAt_first_value F s (x,y))).2

theorem averageVelocity_integrable (F : SmoothTest (Fin d)) (t : ℝ) :
    Integrable (averageVelocity F t) (γ d) := by
  exact (velocity_integrable F t).integral_prod_left

theorem averageEnvelope_integrable (F : SmoothTest (Fin d)) :
    Integrable (averageEnvelope F) (γ d) := by
  exact (envelope_integrable F).integral_prod_left

theorem averageVelocity_norm_le (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) :
    ‖averageVelocity F t x‖ ≤ averageEnvelope F x := by
  apply (norm_integral_le_integral_norm _).trans
  exact integral_mono (velocity_section_integrable F t x).norm
    (envelope_section_integrable F x) (fun y => velocity_norm_le F t (x,y))



/-- A uniform (in time and space) logarithm bound. -/
def logBound (F : SmoothTest (Fin d)) (c : ℝ) : ℝ :=
  |Real.log c| + |Real.log ‖F.value‖|

theorem log_average_norm_le (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) (x : Raw d) :
    ‖Real.log (average F.value t x)‖ ≤ logBound F c := by
  exact AHHGaussianLogTest.norm_log_le_of_bounds hc (average_lower F.value hcf t x)
    (by
      have h := average_norm_le F.value t x
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h)

theorem continuous_log_average (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    Continuous (fun x => Real.log (average F.value t x)) := by
  exact ((continuous_average F.value).comp (continuous_const.prodMk continuous_id)).log
    (fun x => (hc.trans_le (average_lower F.value hcf t x)).ne')

def entropyDensity (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) : ℝ :=
  average F.value t x * Real.log (average F.value t x)

def entropyVelocity (F : SmoothTest (Fin d)) (t : ℝ) (x : Raw d) : ℝ :=
  (Real.log (average F.value t x) + 1) * averageVelocity F t x

theorem entropyDensity_integrable (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    Integrable (entropyDensity F t) (γ d) := by
  apply Integrable.of_bound (C := ‖F.value‖ * logBound F c)
  · exact (((continuous_average F.value).comp (continuous_const.prodMk continuous_id)).mul
      (continuous_log_average F hc hcf t)).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      rw [entropyDensity, norm_mul]
      exact mul_le_mul (average_norm_le F.value t x) (log_average_norm_le F hc hcf t x)
        (norm_nonneg _) (norm_nonneg _)

theorem logOne_average_norm_le (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) (x : Raw d) :
    ‖Real.log (average F.value t x) + 1‖ ≤ logBound F c + 1 := by
  apply (norm_add_le _ _).trans
  simp only [norm_one]
  linarith [log_average_norm_le F hc hcf t x]

theorem entropyVelocity_integrable (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    Integrable (entropyVelocity F t) (γ d) := by
  exact (averageVelocity_integrable F t).bdd_mul
    ((continuous_log_average F hc hcf t).add continuous_const).aestronglyMeasurable
    (ae_of_all _ fun x => logOne_average_norm_le F hc hcf t x)

theorem entropyVelocity_norm_le (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) (x : Raw d) :
    ‖entropyVelocity F t x‖ ≤ (logBound F c + 1) * averageEnvelope F x := by
  rw [entropyVelocity, norm_mul]
  exact mul_le_mul (logOne_average_norm_le F hc hcf t x)
    (averageVelocity_norm_le F t x) (norm_nonneg _) (by unfold logBound; positivity)

theorem hasDerivAt_entropyDensity (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) (x : Raw d) :
    HasDerivAt (fun s => entropyDensity F s x) (entropyVelocity F t x) t := by
  have hpos := hc.trans_le (average_lower F.value hcf t x)
  have hd := hasDerivAt_average F t x
  convert! hd.mul (hd.log hpos.ne') using 1
  unfold entropyVelocity
  field_simp

/-- Differentiation of the expected entropy density under the outer Gaussian integral. -/
theorem hasDerivAt_expected_entropyDensity (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, entropyDensity F s x ∂γ d)
      (∫ x, entropyVelocity F t x ∂γ d) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (entropyDensity_integrable F hc hcf s).aestronglyMeasurable)
    (entropyDensity_integrable F hc hcf t) (entropyVelocity_integrable F hc hcf t).aestronglyMeasurable
    (ae_of_all _ fun x s _ => entropyVelocity_norm_le F hc hcf s x)
    ((averageEnvelope_integrable F).const_mul (logBound F c + 1))
    (ae_of_all _ fun x s _ => hasDerivAt_entropyDensity F hc hcf s x)).2

/-- The same derivative in the product-law form needed by rotated Stein. -/
theorem hasDerivAt_expected_entropyDensity_product (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, entropyDensity F s x ∂γ d)
      (∫ z, (Real.log (average F.value t z.1) + 1) * velocity F t z ∂γ₂ d) t := by
  have hi : Integrable (fun z : Raw d × Raw d =>
      (Real.log (average F.value t z.1) + 1) * velocity F t z) (γ₂ d) :=
    (velocity_integrable F t).bdd_mul
      (((continuous_log_average F hc hcf t).comp continuous_fst).add
        continuous_const).aestronglyMeasurable
      (ae_of_all _ fun z => logOne_average_norm_le F hc hcf t z.1)
  have h := hasDerivAt_expected_entropyDensity F hc hcf t
  convert! h using 1
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change (∫ y, (Real.log (average F.value t x) + 1) * velocity F t (x,y) ∂γ d) = _
    rw [integral_const_mul]
    rfl

theorem hasDerivAt_entropy (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, average F.value s x * Real.log (average F.value s x) ∂γ d)
      (∫ z, (Real.log (average F.value t z.1) + 1) * velocity F t z ∂γ₂ d) t :=
  hasDerivAt_expected_entropyDensity_product F hc hcf t

/-- Entropy derivative packaged as the velocity of the logarithmic smooth test. -/
theorem hasDerivAt_entropy_logOneTest (F : SmoothTest (Fin d)) {c : ℝ}
    (hc : 0 < c) (hcf : ∀ x, c ≤ F.value x) (t : ℝ) :
    HasDerivAt (fun s => ∫ x, average F.value s x * Real.log (average F.value s x) ∂γ d)
      (∫ z, pathVelocity
        (AHHGaussianLogTest.logOneTest (averageTest F t) hc (average_lower F.value hcf t))
        F t z ∂γ₂ d) t := by
  simpa only [entropyDensity, pathVelocity, AHHGaussianLogTest.logOneTest_value,
    averageTest, averageBounded_apply, velocity] using!
    hasDerivAt_expected_entropyDensity_product F hc hcf t

#print axioms hasDerivAt_entropy_logOneTest
end AHHGaussianEntropyDerivative
