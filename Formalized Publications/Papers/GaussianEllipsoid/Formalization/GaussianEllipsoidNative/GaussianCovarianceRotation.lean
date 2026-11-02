/- Newly reconstructed analytic support, 2026-10-03. Not recovered original bytes.
   First-order covariance interpolation under the actual Gaussian product law. -/
import GaussianLipschitzIntegrability
import BMAffineSmooth
import BMRowInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open BMSmoothQuadraticComposition BMAffineSmooth MvPolynomial
open scoped BigOperators BoundedContinuousFunction

namespace GaussianCovarianceRotation
variable {d : ℕ}
abbrev Raw (d : ℕ) := Fin d → ℝ
abbrev γ (d : ℕ) := gaussianProductLaw (Fin d)
abbrev γ₂ (d : ℕ) := (γ d).prod (γ d)

def first (t : ℝ) (z : Raw d × Raw d) : Raw d :=
  Real.cos t • z.1 + Real.sin t • z.2

def second (t : ℝ) (z : Raw d × Raw d) : Raw d :=
  -Real.sin t • z.1 + Real.cos t • z.2

def rotate (t : ℝ) (z : Raw d × Raw d) : Raw d × Raw d :=
  (first t z, second t z)

theorem rotate_preserving (t : ℝ) : MeasurePreserving (rotate (d := d) t) (γ₂ d) (γ₂ d) := by
  let e := MeasurableEquiv.toLp 2 (Raw d)
  have hp := BMQuadraticSpectral.coordinates_preserving (ι := Fin d)
  have h := (hp.prod hp).comp ((GaussianVariance.pairRotation_preserving (ι := Fin d) t).comp
    (hp.symm.prod hp.symm))
  convert h using 1
  funext z
  rw [Function.comp_apply, Function.comp_apply, GaussianVariance.pairRotation_apply]
  rfl

/-- A bounded test is Gaussian-integrable. -/
theorem integrable_bounded (f : Raw d →ᵇ ℝ) : Integrable f (γ d) := by
  simpa only [mul_one] using (integrable_const (1 : ℝ) : Integrable (fun _ : Raw d => (1 : ℝ)) (γ d)).bdd_mul
    f.continuous.aestronglyMeasurable (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- Coordinate Stein identity for an affine image of a bounded C¹ test. -/
theorem affine_coordinate_stein (F : SmoothTest (Fin d)) (c : ℝ) (v : Raw d) (i : Fin d) :
    (∫ y, y i * F.value (c • y + v) ∂γ d) =
      c * ∫ y, F.gradient i (c • y + v) ∂γ d := by
  let G := affineTest F c v
  have hD (y : Raw d) : HasDerivAt (fun t => G.value (Function.update y i t))
      (G.gradient i y) (y i) := by
    have hu : HasDerivAt (fun t => Function.update y i t)
        (Pi.single i (1 : ℝ)) (y i) := by
      apply hasDerivAt_pi.mpr
      intro j
      simpa only [Pi.single_apply, eq_comm] using
        BMGaussianSmoothStein.hasDerivAt_update_coordinate y i j
    have hh := (G.hasFDeriv y).comp_hasDerivAt_of_eq (y i) hu (Function.update_eq_self i y).symm
    simpa only [Function.comp_def, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hh
  have hx : Integrable (fun y => y i * G.value y) (γ d) := by
    simpa only [eval_X] using integrable_poly_bounded G.value (X i)
  have hh := BMGaussianSmoothStein.gaussianProductLaw_smooth_stein G.value (G.gradient i) i
    hD (integrable_bounded G.value) hx (integrable_bounded (G.gradient i))
  simpa only [G, affineTest, BoundedContinuousFunction.compContinuous_apply,
    BoundedContinuousFunction.smul_apply, affineMap, ContinuousMap.coe_mk, smul_eq_mul,
    integral_const_mul] using hh

def firstMap (t : ℝ) : C(Raw d × Raw d, Raw d) :=
  ⟨first t, by unfold first; fun_prop⟩

def fstMap : C(Raw d × Raw d, Raw d) := ⟨Prod.fst, continuous_fst⟩

theorem first_rotate_neg (t : ℝ) (z : Raw d × Raw d) :
    first t (rotate (-t) z) = z.1 := by
  ext i
  simp only [first, rotate, second, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Real.cos_neg, Real.sin_neg, neg_neg]
  linear_combination z.1 i * Real.sin_sq_add_cos_sq t

theorem second_rotate_neg (t : ℝ) (z : Raw d × Raw d) :
    second t (rotate (-t) z) = z.2 := by
  ext i
  simp only [first, rotate, second, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Real.cos_neg, Real.sin_neg, neg_neg]
  linear_combination z.2 i * Real.sin_sq_add_cos_sq t

/-- Stein after rotating the Gaussian pair: the derivative falls on `F`,
so no second derivative of the other factor is needed. -/
theorem rotated_coordinate_stein (F : SmoothTest (Fin d))
    (g : Raw d →ᵇ ℝ) (t : ℝ) (i : Fin d) :
    (∫ z, F.value (first (-t) z) * g z.1 * z.2 i ∂γ₂ d) =
      -Real.sin t * ∫ z, F.gradient i (first (-t) z) * g z.1 ∂γ₂ d := by
  let b : (Raw d × Raw d) →ᵇ ℝ :=
    (F.value.compContinuous (firstMap (-t))) * (g.compContinuous fstMap)
  let b' : (Raw d × Raw d) →ᵇ ℝ :=
    ((F.gradient i).compContinuous (firstMap (-t))) * (g.compContinuous fstMap)
  have hi : Integrable (fun z : Raw d × Raw d =>
      F.value (first (-t) z) * g z.1 * z.2 i) (γ₂ d) := by
    have hh := BMRowInterpolation.integrable_snd_poly_mul (d := d) (m := d) (X i) b
    simpa only [b, BMRowInterpolation.law, eval_X,
      BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.compContinuous_apply,
      firstMap, fstMap, ContinuousMap.coe_mk, mul_comm] using hh
  have hi' : Integrable (fun z : Raw d × Raw d =>
      F.gradient i (first (-t) z) * g z.1) (γ₂ d) := by
    convert! BMRowInterpolation.integrable_bounded b' using 1
  rw [integral_prod _ hi, integral_prod _ hi', ← integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hpoint (y : Raw d) : first (-t) (x,y) = -Real.sin t • y + Real.cos t • x := by
    ext j
    simp only [first, Real.cos_neg, Real.sin_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hpoint]
  have h := affine_coordinate_stein F (-Real.sin t) (Real.cos t • x) i
  calc
    (∫ y, F.value (-Real.sin t • y + Real.cos t • x) * g x * y i ∂γ d) =
        g x * ∫ y, y i * F.value (-Real.sin t • y + Real.cos t • x) ∂γ d := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = -Real.sin t * ∫ y, F.gradient i (-Real.sin t • y + Real.cos t • x) * g x ∂γ d := by
      rw [h, integral_mul_const]
      ring

def covariancePath (F G : SmoothTest (Fin d)) (t : ℝ) (z : Raw d × Raw d) : ℝ :=
  F.value z.1 * G.value (first t z)

def pathVelocity (F G : SmoothTest (Fin d)) (t : ℝ) (z : Raw d × Raw d) : ℝ :=
  F.value z.1 * ∑ i, G.gradient i (first t z) * second t z i

def velocityEnvelope (F G : SmoothTest (Fin d)) (z : Raw d × Raw d) : ℝ :=
  ‖F.value‖ * ∑ i, ‖G.gradient i‖ * (|z.1 i| + |z.2 i|)

theorem hasDerivAt_covariancePath (F G : SmoothTest (Fin d))
    (t : ℝ) (z : Raw d × Raw d) :
    HasDerivAt (fun s => covariancePath F G s z) (pathVelocity F G t z) t := by
  have hf : HasDerivAt (fun s => first s z) (second t z) t := by
    exact ((Real.hasDerivAt_cos t).smul_const z.1).add ((Real.hasDerivAt_sin t).smul_const z.2)
  have hh := ((G.hasFDeriv (first t z)).comp_hasDerivAt t hf).const_mul (F.value z.1)
  simpa only [covariancePath, pathVelocity, Function.comp_def,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] using hh

theorem velocityEnvelope_integrable (F G : SmoothTest (Fin d)) :
    Integrable (velocityEnvelope F G) (γ₂ d) := by
  apply Integrable.const_mul
  apply integrable_finset_sum
  intro i hi
  apply Integrable.const_mul
  have h1 := (BMRowInterpolation.integrable_fst_poly (d := d) (m := d) (X i)).norm
  have h2 := (BMRowInterpolation.integrable_snd_poly (d := d) (m := d) (X i)).norm
  simpa only [eval_X, Real.norm_eq_abs] using! h1.add h2

theorem pathVelocity_norm_le (F G : SmoothTest (Fin d)) (t : ℝ) (z : Raw d × Raw d) :
    ‖pathVelocity F G t z‖ ≤ velocityEnvelope F G z := by
  rw [pathVelocity, norm_mul]
  apply mul_le_mul (F.value.norm_coe_le_norm z.1) _ (norm_nonneg _) (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  apply mul_le_mul (G.gradient i |>.norm_coe_le_norm _) _ (norm_nonneg _) (norm_nonneg _)
  change |(-Real.sin t) * z.1 i + Real.cos t * z.2 i| ≤ |z.1 i| + |z.2 i|
  calc
    _ ≤ |(-Real.sin t)*z.1 i| + |Real.cos t*z.2 i| := abs_add_le _ _
    _ ≤ |z.1 i| + |z.2 i| := by
      simp only [abs_mul, abs_neg]
      exact add_le_add (by nlinarith [Real.abs_sin_le_one t, abs_nonneg (z.1 i)])
        (by nlinarith [Real.abs_cos_le_one t, abs_nonneg (z.2 i)])

theorem pathVelocity_integrable (F G : SmoothTest (Fin d)) (t : ℝ) :
    Integrable (pathVelocity F G t) (γ₂ d) := by
  apply (velocityEnvelope_integrable F G).mono'
  · apply Continuous.aestronglyMeasurable
    unfold pathVelocity first second
    fun_prop
  · exact ae_of_all _ (pathVelocity_norm_le F G t)

theorem covariancePath_integrable (F G : SmoothTest (Fin d)) (t : ℝ) :
    Integrable (covariancePath F G t) (γ₂ d) := by
  convert! BMRowInterpolation.integrable_bounded
    ((F.value.compContinuous fstMap) * (G.value.compContinuous (firstMap t))) using 1

theorem hasDerivAt_expected_covariancePath (F G : SmoothTest (Fin d)) (t : ℝ) :
    HasDerivAt (fun s => ∫ z, covariancePath F G s z ∂γ₂ d)
      (∫ z, pathVelocity F G t z ∂γ₂ d) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (covariancePath_integrable F G s).aestronglyMeasurable)
    (covariancePath_integrable F G t) (pathVelocity_integrable F G t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => fun s _ => pathVelocity_norm_le F G s z)
    (velocityEnvelope_integrable F G)
    (Filter.Eventually.of_forall fun z => fun s _ => hasDerivAt_covariancePath F G s z)).2

/-- Exact first-order covariance interpolation identity. -/
theorem expected_pathVelocity (F G : SmoothTest (Fin d)) (t : ℝ) :
    (∫ z, pathVelocity F G t z ∂γ₂ d) =
      -Real.sin t * ∫ z, ∑ i, F.gradient i (first (-t) z) * G.gradient i z.1 ∂γ₂ d := by
  have hr : (∫ z, pathVelocity F G t (rotate (-t) z) ∂γ₂ d) =
      ∫ z, pathVelocity F G t z ∂γ₂ d := by
    have hp := rotate_preserving (d := d) (-t)
    have hm := (pathVelocity_integrable F G t).aestronglyMeasurable
    have hm' : AEStronglyMeasurable (pathVelocity F G t) (Measure.map (rotate (-t)) (γ₂ d)) := by
      rwa [hp.map_eq]
    calc
      _ = ∫ z, pathVelocity F G t z ∂Measure.map (rotate (-t)) (γ₂ d) :=
        (integral_map hp.measurable.aemeasurable hm').symm
      _ = _ := by rw [hp.map_eq]
  have hpoint (z : Raw d × Raw d) : pathVelocity F G t (rotate (-t) z) =
      ∑ i, F.value (first (-t) z) * G.gradient i z.1 * z.2 i := by
    unfold pathVelocity
    rw [first_rotate_neg, second_rotate_neg]
    change F.value (first (-t) z) * (∑ i, G.gradient i z.1 * z.2 i) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hi (i : Fin d) : Integrable (fun z : Raw d × Raw d =>
      F.value (first (-t) z) * G.gradient i z.1 * z.2 i) (γ₂ d) := by
    let b : (Raw d × Raw d) →ᵇ ℝ :=
      (F.value.compContinuous (firstMap (-t))) * ((G.gradient i).compContinuous fstMap)
    have hh := BMRowInterpolation.integrable_snd_poly_mul (d := d) (m := d) (X i) b
    simpa only [b, BMRowInterpolation.law, eval_X,
      BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.compContinuous_apply,
      firstMap, fstMap, ContinuousMap.coe_mk, mul_comm] using hh
  have hi' (i : Fin d) : Integrable (fun z : Raw d × Raw d =>
      F.gradient i (first (-t) z) * G.gradient i z.1) (γ₂ d) := by
    convert! BMRowInterpolation.integrable_bounded
      (((F.gradient i).compContinuous (firstMap (-t))) * ((G.gradient i).compContinuous fstMap)) using 1
  rw [← hr]
  simp_rw [hpoint]
  rw [integral_finset_sum _ (fun i _ => hi i)]
  simp_rw [rotated_coordinate_stein]
  rw [← Finset.mul_sum, integral_finset_sum _ (fun i _ => hi' i)]

#print axioms rotate_preserving
#print axioms affine_coordinate_stein
#print axioms rotated_coordinate_stein
#print axioms hasDerivAt_expected_covariancePath
#print axioms expected_pathVelocity
end GaussianCovarianceRotation
