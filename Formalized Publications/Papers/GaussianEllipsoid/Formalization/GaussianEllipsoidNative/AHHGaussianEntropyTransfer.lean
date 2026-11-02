import AHHSphereMomentReduction
import AHHActualDirectionLaw
import AHHRadialGammaMoments

/-! Exact Gaussian-to-sphere entropy transport and the inverse-square radial
moment. These are unconditional ingredients for a Gaussian proof of the sphere
entropy bound. This module does not assert a Gaussian or sphere log-Sobolev
inequality, or the still missing Sobolev approximation theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory AHHBoundedPositiveMoments
open GaussianMixedNormHelpers
namespace AHHRadial

theorem gamma_integral_inv {a b : ℝ} (ha : 1 < a) (hb : 0 < b) :
    (∫ r : ℝ, r⁻¹ ∂gammaMeasure a b) = b / (a - 1) := by
  have ha0 : 0 < a := by linarith
  have ham : 0 < a - 1 := by linarith
  have hg : Real.Gamma a = (a - 1) * Real.Gamma (a - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one ham.ne'
  have hi := gamma_integral_rpow (q := -1) ha0 hb (by linarith)
  simp only [Real.rpow_neg_one, ← sub_eq_add_neg] at hi
  rw [hi, hg]
  field_simp [(Real.Gamma_pos_of_pos ham).ne', hb.ne', ham.ne']

theorem gamma_integrable_inv {a b : ℝ} (ha : 1 < a) (hb : 0 < b) :
    Integrable (fun r : ℝ => r⁻¹) (gammaMeasure a b) := by
  simpa only [Real.rpow_neg_one] using
    gamma_integrable_rpow (q := -1) (by linarith : 0 < a) hb (by linarith)

section GeneralRadial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

theorem radialGaussian_integral_inv_norm_sq {b : ℝ} (hb : 0 < b)
    (hdim : 2 < Module.finrank ℝ E) :
    (∫ x : E, (‖x‖^2)⁻¹ ∂radialGaussianLaw μ b) =
      b / ((Module.finrank ℝ E : ℝ) / 2 - 1) := by
  have ha : 1 < (Module.finrank ℝ E : ℝ) / 2 := by
    have hd : (2 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hdim
    linarith
  have he := integral_map (μ := radialGaussianLaw μ b) (φ := fun x : E => ‖x‖^2)
    (f := fun r : ℝ => r⁻¹) (by fun_prop) (by fun_prop)
  rw [radialGaussianLaw_map_norm_sq μ hb, gamma_integral_inv ha hb] at he
  exact he.symm

theorem radialGaussian_integrable_inv_norm_sq {b : ℝ} (hb : 0 < b)
    (hdim : 2 < Module.finrank ℝ E) :
    Integrable (fun x : E => (‖x‖^2)⁻¹) (radialGaussianLaw μ b) := by
  have ha : 1 < (Module.finrank ℝ E : ℝ) / 2 := by
    have hd : (2 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hdim
    linarith
  have hi := gamma_integrable_inv ha hb
  rw [← radialGaussianLaw_map_norm_sq μ hb] at hi
  exact (integrable_map_measure (by fun_prop : AEStronglyMeasurable
    (fun r : ℝ => r⁻¹) ((radialGaussianLaw μ b).map (fun x : E => ‖x‖^2)))
    (by fun_prop : AEMeasurable (fun x : E => ‖x‖^2) (radialGaussianLaw μ b))).mp hi

theorem radiusLaw_integral_inv_sq {b : ℝ} (hb : 0 < b)
    (hdim : 2 < Module.finrank ℝ E) :
    (∫ r : Radius, ((r : ℝ)^2)⁻¹ ∂radiusLaw μ b) =
      b / ((Module.finrank ℝ E : ℝ) / 2 - 1) := by
  have ha : 1 < (Module.finrank ℝ E : ℝ) / 2 := by
    have hd : (2 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hdim
    linarith
  have he := integral_map (μ := radiusLaw μ b) (φ := fun r : Radius => (r : ℝ)^2)
    (f := fun t : ℝ => t⁻¹) (by fun_prop) (by fun_prop)
  rw [radiusLaw_map_sq μ hb, gamma_integral_inv ha hb] at he
  exact he.symm

end GeneralRadial

theorem complex_gaussian_integral_inv_norm_sq (h : ℕ) (hh : 2 ≤ h)
    {b : ℝ} (hb : 0 < b) :
    (∫ x : CE h, (‖x‖^2)⁻¹ ∂radialGaussianLaw (volume : Measure (CE h)) b) =
      b / ((h : ℝ) - 1) := by
  letI : NeZero h := ⟨by omega⟩
  rw [radialGaussian_integral_inv_norm_sq _ hb
    (by rw [complex_finrank_real]; omega), complex_finrank_real]
  congr 1
  push_cast
  ring

/-- Apply the actual measurable normalization in every independent factor. -/
def gaussianDirections (n h : ℕ) [NeZero h]
    (z : Fin n → CE h × CE h) : Directions n h :=
  fun i => (direction (z i).1, direction (z i).2)

theorem gaussianDirections_preserving (n h : ℕ) [NeZero h] (hh : 0 < h) :
    MeasurePreserving (gaussianDirections n h) (gaussianPairsLaw n h)
      (directionsLaw n h) := by
  letI := gaussianPairLaw_probability h hh
  letI := directionPairLaw_probability h hh
  letI := radialGaussianLaw_isProbabilityMeasure (volume : Measure (CE h))
    (show (0 : ℝ) < h by exact_mod_cast hh)
  have hsingle : MeasurePreserving (direction (E := CE h))
      (radialGaussianLaw (volume : Measure (CE h)) h)
      (sphereLaw (volume : Measure (CE h))) :=
    ⟨measurable_direction, radialGaussian_direction_law _ (by exact_mod_cast hh)⟩
  exact measurePreserving_pi (fun _ : Fin n => gaussianPairLaw h)
    (fun _ => directionPairLaw h) (fun _ => hsingle.prod hsingle)

theorem powerEntropy_comp_measurePreserving
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {X : Ξ → ℝ} (hX : Measurable X) (p : ℝ) :
    powerEntropy P (X ∘ T) p = powerEntropy Q X p := by
  have hM : mgf (X ∘ T) P p = mgf X Q p := by
    unfold mgf
    have hm := integral_map (μ := P) (φ := T)
      (f := fun y => Real.exp (p * X y)) hT.measurable.aemeasurable
      ((hX.const_mul p).exp.aestronglyMeasurable)
    rw [hT.map_eq] at hm
    exact hm.symm
  have hI : (∫ x, (X ∘ T) x * Real.exp (p * (X ∘ T) x) ∂P) =
      ∫ y, X y * Real.exp (p * X y) ∂Q := by
    have hm := integral_map (μ := P) (φ := T)
      (f := fun y => X y * Real.exp (p * X y)) hT.measurable.aemeasurable
      ((hX.mul (hX.const_mul p).exp).aestronglyMeasurable)
    rw [hT.map_eq] at hm
    exact hm.symm
  simp only [powerEntropy, hM, hI]

/-- Entropy of the actual angular observable is unchanged by Gaussian
normalization. No concentration estimate is used. -/
theorem sphere_powerEntropy_eq_gaussian (n h : ℕ) [NeZero h]
    (hh : 0 < h) (p : ℝ) :
    powerEntropy (directionsLaw n h) (fun d => Real.log (unitCovarianceNorm n h d)) p =
      powerEntropy (gaussianPairsLaw n h)
        (fun z => Real.log (unitCovarianceNorm n h (gaussianDirections n h z))) p := by
  exact (powerEntropy_comp_measurePreserving (gaussianDirections_preserving n h hh)
    (continuous_unitCovarianceNorm n h).measurable.log p).symm

theorem sphere_rpow_integral_eq_gaussian (n h : ℕ) [NeZero h]
    (hh : 0 < h) (p : ℝ) :
    (∫ d, (unitCovarianceNorm n h d)^p ∂directionsLaw n h) =
      ∫ z, (unitCovarianceNorm n h (gaussianDirections n h z))^p
        ∂gaussianPairsLaw n h := by
  have hT := gaussianDirections_preserving n h hh
  have hm := integral_map (μ := gaussianPairsLaw n h) (φ := gaussianDirections n h)
    (f := fun d => (unitCovarianceNorm n h d)^p) hT.measurable.aemeasurable
    ((continuous_unitCovarianceNorm n h).measurable.pow_const p).aestronglyMeasurable
  rw [hT.map_eq] at hm
  exact hm

@[simp] theorem gaussianDirections_assembleSample (n h : ℕ) [NeZero h]
    (w : (Fin n → Radius × Radius) × Directions n h) :
    gaussianDirections n h (assembleSample n h w) = w.2 := by
  funext i
  apply Prod.ext
  · exact direction_assemble ((w.2 i).1, (w.1 i).1)
  · exact direction_assemble ((w.2 i).2, (w.1 i).2)

/-- The inverse-square moment of either selected radius in any sample. -/
theorem selectedRadius_integral_inv_sq (n h : ℕ) (hh : 2 ≤ h)
    (i : Fin n) (second : Bool) :
    (∫ r : Fin n → Radius × Radius,
      (((((if second then (r i).2 else (r i).1) : Radius) : ℝ)^2)⁻¹)
        ∂radiiLaw n h) = (h : ℝ) / ((h : ℝ) - 1) := by
  letI : NeZero h := ⟨by omega⟩
  have hh0 : 0 < h := by omega
  letI := radiusPairLaw_probability h hh0
  letI := radiusLaw_probability (volume : Measure (CE h))
    (show (0 : ℝ) < h by exact_mod_cast hh0)
  have hr : (∫ r : Radius, ((r : ℝ)^2)⁻¹
      ∂radiusLaw (volume : Measure (CE h)) h) = (h : ℝ) / ((h : ℝ) - 1) := by
    rw [radiusLaw_integral_inv_sq _ (by exact_mod_cast hh0)
      (by rw [complex_finrank_real]; omega), complex_finrank_real]
    congr 1
    push_cast
    ring
  cases second
  · change (∫ r, (((r i).1 : ℝ)^2)⁻¹ ∂radiiLaw n h) = _
    rw [radiiLaw, integral_comp_eval (μ := fun _ : Fin n => radiusPairLaw h)
      (i := i) (f := fun z : Radius × Radius => ((z.1 : ℝ)^2)⁻¹) (by fun_prop)]
    have he := integral_prod_mul (μ := radiusLaw (volume : Measure (CE h)) h)
      (ν := radiusLaw (volume : Measure (CE h)) h)
      (fun r : Radius => ((r : ℝ)^2)⁻¹) (fun _ : Radius => (1 : ℝ))
    simpa [radiusPairLaw, hr] using he
  · change (∫ r, (((r i).2 : ℝ)^2)⁻¹ ∂radiiLaw n h) = _
    rw [radiiLaw, integral_comp_eval (μ := fun _ : Fin n => radiusPairLaw h)
      (i := i) (f := fun z : Radius × Radius => ((z.2 : ℝ)^2)⁻¹) (by fun_prop)]
    have he := integral_prod_mul (μ := radiusLaw (volume : Measure (CE h)) h)
      (ν := radiusLaw (volume : Measure (CE h)) h)
      (fun _ : Radius => (1 : ℝ)) (fun r : Radius => ((r : ℝ)^2)⁻¹)
    simpa [radiusPairLaw, hr] using he

/-- Exact radial separation for an arbitrary measurable angular weight. This
is the scalar ingredient needed to integrate each component of angular energy.
It neither assumes nor proves differentiability or log-Sobolev. -/
theorem gaussian_angular_weight_div_norm_sq (n h : ℕ) [NeZero h]
    (hh : 2 ≤ h) (i : Fin n) (second : Bool)
    (W : Directions n h → ℝ) (hW : Measurable W) :
    (∫ z : Fin n → CE h × CE h,
      W (gaussianDirections n h z) / ‖if second then (z i).2 else (z i).1‖^2
        ∂gaussianPairsLaw n h) =
      (h : ℝ) / ((h : ℝ) - 1) * (∫ d, W d ∂directionsLaw n h) := by
  have hh0 : 0 < h := by omega
  letI := radiiLaw_probability n h hh0
  letI := directionsLaw_probability n h hh0
  have hT := assembleSample_preserving n h hh0
  have hm := integral_map (μ := (radiiLaw n h).prod (directionsLaw n h))
    (φ := assembleSample n h)
    (f := fun z : Fin n → CE h × CE h =>
      W (gaussianDirections n h z) / ‖if second then (z i).2 else (z i).1‖^2)
    hT.measurable.aemeasurable (by
      apply Measurable.aestronglyMeasurable
      apply Measurable.div
      · exact hW.comp (gaussianDirections_preserving n h hh0).measurable
      · cases second <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop)
  rw [hT.map_eq] at hm
  rw [hm]
  have hn (w : (Fin n → Radius × Radius) × Directions n h) :
      ‖if second then (assembleSample n h w i).2 else (assembleSample n h w i).1‖ =
        (((if second then (w.1 i).2 else (w.1 i).1) : Radius) : ℝ) := by
    cases second
    · exact norm_assemble ((w.2 i).1, (w.1 i).1)
    · exact norm_assemble ((w.2 i).2, (w.1 i).2)
  simp_rw [gaussianDirections_assembleSample, hn, div_eq_mul_inv, mul_comm (W _)]
  rw [integral_prod_mul (fun r : Fin n → Radius × Radius =>
    (((((if second then (r i).2 else (r i).1) : Radius) : ℝ)^2)⁻¹)) W,
    selectedRadius_integral_inv_sq n h hh i second, div_eq_mul_inv]

#print axioms gamma_integral_inv
#print axioms gamma_integrable_inv
#print axioms radialGaussian_integral_inv_norm_sq
#print axioms radialGaussian_integrable_inv_norm_sq
#print axioms complex_gaussian_integral_inv_norm_sq
#print axioms gaussianDirections_preserving
#print axioms powerEntropy_comp_measurePreserving
#print axioms sphere_powerEntropy_eq_gaussian
#print axioms sphere_rpow_integral_eq_gaussian
#print axioms radiusLaw_integral_inv_sq
#print axioms gaussianDirections_assembleSample
#print axioms selectedRadius_integral_inv_sq
#print axioms gaussian_angular_weight_div_norm_sq
end AHHRadial
