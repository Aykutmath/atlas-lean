import AHHGaussianEntropyTransfer

/-! Integrability and null-origin control for the genuine angular Gaussian weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers
open scoped BigOperators
namespace AHHRadial

theorem selectedRadius_integrable_inv_sq (n h : ℕ) (hh : 2 ≤ h)
    (i : Fin n) (second : Bool) :
    Integrable (fun r : Fin n → Radius × Radius =>
      (((((if second then (r i).2 else (r i).1) : Radius) : ℝ)^2)⁻¹))
      (radiiLaw n h) := by
  apply Integrable.of_integral_ne_zero
  rw [selectedRadius_integral_inv_sq n h hh i second]
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hh1 : (0 : ℝ) < (h : ℝ) - 1 := by
    have : (2 : ℝ) ≤ h := by exact_mod_cast hh
    linarith
  exact (div_pos hh0 hh1).ne'

theorem gaussian_angular_weight_div_norm_sq_integrable (n h : ℕ) [NeZero h]
    (hh : 2 ≤ h) (i : Fin n) (second : Bool)
    (W : Directions n h → ℝ) (hW : Integrable W (directionsLaw n h)) :
    Integrable (fun z : Fin n → CE h × CE h =>
      W (gaussianDirections n h z) / ‖if second then (z i).2 else (z i).1‖ ^ 2)
      (gaussianPairsLaw n h) := by
  have hh0 : 0 < h := by omega
  letI := radiiLaw_probability n h hh0
  letI := directionsLaw_probability n h hh0
  have hT := assembleSample_preserving n h hh0
  have hm : AEStronglyMeasurable (fun z : Fin n → CE h × CE h =>
      W (gaussianDirections n h z) / ‖if second then (z i).2 else (z i).1‖ ^ 2)
      (gaussianPairsLaw n h) := by
    have hw := hW.aestronglyMeasurable.comp_measurePreserving
      (gaussianDirections_preserving n h hh0)
    have hr : Measurable (fun z : Fin n → CE h × CE h =>
        (‖if second then (z i).2 else (z i).1‖ ^ 2)⁻¹) := by
      cases second <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop
    convert hw.mul hr.aestronglyMeasurable using 1
    funext z
    simp only [Pi.mul_apply, Function.comp_def, div_eq_mul_inv]
  apply (hT.integrable_comp hm).mp
  have hi := (selectedRadius_integrable_inv_sq n h hh i second).mul_prod hW
  have hn (w : (Fin n → Radius × Radius) × Directions n h) :
      ‖if second then (assembleSample n h w i).2 else (assembleSample n h w i).1‖ =
        (((if second then (w.1 i).2 else (w.1 i).1) : Radius) : ℝ) := by
    cases second
    · exact norm_assemble ((w.2 i).1, (w.1 i).1)
    · exact norm_assemble ((w.2 i).2, (w.1 i).2)
  simpa only [Function.comp_def, gaussianDirections_assembleSample, hn, div_eq_mul_inv,
    mul_comm (W _)] using hi

theorem gaussianPairs_ae_nonzero (n h : ℕ) (hh : 0 < h) :
    ∀ᵐ z ∂gaussianPairsLaw n h, ∀ i, (z i).1 ≠ 0 ∧ (z i).2 ≠ 0 := by
  letI : NeZero h := ⟨Nat.ne_of_gt hh⟩
  have hT := assembleSample_preserving n h hh
  rw [← hT.map_eq]
  apply (ae_map_iff hT.measurable.aemeasurable (by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl.inter
      (measurableSet_eq_fun (by fun_prop) measurable_const).compl)).mpr
  apply ae_of_all
  intro w i
  constructor
  · intro he
    have hn := norm_assemble ((w.2 i).1, (w.1 i).1)
    change ‖(assembleSample n h w i).1‖ = _ at hn
    rw [he, norm_zero] at hn
    exact (w.1 i).1.property.ne' hn.symm
  · intro he
    have hn := norm_assemble ((w.2 i).2, (w.1 i).2)
    change ‖(assembleSample n h w i).2‖ = _ at hn
    rw [he, norm_zero] at hn
    exact (w.1 i).2.property.ne' hn.symm

#print axioms gaussian_angular_weight_div_norm_sq_integrable
#print axioms gaussianPairs_ae_nonzero
end AHHRadial
