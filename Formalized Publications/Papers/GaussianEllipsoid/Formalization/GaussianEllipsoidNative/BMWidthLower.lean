import BMWidthExpectation

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

def coneBadEvent (d : ℕ) (a C : ℝ) : Set ((Fin d × Fin d) → ℝ) :=
  {x | gaussianPSDSupportRaw d x < a*d} ∪
    {x | C*Real.sqrt d < ‖isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)‖}

theorem isotropicOpRaw_continuous (d : ℕ) :
    Continuous (fun x : (Fin d × Fin d) → ℝ => isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)) := by
  have h := (continuous_frobeniusOperator d d).comp (isotropicFrobeniusRaw_continuous d)
  simpa only [Function.comp_def, frobeniusOperator_operatorFrobenius] using h

theorem coneBadEvent_measurable (d : ℕ) (a C : ℝ) : MeasurableSet (coneBadEvent d a C) :=
  (measurableSet_lt (gaussianPSDSupportRaw_continuous d).measurable measurable_const).union
    (measurableSet_lt measurable_const (isotropicOpRaw_continuous d).norm.measurable)

theorem two_mul_le_young_dimension {g δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D) :
    2*g ≤ (δ/D)*g^2 + D/δ := by
  have heq : (δ/D)*g^2 + D/δ = (δ^2*g^2+D^2)/(δ*D) := by field_simp
  rw [heq]
  apply (le_div_iff₀ (mul_pos hδ hD)).mpr
  nlinarith [sq_nonneg (δ*g-D)]

theorem support_lower_with_bad_penalty {d : ℕ} (hd : 0 < d) {a C ε κ δ : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hε : 0 < ε) (hκ : 1 ≤ κ) (hκε : C+ε ≤ κ*ε)
    (hδ : 0 < δ) (x : (Fin d × Fin d) → ℝ) :
    gaussianPSDSupportRaw d x - ε*d*(1+C/a) - (δ/d)*gaussianSymmetricEnergy d x -
      (d/δ)*(coneBadEvent d a C).indicator (fun _ => (1:ℝ)) x ≤ gaussianConditionedSupportRaw d κ x := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  let T := isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)
  have hT := isotropicSymmetricOp_symmetric d ((WithLp.equiv 2 _).symm x)
  have hpos : 0 ≤ (δ/(d:ℝ))*gaussianSymmetricEnergy d x :=
    mul_nonneg (div_nonneg hδ.le hd'.le) (sq_nonneg _)
  have hloss : 0 ≤ ε*(d:ℝ)*(1+C/a) := by positivity
  by_cases hx : x ∈ coneBadEvent d a C
  · rw [Set.indicator_of_mem hx]
    have h1 := positive_norm_le_frobenius T hT
    have h2 := neg_norm_le_conditionedSupport hd hκ (operatorFrobenius T)
    have h3 := two_mul_le_young_dimension (g := ‖operatorFrobenius T‖) hδ hd'
    change gaussianPSDSupportRaw d x ≤ ‖operatorFrobenius T‖ at h1
    change -‖operatorFrobenius T‖ ≤ gaussianConditionedSupportRaw d κ x at h2
    change 2*‖operatorFrobenius T‖ ≤ (δ/(d:ℝ))*gaussianSymmetricEnergy d x + (d:ℝ)/δ at h3
    nlinarith
  · rw [Set.indicator_of_notMem hx, mul_zero, sub_zero]
    have hh : a*(d:ℝ) ≤ gaussianPSDSupportRaw d x ∧ ‖T‖ ≤ C*Real.sqrt d := by
      simpa only [coneBadEvent, Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] using hx
    have hnorm : ‖operatorFrobenius T‖ ≤ C*d := by
      have h := mul_le_mul_of_nonneg_left hh.2 (Real.sqrt_nonneg d)
      have hs := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
      have hf := frobenius_le_sqrt_dim_opNorm T
      nlinarith
    have h := conditionedSupport_lower_of_good_event hd T hT ha hε (zero_le_one.trans hκ) hκε hh.2 hh.1 hnorm
    change gaussianPSDSupportRaw d x - ε*d*(1+C/a) ≤ gaussianConditionedSupportRaw d κ x at h
    linarith

/-- Quantitative width lower bound with an explicit bad-event mass, all integrals under the actual
Gaussian entry law. Young's inequality avoids any unproved Gaussian uniform-integrability step. -/
theorem conditionedWidth_lower_with_bad_mass {d : ℕ} (hd : 0 < d) {a C ε κ δ : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hε : 0 < ε) (hκ : 1 ≤ κ) (hκε : C+ε ≤ κ*ε) (hδ : 0 < δ) :
    psdWidth d - ε*d*(1+C/a) - δ*(d+1)/2 -
      (d/δ)*(gaussianProductLaw (Fin d × Fin d)).real (coneBadEvent d a C) ≤ conditionedWidth d κ := by
  let μ := gaussianProductLaw (Fin d × Fin d)
  have hi : Integrable (fun x => gaussianPSDSupportRaw d x - ε*d*(1+C/a) - (δ/d)*gaussianSymmetricEnergy d x -
      (d/δ)*(coneBadEvent d a C).indicator (fun _ => (1:ℝ)) x) μ :=
    (((gaussianPSDSupportRaw_integrable d).sub (integrable_const _)).sub
      ((gaussianSymmetricEnergy_integrable d).const_mul _)).sub
      (((integrable_const (1:ℝ)).indicator (coneBadEvent_measurable d a C)).const_mul _)
  have h := integral_mono hi (gaussianConditionedSupportRaw_integrable hd hκ)
    (support_lower_with_bad_penalty hd ha hC hε hκ hκε hδ)
  have hfirst : Integrable (fun x => gaussianPSDSupportRaw d x - ε*d*(1+C/a)) μ :=
    (gaussianPSDSupportRaw_integrable d).sub (integrable_const _)
  have hsecond : Integrable (fun x => gaussianPSDSupportRaw d x - ε*d*(1+C/a) - (δ/d)*gaussianSymmetricEnergy d x) μ :=
    hfirst.sub ((gaussianSymmetricEnergy_integrable d).const_mul _)
  rw [integral_sub hsecond (((integrable_const (1:ℝ)).indicator (coneBadEvent_measurable d a C)).const_mul _),
    integral_sub hfirst ((gaussianSymmetricEnergy_integrable d).const_mul _),
    integral_sub (gaussianPSDSupportRaw_integrable d) (integrable_const _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator (coneBadEvent_measurable d a C)] at h
  simp only [μ, integral_const, probReal_univ, smul_eq_mul, one_mul,
    Measure.real, Measure.restrict_apply_univ, measure_univ, ENNReal.toReal_one, mul_one, psdWidth, conditionedWidth,
    gaussianSymmetricEnergy_mean] at h
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have heq : (δ/(d:ℝ))*((d:ℝ)*(d+1)/2) = δ*(d+1)/2 := by field_simp
  rw [heq] at h
  simpa only [psdWidth, conditionedWidth, Measure.real] using h

end BMGeometry
