import BMConeSupport
import BMGaussianEnergy
import BMOperatorTail

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

def psdWidth (d : ℕ) : ℝ := ∫ x, gaussianPSDSupportRaw d x ∂gaussianProductLaw (Fin d × Fin d)

def gaussianConditionedSupportRaw (d : ℕ) (κ : ℝ) (x : (Fin d × Fin d) → ℝ) : ℝ :=
  conditionedSupport d κ (operatorFrobenius (isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x)))

def conditionedWidth (d : ℕ) (κ : ℝ) : ℝ :=
  ∫ x, gaussianConditionedSupportRaw d κ x ∂gaussianProductLaw (Fin d × Fin d)

theorem gaussianPSDSupportRaw_integrable (d : ℕ) :
    Integrable (gaussianPSDSupportRaw d) (gaussianProductLaw (Fin d × Fin d)) :=
  MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq (gaussianPSDSupportRaw_continuous d).aestronglyMeasurable).mpr
      (gaussianPSDSupportRaw_sq_integrable d))

theorem psdWidth_nonneg (d : ℕ) : 0 ≤ psdWidth d :=
  integral_nonneg fun x => norm_nonneg _

/-- Exact variance-to-width step; the only premise here is a genuine centered-square integral bound. -/
theorem psdWidth_lower_of_variance {d : ℕ} {V : ℝ}
    (hvar : (∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2
      ∂gaussianProductLaw (Fin d × Fin d)) ≤ V) :
    Real.sqrt ((d : ℝ)*(d+1)/4 - V) ≤ psdWidth d := by
  let μ := gaussianProductLaw (Fin d × Fin d)
  have hexp : (∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2 ∂μ) =
      (d : ℝ)*(d+1)/4 - (psdWidth d)^2 := by
    have heq (x : (Fin d × Fin d) → ℝ) :
        (gaussianPSDSupportRaw d x - psdWidth d)^2 =
        (gaussianPSDSupportRaw d x)^2 - 2*psdWidth d*gaussianPSDSupportRaw d x + (psdWidth d)^2 := by ring
    simp_rw [heq]
    have hi : Integrable (fun x => (gaussianPSDSupportRaw d x)^2 - 2*psdWidth d*gaussianPSDSupportRaw d x) μ :=
      (gaussianPSDSupportRaw_sq_integrable d).sub ((gaussianPSDSupportRaw_integrable d).const_mul (2*psdWidth d))
    rw [integral_add hi (integrable_const _),
      integral_sub (gaussianPSDSupportRaw_sq_integrable d)
        ((gaussianPSDSupportRaw_integrable d).const_mul (2*psdWidth d)), integral_const_mul]
    simp only [μ, gaussianPSDSupportRaw_second_moment, integral_const, probReal_univ,
      smul_eq_mul, one_mul, psdWidth]
    ring
  rw [hexp] at hvar
  exact Real.sqrt_le_left (psdWidth_nonneg d) |>.mpr (by linarith)

theorem positive_norm_le_frobenius {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ‖operatorFrobenius (positivePart T hT)‖ ≤ ‖operatorFrobenius T‖ := by
  have h := positive_negative_energy T hT
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖operatorFrobenius (negativePart T hT)‖]

theorem isotropicFrobeniusRaw_continuous (d : ℕ) :
    Continuous (fun x : (Fin d × Fin d) → ℝ =>
      operatorFrobenius (isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x))) := by
  simp only [isotropicSymmetricOp_frobenius]
  exact (symmetricFrobLM d).continuous_of_finiteDimensional.comp
    ((frobeniusEquivEuclidean d d).symm.continuous.comp (PiLp.continuous_toLp _ _))

theorem isotropicFrobeniusRaw_norm_integrable (d : ℕ) :
    Integrable (fun x : (Fin d × Fin d) → ℝ =>
      ‖operatorFrobenius (isotropicSymmetricOp d ((WithLp.equiv 2 _).symm x))‖)
      (gaussianProductLaw (Fin d × Fin d)) :=
  MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((memLp_two_iff_integrable_sq (isotropicFrobeniusRaw_continuous d).norm.aestronglyMeasurable).mpr
      (gaussianSymmetricEnergy_integrable d))

theorem gaussianConditionedSupportRaw_integrable {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    Integrable (gaussianConditionedSupportRaw d κ) (gaussianProductLaw (Fin d × Fin d)) := by
  apply (isotropicFrobeniusRaw_norm_integrable d).mono'
    ((conditionedSupport_lipschitz hd hκ).continuous.comp (isotropicFrobeniusRaw_continuous d)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨neg_norm_le_conditionedSupport hd hκ _, conditionedSupport_le_norm hd hκ _⟩

theorem conditionedWidth_le_psdWidth {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    conditionedWidth d κ ≤ psdWidth d :=
  integral_mono (gaussianConditionedSupportRaw_integrable hd hκ) (gaussianPSDSupportRaw_integrable d)
    (fun x => conditionedSupport_le_psd hd hκ _ _)

end BMGeometry
