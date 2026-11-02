import BMWidthExpectation

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
open GaussianEllipsoid GaussianTensorMoments MeasureTheory ProbabilityTheory
namespace BMGeometry

/-- Sharp upper bound for the Gaussian PSD Frobenius-unit cone width. -/
theorem psdWidth_sq_le (d : ℕ) :
    (psdWidth d)^2 ≤ (d : ℝ)*(d+1)/4 := by
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
  have hn : 0 ≤ ∫ x, (gaussianPSDSupportRaw d x - psdWidth d)^2 ∂μ :=
    integral_nonneg fun x => sq_nonneg _
  rw [hexp] at hn
  linarith

theorem psdWidth_le_sqrt (d : ℕ) :
    psdWidth d ≤ Real.sqrt ((d : ℝ)*(d+1)/4) := by
  have hd : 0 ≤ (d : ℝ)*(d+1)/4 := by positivity
  have h := psdWidth_sq_le d
  nlinarith [Real.sq_sqrt hd, Real.sqrt_nonneg ((d : ℝ)*(d+1)/4)]

/-- The exact leading width constant is one half, with an explicit finite-d correction. -/
theorem psdWidth_le_half_dimension (d : ℕ) :
    psdWidth d ≤ (d : ℝ)/2 + 1/4 := by
  have h := psdWidth_sq_le d
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg (psdWidth d - ((d : ℝ)/2+1/4))]

#print axioms psdWidth_sq_le
#print axioms psdWidth_le_sqrt
#print axioms psdWidth_le_half_dimension
end BMGeometry
