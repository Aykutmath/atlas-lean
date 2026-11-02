import AHHSphereObservableBounds

/-! Phase-aligned distances for products of complex unit vectors. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianMixedNormHelpers AHHAlgebraBridges
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHRadial

/-- A unit complex scalar rotates any complex number onto the nonnegative real axis. -/
theorem exists_unit_phase_mul (z : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, norm_one, by simp⟩
  · refine ⟨(‖z‖ : ℂ) / z, ?_, div_mul_cancel₀ _ hz⟩
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr hz)

/-- Inner products of product vectors factor into the two coordinate inner products. -/
theorem productVector_inner (h : ℕ) (x y x' y' : CE h) :
    inner ℂ (productVector h x y) (productVector h x' y') =
      inner ℂ x x' * inner ℂ y y' := by
  simp only [productVector, PiLp.inner_apply, RCLike.inner_apply,
    map_mul, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Multiplication of a vector by a unit complex scalar does not change its rank-one projector. -/
theorem rankOne_unit_phase {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (w : E) (c : ℂ) (hc : ‖c‖ = 1) :
    InnerProductSpace.rankOne ℂ (c • w) (c • w) =
      InnerProductSpace.rankOne ℂ w w := by
  have hcc : star c * c = (1 : ℂ) := by
    change (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    norm_num
  ext z
  simp only [InnerProductSpace.rankOne_apply, inner_smul_left, smul_smul,
    starRingEnd_apply]
  rw [mul_right_comm, hcc, one_mul]

/-- Tensor products of unit vectors admit a phase choice with a sharp product-distance bound. -/
theorem exists_productVector_unit_phase_distance (h : ℕ)
    (x y x' y' : UnitDirection h) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      ‖productVector h x y - c • productVector h x' y'‖ ^ 2 ≤
        ‖(x : CE h) - (x' : CE h)‖ ^ 2 +
          ‖(y : CE h) - (y' : CE h)‖ ^ 2 := by
  have hx : ‖(x : CE h)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖(y : CE h)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  have hx' : ‖(x' : CE h)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x'.property
  have hy' : ‖(y' : CE h)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y'.property
  let a : ℂ := inner ℂ (x : CE h) (x' : CE h)
  let b : ℂ := inner ℂ (y : CE h) (y' : CE h)
  obtain ⟨c, hc, hphase⟩ := exists_unit_phase_mul (a * b)
  refine ⟨c, hc, ?_⟩
  have ha : ‖a‖ ≤ 1 := by
    simpa only [a, hx, hx', one_mul] using norm_inner_le_norm (x : CE h) (x' : CE h)
  have hb : ‖b‖ ≤ 1 := by
    simpa only [b, hy, hy', one_mul] using norm_inner_le_norm (y : CE h) (y' : CE h)
  have hab : (1 - ‖a‖) * (1 - ‖b‖) ≥ 0 :=
    mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  have hreal : (inner ℂ (productVector h x y)
      (c • productVector h x' y')).re = ‖a‖ * ‖b‖ := by
    rw [inner_smul_right, productVector_inner]
    change (c * (a * b)).re = ‖a‖ * ‖b‖
    rw [hphase, Complex.ofReal_re, norm_mul]
  rw [@norm_sub_sq ℂ, @norm_sub_sq ℂ, @norm_sub_sq ℂ]
  rw [unit_productVector_norm, norm_smul, hc, unit_productVector_norm,
    hx, hx', hy, hy']
  change 1 ^ 2 - 2 * (inner ℂ (productVector h x y)
      (c • productVector h x' y')).re + (1 * 1) ^ 2 ≤
    (1 ^ 2 - 2 * a.re + 1 ^ 2) + (1 ^ 2 - 2 * b.re + 1 ^ 2)
  rw [hreal]
  nlinarith [Complex.re_le_norm a, Complex.re_le_norm b]

#print axioms exists_unit_phase_mul
#print axioms productVector_inner
#print axioms rankOne_unit_phase
#print axioms exists_productVector_unit_phase_distance
end AHHRadial
