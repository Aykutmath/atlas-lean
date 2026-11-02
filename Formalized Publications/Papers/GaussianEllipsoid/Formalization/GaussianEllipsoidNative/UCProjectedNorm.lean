import GaussianChiSquareTail
import GaussianRadialDensity
import UCGaussianProjection
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianEllipsoidCandidate
open scoped ENNReal NNReal
namespace UCEscape

/-- Elementary lower-tail MGF factor, uniform in the relative deviation. -/
theorem chi_square_minus_factor_general (ε : ℝ) (hε : 0 ≤ ε) :
    (Real.sqrt (1 - 2 * (-ε / 4)))⁻¹ ≤ Real.exp (-ε / 4 + ε ^ 2 / 8) := by
  have ha : 0 < 1 + ε / 2 := by linarith
  apply inv_sqrt_le_exp_of_sq _ _ (by linarith)
  have hi : 0 < (1 + ε / 2)⁻¹ := inv_pos.mpr ha
  have hl := Real.log_le_sub_one_of_pos hi
  have hr : (1 + ε / 2)⁻¹ - 1 ≤ 2 * (-ε / 4 + ε ^ 2 / 8) := by
    apply (mul_le_mul_iff_of_pos_right ha).mp
    field_simp
    nlinarith [sq_nonneg ε, mul_nonneg hε (sq_nonneg ε)]
  have he := Real.exp_le_exp.mpr (hl.trans hr)
  rw [Real.exp_log hi] at he
  convert he using 2 <;> ring

/-- Uniform lower MGF bound, obtained from the exact finite Gaussian product integral. -/
theorem gaussian_square_sum_mgf_minus_general {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 ≤ ε) :
    mgf (fun x : ι → ℝ => ∑ i, (x i)^2) (gaussianProductLaw ι) (-ε / 4) ≤
      Real.exp ((Fintype.card ι : ℝ) * (-ε / 4 + ε ^ 2 / 8)) := by
  rw [gaussian_square_sum_mgf (-ε / 4) (by linarith)]
  calc
    _ ≤ (Real.exp (-ε / 4 + ε ^ 2 / 8)) ^ Fintype.card ι :=
      pow_le_pow_left₀ (by positivity) (chi_square_minus_factor_general ε hε) _
    _ = _ := (Real.exp_nat_mul _ _).symm

/-- Arbitrary relative lower deviation for the actual iid Gaussian square sum. -/
theorem gaussian_square_sum_lower_general {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianProductLaw ι).real
      {x : ι → ℝ | (∑ i, (x i)^2) ≤ (1 - ε) * Fintype.card ι} ≤
      Real.exp (-ε ^ 2 * (Fintype.card ι : ℝ) / 8) := by
  have hh := measure_le_le_exp_mul_mgf (μ := gaussianProductLaw ι)
    (X := fun x : ι → ℝ => ∑ i, (x i)^2) ((1 - ε) * Fintype.card ι)
    (t := -ε / 4) (by linarith)
    (gaussian_square_sum_exp_integrable (-ε / 4) (by linarith))
  apply hh.trans
  calc
    _ ≤ Real.exp (-(-ε / 4) * ((1 - ε) * Fintype.card ι)) *
        Real.exp ((Fintype.card ι : ℝ) * (-ε / 4 + ε ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left (gaussian_square_sum_mgf_minus_general ε hε)
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The project's Euclidean Gaussian realization equals mathlib's standard law. -/
theorem euclideanGaussianLaw_eq_stdGaussian {ι : Type*} [Fintype ι] :
    GaussianMixedNormHelpers.euclideanGaussianLaw ι = stdGaussian (EuclideanSpace ℝ ι) := by
  exact map_pi_eq_stdGaussian

/-- The actual standard Gaussian Euclidean norm has a relative lower-tail bound. -/
theorem stdGaussian_norm_lower_tail {ι : Type*} [Fintype ι]
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (stdGaussian (EuclideanSpace ℝ ι)).real
      {x | ‖x‖ ≤ (1 - ε) * Real.sqrt (Fintype.card ι)} ≤
      Real.exp (-ε ^ 2 * (Fintype.card ι : ℝ) / 8) := by
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.real, Measure.map_apply (by fun_prop) (by measurability)]
  change (gaussianProductLaw ι).real
    {x | ‖WithLp.toLp 2 x‖ ≤ (1 - ε) * Real.sqrt (Fintype.card ι)} ≤ _
  apply (measureReal_mono ?_).trans (gaussian_square_sum_lower_general ε hε)
  intro x hx
  have hc : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hc
  have hnorm : ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, (x i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq _
  have hsq := sq_le_sq₀ (norm_nonneg (WithLp.toLp 2 x))
    (show 0 ≤ (1 - ε) * Real.sqrt (Fintype.card ι) by positivity) |>.2 hx
  simp only [Set.mem_setOf_eq]
  rw [hnorm, mul_pow, hs] at hsq
  nlinarith [mul_nonneg hc (mul_nonneg hε (sub_nonneg.mpr hε1))]

/-- Orthogonal-frame projection lower tail, with no independence required between frames. -/
theorem projected_norm_lower_tail (n r : ℕ)
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin n))).real
      {x | ‖U.toContinuousLinearMap.adjoint x‖ ≤ (1 - ε) * Real.sqrt r} ≤
      Real.exp (-ε ^ 2 * (r : ℝ) / 8) := by
  have h := stdGaussian_norm_lower_tail (ι := Fin r) ε hε hε1
  simp only [Fintype.card_fin] at h
  rw [← stdGaussian_adjoint_isometry n r U] at h
  rw [Measure.real, Measure.map_apply (by fun_prop) (by measurability)] at h
  exact h

#print axioms gaussian_square_sum_lower_general
#print axioms stdGaussian_norm_lower_tail
#print axioms projected_norm_lower_tail
end UCEscape
