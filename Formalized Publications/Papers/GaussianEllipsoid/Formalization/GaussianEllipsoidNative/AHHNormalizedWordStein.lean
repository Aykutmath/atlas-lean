import AHHGaussianWordStein
import AHHNormalizedWordGluing

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped BigOperators
namespace AHHGaussian

theorem normalizedWordMean_eq_raw (n h : ℕ) (w : List (Fin n)) :
    normalizedWordMean n h w = ((2 * (h : ℝ))⁻¹) ^ w.length *
      (∫ x : ((Fin n × Fin h) × Bool) → ℝ, Matrix.trace (AHH.gaussianWordMatrix x w)
        ∂gaussianProductLaw ((Fin n × Fin h) × Bool)).re := by
  unfold normalizedWordMean
  rw [normalizedWordTrace_integral]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem normalizedWordPairMean_eq_raw (n h : ℕ) (w v : List (Fin n)) :
    normalizedWordPairMean n h w v = ((2 * (h : ℝ))⁻¹) ^ (w.length + v.length) *
      (∫ x : ((Fin n × Fin h) × Bool) → ℝ,
        Matrix.trace (AHH.gaussianWordMatrix x w) * Matrix.trace (AHH.gaussianWordMatrix x v)
        ∂gaussianProductLaw ((Fin n × Fin h) × Bool)).re := by
  unfold normalizedWordPairMean
  rw [normalizedWordTrace_mul_integral]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Exact one-subsystem loop equation for the actual normalized complex
Gaussian law. Its coefficient is 1/h, including arbitrary repeated labels. -/
theorem normalizedWordMean_position_loop (n h : ℕ) (hh : 0 < h)
    (s : Fin n) (w : List (Fin n)) :
    normalizedWordMean n h (s :: w) =
      (normalizedWordMean n h w + ∑ k : Fin w.length, if s = w.get k then
        normalizedWordPairMean n h (s :: w.take k.val) (w.drop (k.val + 1)) else 0) / h := by
  have hhR : (h : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hh)
  have hlen (k : Fin w.length) :
      (s :: w.take k.val).length + (w.drop (k.val + 1)).length = w.length := by
    simp only [List.length_cons, List.length_take, List.length_drop]
    rw [Nat.min_eq_left (Nat.le_of_lt k.isLt)]
    omega
  simp_rw [normalizedWordMean_eq_raw, normalizedWordPairMean_eq_raw, hlen]
  rw [AHH.gaussian_wordTrace_integral_loop_re]
  simp only [List.length_cons]
  let a : ℝ := (∫ x : ((Fin n × Fin h) × Bool) → ℝ,
      Matrix.trace (AHH.gaussianWordMatrix x w)
      ∂gaussianProductLaw ((Fin n × Fin h) × Bool)).re
  let b (k : Fin w.length) : ℝ :=
    (∫ x : ((Fin n × Fin h) × Bool) → ℝ,
      Matrix.trace (AHH.gaussianWordMatrix x (s :: w.take k.val)) *
        Matrix.trace (AHH.gaussianWordMatrix x (w.drop (k.val + 1)))
      ∂gaussianProductLaw ((Fin n × Fin h) × Bool)).re
  change ((2 * (h : ℝ))⁻¹) ^ (w.length + 1) *
      (2 * a + ∑ k : Fin w.length, if s = w.get k then 2 * b k else 0) =
    (((2 * (h : ℝ))⁻¹) ^ w.length * a +
      ∑ k : Fin w.length, if s = w.get k then
        ((2 * (h : ℝ))⁻¹) ^ w.length * b k else 0) / h
  have hs (c : ℝ) :
      (∑ k : Fin w.length, if s = w.get k then c * b k else 0) =
        c * ∑ k : Fin w.length, if s = w.get k then b k else 0 := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [hs, hs, pow_succ]
  field_simp

theorem normalizedWordMean_single (n h : ℕ) (hh : 0 < h)
    (s : Fin n) (w : List (Fin n)) (hs : s ∉ w) :
    normalizedWordMean n h (s :: w) = normalizedWordMean n h w / h := by
  rw [normalizedWordMean_position_loop n h hh]
  have hz : (∑ k : Fin w.length, if s = w.get k then
      normalizedWordPairMean n h (s :: w.take k.val) (w.drop (k.val + 1)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    apply if_neg
    intro he
    exact hs (he ▸ List.get_mem w k)
  rw [hz, add_zero]

end AHHGaussian
