import GaussianLipschitzIntegrability

set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers Filter
open scoped BigOperators InnerProductSpace
namespace GaussianVariance
variable {ι : Type*} [Fintype ι]

theorem finite_rotation_bound {f : E ι → ℝ} (hf : LipschitzWith 1 f) (t : ℝ) (n : ℕ) :
    (∫ z, (f (first (n*t) z)-f z.1)^2 ∂γ₂ ι) ≤
      (n:ℝ)^2 * ∫ z, (f (first t z)-f z.1)^2 ∂γ₂ ι := by
  have hp (z : E ι × E ι) := telescoping_square_bound (fun k => f (first (k*t) z)) n
  simp only [Nat.cast_zero, zero_mul, first_zero, Nat.cast_add, Nat.cast_one] at hp
  have h := integral_mono (pair_diff_sq_integrable hf (n*t))
    ((integrable_finset_sum (Finset.range n) (fun i _ =>
      pair_increment_sq_integrable hf ((i+1)*t) (i*t))).const_mul (n:ℝ)) hp
  rw [integral_const_mul, integral_finset_sum (Finset.range n) (fun (i : ℕ) _ =>
    pair_increment_sq_integrable hf ((i+1)*t) (i*t))] at h
  have hs (i : ℕ) :
      (∫ z, (f (first ((i+1)*t) z)-f (first (i*t) z))^2 ∂γ₂ ι) =
        ∫ z, (f (first t z)-f z.1)^2 ∂γ₂ ι := by
    rw [show ((i:ℝ)+1)*t = t+(i:ℝ)*t by ring]
    exact first_increment_stationary f t (i*t)
  simp_rw [hs] at h
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← pow_two] using h

theorem finite_slope_bound {f : E ι → ℝ} (hf : LipschitzWith 1 f)
    (a : ℝ) (ha : a ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    (∫ z, (f (first a z)-f z.1)^2 ∂γ₂ ι) ≤
      a^2 * ∫ z, ((f (first (a/n) z)-f z.1)/(a/n))^2 ∂γ₂ ι := by
  have hn' : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := finite_rotation_bound hf (a/n) n
  rw [show (n:ℝ)*(a/n)=a by field_simp] at h
  rw [show (fun z : E ι × E ι => ((f (first (a/n) z)-f z.1)/(a/n))^2) =
    (fun z => (f (first (a/n) z)-f z.1)^2 / (a/n)^2) by funext z; ring,
    integral_div]
  convert h using 1 <;> field_simp <;> ring

theorem pair_difference_eq_twice_variance {f : E ι → ℝ} (hf : LipschitzWith 1 f) :
    (∫ z : E ι × E ι, (f z.2-f z.1)^2 ∂γ₂ ι) = 2 * variance f (γ ι) := by
  have h1 := pair_fst_sq_integrable hf
  have h2 : Integrable (fun z : E ι × E ι => (f z.2)^2) (γ₂ ι) := by
    simpa only [first_pi_div_two] using pair_first_sq_integrable hf (Real.pi/2)
  have hm := (lipschitz_integrable hf).mul_prod (lipschitz_integrable hf)
  have hrepr (z : E ι × E ι) : (f z.2-f z.1)^2 =
      (f z.2)^2+(f z.1)^2-2*(f z.1*f z.2) := by ring
  simp_rw [hrepr]
  have ha : Integrable (fun z : E ι × E ι => (f z.2)^2+(f z.1)^2) (γ₂ ι) := h2.add h1
  have hb : Integrable (fun z : E ι × E ι => 2*(f z.1*f z.2)) (γ₂ ι) := hm.const_mul 2
  rw [integral_sub ha hb, integral_add h2 h1,
    integral_const_mul, integral_prod_mul]
  have he1 : (∫ z : E ι × E ι, (f z.1)^2 ∂γ₂ ι) = ∫ x, (f x)^2 ∂γ ι := by
    simpa only [first_zero] using first_preserves_integral (fun x => (f x)^2) 0
  have he2 : (∫ z : E ι × E ι, (f z.2)^2 ∂γ₂ ι) = ∫ x, (f x)^2 ∂γ ι := by
    simpa only [first_pi_div_two] using first_preserves_integral (fun x => (f x)^2) (Real.pi/2)
  rw [he1, he2, variance_eq_sub ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).mpr
    (lipschitz_sq_integrable hf))]
  simp only [Pi.pow_apply]
  ring

end GaussianVariance
