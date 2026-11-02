import ShiftedExponentialMoments
import GaussianMomentTailArithmetic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic

noncomputable section
open MeasureTheory Real Set GaussianTensorMoments
open scoped ENNReal BigOperators
namespace BMUniformMoment

noncomputable def bernsteinGauge (D z : ℝ) : ℝ := min (z^2) (D*|z|)/16

lemma bernsteinGauge_nonneg {D : ℝ} (hD : 0 ≤ D) (z : ℝ) :
    0 ≤ bernsteinGauge D z := by unfold bernsteinGauge; positivity

lemma quadratic_le_gauge_powers {D : ℝ} (hD : 0 < D) (z : ℝ) (k : ℕ) :
    |z|^(2*k) ≤ (16*bernsteinGauge D z)^k +
      (256/D^2)^k * (bernsteinGauge D z)^(2*k) := by
  have hG := bernsteinGauge_nonneg hD.le z
  by_cases h : z^2 ≤ D*|z|
  · have heq : 16*bernsteinGauge D z = z^2 := by
      simp [bernsteinGauge, min_eq_left h]; ring
    rw [heq, pow_mul, sq_abs]
    exact le_add_of_nonneg_right (by positivity)
  · have heq : (256/D^2)^k * (bernsteinGauge D z)^(2*k) = |z|^(2*k) := by
      have hh : (256/D^2)*(bernsteinGauge D z)^2 = |z|^2 := by
        simp only [bernsteinGauge, min_eq_right (le_of_not_ge h)]
        field_simp <;> ring_nf <;> simp only [sq_abs]
      rw [pow_mul, ← mul_pow, hh, ← pow_mul]
    rw [heq]
    exact le_add_of_nonneg_left (pow_nonneg (by positivity) _)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Bernstein's two scales yield exact integer moments of a single nonnegative
comparison variable. -/
theorem gauge_shifted_moment_le (Z : Ω → ℝ) (hZ : Measurable Z) (D : ℝ) (hD : 0 < D)
    (htail : ∀ t > 0, μ {x | t < bernsteinGauge D (Z x)} ≤ ENNReal.ofReal (2*exp (-t)))
    (k : ℕ) :
    Integrable (fun x => (bernsteinGauge D (Z x))^k) μ ∧
    (∫ x, (bernsteinGauge D (Z x))^k ∂μ) ≤ (log 2 + k)^k := by
  have hm : Measurable (fun x => bernsteinGauge D (Z x)) := by
    unfold bernsteinGauge; fun_prop
  have hn : 0 ≤ᵐ[μ] fun x => bernsteinGauge D (Z x) :=
    ae_of_all _ (fun x => bernsteinGauge_nonneg hD.le (Z x))
  have hl : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
  have ht : ∀ t > 0, μ {x | log 2 + t < bernsteinGauge D (Z x)} ≤ ENNReal.ofReal (exp (-t)) := by
    intro t ht
    have hh := htail (log 2+t) (by linarith)
    have he : 2*exp (-(log 2+t)) = exp (-t) := by
      rw [neg_add, exp_add, exp_neg, exp_log (by norm_num : (0:ℝ)<2)]
      ring
    rwa [he] at hh
  exact ⟨shifted_exp_tail_integrable_pow hn hm.aemeasurable hl ht k,
    shifted_exp_tail_integral_pow_le hn hm.aemeasurable hl ht k⟩

/-- The two-tailed Gaussian-quadratic scale gives a concrete even-moment bound.
No Latała inequality or higher-moment assumption appears in this conversion. -/
theorem bernstein_even_moment (Z : Ω → ℝ) (hZ : Measurable Z) (D : ℝ) (hD : 0 < D)
    (htail : ∀ t > 0, μ {x | t < bernsteinGauge D (Z x)} ≤ ENNReal.ofReal (2*exp (-t)))
    (k : ℕ) (hk : 0 < k) :
    Integrable (fun x => |Z x|^(2*k)) μ ∧
    (∫ x, |Z x|^(2*k) ∂μ) ≤ (32*k+2304*k^2/D^2)^k := by
  have h1 := gauge_shifted_moment_le Z hZ D hD htail k
  have h2 := gauge_shifted_moment_le Z hZ D hD htail (2*k)
  have hI : Integrable (fun x => (16*bernsteinGauge D (Z x))^k +
      (256/D^2)^k * (bernsteinGauge D (Z x))^(2*k)) μ := by
    simp_rw [mul_pow]
    exact (h1.1.const_mul _).add (h2.1.const_mul _)
  have hi : Integrable (fun x => |Z x|^(2*k)) μ :=
    hI.mono' ((hZ.abs.pow_const (2*k)).aestronglyMeasurable) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact quadratic_le_gauge_powers hD (Z x) k))
  refine ⟨hi, ?_⟩
  calc
    (∫ x, |Z x|^(2*k) ∂μ)
      ≤ ∫ x, (16*bernsteinGauge D (Z x))^k +
          (256/D^2)^k * (bernsteinGauge D (Z x))^(2*k) ∂μ :=
        integral_mono hi hI (fun x => quadratic_le_gauge_powers hD (Z x) k)
    _ = 16^k * (∫ x, (bernsteinGauge D (Z x))^k ∂μ) +
          (256/D^2)^k * (∫ x, (bernsteinGauge D (Z x))^(2*k) ∂μ) := by
        simp_rw [mul_pow]
        rw [integral_add (h1.1.const_mul _) (h2.1.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 16^k*(log 2+k)^k + (256/D^2)^k*(log 2+↑(2*k))^(2*k) := by
      exact add_le_add (mul_le_mul_of_nonneg_left h1.2 (by positivity))
        (mul_le_mul_of_nonneg_left h2.2 (by positivity))
    _ ≤ (32*k)^k + (2304*k^2/D^2)^k := by
      have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
      have hl0 : 0 ≤ log 2 := Real.log_nonneg (by norm_num)
      have hla : log 2+(k:ℝ) ≤ 2*k := by linarith [log_two_le_one]
      have hlb : log 2+(↑(2*k):ℝ) ≤ 3*k := by push_cast; linarith [log_two_le_one]
      apply add_le_add
      · calc
          _ ≤ (16:ℝ)^k*(2*(k:ℝ))^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hla _) (by positivity)
          _ = _ := by rw [← mul_pow]; congr 1; ring
      · calc
          _ ≤ (256/D^2)^k*(3*(k:ℝ))^(2*k) := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hlb _) (by positivity)
          _ = _ := by rw [pow_mul, ← mul_pow]; congr 1; ring
    _ ≤ (32*k+2304*k^2/D^2)^k := pow_add_pow_le (by positivity) (by positivity) (by omega)

#print axioms quadratic_le_gauge_powers
#print axioms gauge_shifted_moment_le
#print axioms bernstein_even_moment
end BMUniformMoment
