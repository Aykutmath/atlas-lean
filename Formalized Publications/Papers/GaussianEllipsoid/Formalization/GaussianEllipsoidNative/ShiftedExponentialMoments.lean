import ExponentialTailMoments
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open MeasureTheory Real Set Filter
open scoped ENNReal MeasureTheory BigOperators

namespace GaussianTensorMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Exponential tail control supplies the integrability needed for moment algebra. -/
theorem exp_tail_integrable_pow_succ
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : Integrable (fun ω => X ω ^ (m+1)) μ := by
  refine ⟨(hXm.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (hXnn.mono (fun ω h => pow_nonneg h _))]
  exact lt_of_le_of_lt (exp_tail_lintegral_pow_le_factorial hXnn hXm htail m)
    ENNReal.ofReal_lt_top

/-- Real-integral version of the exact factorial bound. -/
theorem exp_tail_integral_pow_succ_le_factorial
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : (∫ ω, X ω ^ (m+1) ∂μ) ≤ (m+1).factorial := by
  have hb := exp_tail_lintegral_pow_le_factorial hXnn hXm htail m
  have hi := exp_tail_integrable_pow_succ hXnn hXm htail m
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (hXnn.mono (fun ω h => pow_nonneg h _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

variable [IsProbabilityMeasure μ]

theorem exp_tail_integrable_pow
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : Integrable (fun ω => X ω ^ m) μ := by
  cases m with
  | zero => simp
  | succ m => exact exp_tail_integrable_pow_succ hXnn hXm htail m

theorem exp_tail_integral_pow_le_factorial
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : (∫ ω, X ω ^ m ∂μ) ≤ m.factorial := by
  cases m with
  | zero => simp
  | succ m => exact exp_tail_integral_pow_succ_le_factorial hXnn hXm htail m

/-- An exact binomial-moment bound replaces the informal appeal to L^m
Minkowski: moments of D+X are bounded by (D+m)^m. -/
theorem exp_tail_integral_add_pow_le
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    {D : ℝ} (hD : 0 ≤ D) (m : ℕ) :
    (∫ ω, (D + X ω)^m ∂μ) ≤ (D + m)^m := by
  have hint (i : ℕ) : Integrable
      (fun ω => D^i * X ω^(m-i) * (m.choose i : ℝ)) μ :=
    ((exp_tail_integrable_pow hXnn hXm htail (m-i)).const_mul _).mul_const _
  simp_rw [add_pow]
  rw [integral_finset_sum _ (fun i _ => hint i)]
  apply Finset.sum_le_sum
  intro i hi
  rw [integral_mul_const, integral_const_mul]
  have hmom : (∫ ω, X ω^(m-i) ∂μ) ≤ (m : ℝ)^(m-i) := by
    calc
      _ ≤ ((m-i).factorial : ℝ) := exp_tail_integral_pow_le_factorial hXnn hXm htail _
      _ ≤ (m : ℝ)^(m-i) := by
        exact_mod_cast ((Nat.factorial_le_pow (m-i)).trans
          (Nat.pow_le_pow_left (Nat.sub_le m i) (m-i)))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmom (pow_nonneg hD _))
    (Nat.cast_nonneg _)

/-- Polynomial integrability of the shifted comparison variable. -/
theorem exp_tail_integrable_add_pow
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (D : ℝ) (m : ℕ) : Integrable (fun ω => (D + X ω)^m) μ := by
  simp_rw [add_pow]
  apply integrable_finset_sum
  intro i hi
  exact ((exp_tail_integrable_pow hXnn hXm htail (m-i)).const_mul _).mul_const _

/-- Complete shifted-tail to moment inequality. This applies directly to
||G||²/8 after the Gaussian sphere-net union bound. -/
theorem shifted_exp_tail_lintegral_pow_le
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    {D : ℝ} (hD : 0 ≤ D)
    (htail : ∀ t > 0, μ {ω | D + t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : (∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂μ) ≤
      ENNReal.ofReal ((D + m)^m) := by
  let Z : Ω → ℝ := fun ω => max (X ω-D) 0
  have hZn : 0 ≤ᵐ[μ] Z := ae_of_all _ (fun ω => le_max_right _ _)
  have hZm : AEMeasurable Z μ := (hXm.sub_const D).max aemeasurable_const
  have hZtail : ∀ t > 0, μ {ω | t < Z ω} ≤ ENNReal.ofReal (exp (-t)) := by
    intro t ht
    have heq : {ω | t < Z ω} = {ω | D+t < X ω} := by
      ext ω
      dsimp [Z]
      rw [lt_max_iff]
      constructor
      · intro h
        rcases h with h | h <;> linarith
      · intro h
        left
        linarith
    rw [heq]
    exact htail t ht
  have hIZ := exp_tail_integrable_add_pow hZn hZm hZtail D m
  have hnonneg : 0 ≤ᵐ[μ] fun ω => (D+Z ω)^m :=
    hZn.mono (fun ω h => pow_nonneg (add_nonneg hD h) _)
  calc
    (∫⁻ ω, ENNReal.ofReal (X ω ^ m) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal ((D+Z ω)^m) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hXnn] with ω hω
        apply ENNReal.ofReal_le_ofReal
        apply pow_le_pow_left₀ hω
        have hh : X ω-D ≤ Z ω := le_max_left _ _
        linarith
    _ = ENNReal.ofReal (∫ ω, (D+Z ω)^m ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hIZ hnonneg).symm
    _ ≤ ENNReal.ofReal ((D+m)^m) := ENNReal.ofReal_le_ofReal
      (exp_tail_integral_add_pow_le hZn hZm hZtail hD m)

/-- The shifted tail in particular proves integrability of every integer power. -/
theorem shifted_exp_tail_integrable_pow
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    {D : ℝ} (hD : 0 ≤ D)
    (htail : ∀ t > 0, μ {ω | D + t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : Integrable (fun ω => X ω^m) μ := by
  refine ⟨(hXm.pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (hXnn.mono (fun ω h => pow_nonneg h _))]
  exact lt_of_le_of_lt (shifted_exp_tail_lintegral_pow_le hXnn hXm hD htail m)
    ENNReal.ofReal_lt_top

/-- Real-valued form of the complete shifted-tail moment bound. -/
theorem shifted_exp_tail_integral_pow_le
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    {D : ℝ} (hD : 0 ≤ D)
    (htail : ∀ t > 0, μ {ω | D + t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) : (∫ ω, X ω^m ∂μ) ≤ (D+m)^m := by
  have hb := shifted_exp_tail_lintegral_pow_le hXnn hXm hD htail m
  have hi := shifted_exp_tail_integrable_pow hXnn hXm hD htail m
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (hXnn.mono (fun ω h => pow_nonneg h _))] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

#print axioms shifted_exp_tail_lintegral_pow_le
#print axioms shifted_exp_tail_integral_pow_le
#print axioms exp_tail_integrable_pow_succ
#print axioms exp_tail_integral_add_pow_le

end GaussianTensorMoments
