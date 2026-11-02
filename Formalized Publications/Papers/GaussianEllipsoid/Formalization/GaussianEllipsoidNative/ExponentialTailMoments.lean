import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! Exact layer-cake integration of an exponential tail. This is the
probabilistic tail-to-moment step used after a finite Gaussian sphere net. -/

open MeasureTheory Real Set Filter
open scoped ENNReal MeasureTheory

namespace GaussianTensorMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- A nonnegative variable with tail at most exp(-t) has each positive integer
moment at most the corresponding factorial. Integrability is a conclusion of
this finite lintegral bound, not an additional moment assumption. -/
theorem exp_tail_lintegral_pow_le_factorial
    (hXnn : 0 ≤ᵐ[μ] X) (hXm : AEMeasurable X μ)
    (htail : ∀ t > 0, μ {ω | t < X ω} ≤ ENNReal.ofReal (exp (-t)))
    (m : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (X ω ^ (m + 1)) ∂μ) ≤
      ENNReal.ofReal ((m + 1).factorial : ℝ) := by
  have hmp : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t : ℝ => exp (-t) * t ^ (((m + 1 : ℕ) : ℝ) - 1) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (le_of_lt (exp_pos _)) (Real.rpow_nonneg (le_of_lt ht) _)
  have hint : IntegrableOn
      (fun t : ℝ => exp (-t) * t ^ (((m + 1 : ℕ) : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent hmp
  have hid : (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (exp (-t)) *
      ENNReal.ofReal (t ^ (((m + 1 : ℕ) : ℝ) - 1))) =
      ENNReal.ofReal (Gamma ((m + 1 : ℕ) : ℝ)) := by
    simp_rw [← ENNReal.ofReal_mul (le_of_lt (exp_pos _))]
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← Gamma_eq_integral hmp]
  have hlayer := lintegral_rpow_eq_lintegral_meas_lt_mul μ hXnn hXm hmp
  simp only [Real.rpow_natCast] at hlayer
  rw [hlayer]
  calc
    ENNReal.ofReal ((m + 1 : ℕ) : ℝ) *
        ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < X ω} *
          ENNReal.ofReal (t ^ (((m + 1 : ℕ) : ℝ) - 1))
      ≤ ENNReal.ofReal ((m + 1 : ℕ) : ℝ) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (exp (-t)) *
          ENNReal.ofReal (t ^ (((m + 1 : ℕ) : ℝ) - 1)) := by
        apply mul_le_mul_right
        apply lintegral_mono_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_le_mul_left (htail t ht) _
    _ = ENNReal.ofReal ((m + 1).factorial : ℝ) := by
      rw [hid, ← ENNReal.ofReal_mul (le_of_lt hmp)]
      congr 1
      rw [Nat.cast_add, Nat.cast_one, Gamma_nat_eq_factorial]
      simp [Nat.factorial_succ, Nat.cast_mul]

#print axioms exp_tail_lintegral_pow_le_factorial

end GaussianTensorMoments
