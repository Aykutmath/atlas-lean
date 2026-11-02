import GaussianUniformFractionalMoment
import ClippedL1Bridge

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Real Set GaussianMixedNormHelpers BMQuadraticSpectral
open scoped ENNReal BigOperators InnerProductSpace
namespace BMUniformMoment

theorem normalizedQuadratic_smul_eq {d : ℕ} (c : ℝ)
    (T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d)
    (x : BMQuadraticSpectral.Euclid d) :
    normalizedQuadratic (c • T) x = c * normalizedQuadratic T x := by
  simp [normalizedQuadratic, inner_smul_right, mul_sub, mul_div_assoc]
  ring

theorem empirical_fractional_sum_smul {d n : ℕ} (c : ℝ)
    (T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d)
    (x : Fin n → BMQuadraticSpectral.Euclid d) :
    (∑ i, |normalizedQuadratic (c • T) (x i)|^((6:ℝ)/5)) =
      |c|^((6:ℝ)/5) * ∑ i, |normalizedQuadratic T (x i)|^((6:ℝ)/5) := by
  simp_rw [normalizedQuadratic_smul_eq, abs_mul,
    Real.mul_rpow (abs_nonneg c) (abs_nonneg _)]
  exact (Finset.mul_sum _ _ _).symm

/-- The unit-operator-ball bound extends to any fixed spectral radius. -/
theorem empirical_fractional_sum_le_radius {d n : ℕ}
    (x : Fin n → BMQuadraticSpectral.Euclid d) (K L : ℝ) (hL : 0 < L)
    (hunit : ∀ T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d,
      T.toLinearMap.IsSymmetric → ‖T‖ ≤ 1 →
      (∑ i, |normalizedQuadratic T (x i)|^((6:ℝ)/5)) ≤ K*n)
    (T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d)
    (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ L) :
    (∑ i, |normalizedQuadratic T (x i)|^((6:ℝ)/5)) ≤ (K*L^((6:ℝ)/5))*n := by
  let S := L⁻¹ • T
  have hs : S.toLinearMap.IsSymmetric := hT.smul (by simp)
  have hn : ‖S‖ ≤ 1 := by
    dsimp [S]
    calc
      _ ≤ ‖L⁻¹‖*‖T‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = L⁻¹*‖T‖ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      _ ≤ L⁻¹*L := mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr hL.le)
      _ = 1 := inv_mul_cancel₀ hL.ne'
  have hb := hunit S hs hn
  have he : L • S = T := by simp [S, smul_smul, hL.ne']
  have hh := empirical_fractional_sum_smul L S x
  rw [he, abs_of_pos hL] at hh
  rw [hh]
  calc
    _ ≤ L^((6:ℝ)/5)*(K*n) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hL.le _)
    _ = (K*L^((6:ℝ)/5))*n := by ring

/-- Actual uniform shifted-residual 6/5 moments on every fixed operator-norm
ball. This is the direct input to bounded-smooth-loss to L1 passage. -/
theorem exists_uniform_fractional_residual_constant (a A L : ℝ)
    (ha : 0 < a) (hA : 1 ≤ A) (hL : 0 < L) :
    ∃ K : ℝ, 0 < K ∧ ∀ d n : ℕ, 0 < d → 0 < n →
      a*(d:ℝ)^2 ≤ n → (n:ℝ) ≤ A*(d:ℝ)^2 →
      ∃ E : Set (Fin n → BMQuadraticSpectral.Euclid d), MeasurableSet E ∧
        (∀ x ∈ E, ∀ T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d,
          T.toLinearMap.IsSymmetric → ‖T‖ ≤ L →
          (∑ i, |normalizedQuadratic T (x i)-1|^((6:ℝ)/5)) ≤ K*n) ∧
        (gaussianSampleLaw d n).real Eᶜ ≤ exp (-(n:ℝ)) := by
  obtain ⟨K, hK, hall⟩ := exists_uniform_fractional_constant a A ha hA
  refine ⟨4*(K*L^((6:ℝ)/5)+1), by positivity, ?_⟩
  intro d n hd hn hlow hhigh
  obtain ⟨E, hE, hgood, hbad⟩ := hall d n hd hn hlow hhigh
  refine ⟨E, hE, ?_, hbad⟩
  intro x hx T hT hN
  exact BMClippedL1Bridge.sum_abs_sub_one_six_fifths_le
    (fun i => normalizedQuadratic T (x i))
    (empirical_fractional_sum_le_radius x K L hL (hgood x hx) T hT hN)

#print axioms normalizedQuadratic_smul_eq
#print axioms empirical_fractional_sum_le_radius
#print axioms exists_uniform_fractional_residual_constant
end BMUniformMoment
