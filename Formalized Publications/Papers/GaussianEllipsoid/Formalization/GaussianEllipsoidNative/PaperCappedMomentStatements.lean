import PaperCappedMoment
import GaussianCappedRealMoment

noncomputable section
open MeasureTheory Finset GaussianTensorMoments
open GaussianEllipsoid.CappedSimplex GaussianEllipsoid.SmallBall
namespace GaussianMixedNormHelpers

theorem paper_coordinate_theta_cap {r N : ℕ} (hr : 0 < r) (θ : ℝ) (z : Fin N → ℝ)
    (hz : Real.sqrt (r:ℝ)*‖z‖ ≤ θ) : ∀ i, (z i)^2 ≤ θ^2/(r:ℝ) := by
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hr
  intro i
  have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  have hprod := (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)).trans hz
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ Real.sqrt (r:ℝ)*|z i|) hprod 2
  rw [mul_pow, Real.sq_sqrt hrR.le, sq_abs] at hsq
  apply (le_div_iff₀ hrR).mpr
  nlinarith

/-- Literal C_theta=(1−2theta²)^(-1/2) raised to r², for every r≥2. -/
theorem paper_capped_determinant_explicit_constant (r N : ℕ) (hr : 2 ≤ r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (z : Fin N → ℝ) (hzsum : ∑ i, (z i)^2 = 1)
    (hz : Real.sqrt (r:ℝ)*‖z‖ ≤ θ) :
    (∫⁻ g : Fin N → Fin r → ℝ,
      ((ENNReal.ofReal (weightedGram g (fun i => (z i)^2)).det)^((r:ℝ)/2))⁻¹
        ∂Measure.pi (fun _ : Fin N => gaussianProductLaw (Fin r))) ≤
      ENNReal.ofReal (((1-2*θ^2)^(-(1/2:ℝ)))^(r*r)) := by
  have hb : 0 < 1-2*θ^2 := by linarith [paper_theta_sq_lt_half hθ0 hθ]
  have heq : ((1-2*θ^2)^(-(1/2:ℝ)))^(r*r) =
      (1-2*θ^2)^(-((r:ℝ)*((r:ℝ)/2))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    push_cast
    ring
  rw [heq]
  exact paper_uniform_capped_determinant_moment r N hr hθ0 hθ (fun i => (z i)^2) hzsum
    (fun i => ⟨sq_nonneg _, paper_coordinate_theta_cap (by omega) θ z hz i⟩)

/-- Paper Proposition5.3's all-dimension existential constant, including r=1.
The proved endpoint-cap bound supplies a universal C, while the previous
statement preserves the paper's sharper displayed theta-dependent constant. -/
theorem paper_capped_determinant_exists_constant {θ : ℝ}
    (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ r N : ℕ, 0 < r → ∀ z : Fin N → ℝ,
      (∑ i, (z i)^2 = 1) → Real.sqrt (r:ℝ)*‖z‖ ≤ θ →
      (∫⁻ g : Fin N → Fin r → ℝ,
        ((ENNReal.ofReal (weightedGram g (fun i => (z i)^2)).det)^((r:ℝ)/2))⁻¹
          ∂Measure.pi (fun _ : Fin N => gaussianProductLaw (Fin r))) ≤
        ENNReal.ofReal (C^(r*r)) := by
  refine ⟨(2*Real.exp 1)^(1/2:ℝ), by positivity, ?_⟩
  intro r N hr z hzsum hz
  have h := gaussian_capped_real_moment r hr
    (w := fun i => (z i)^2) ⟨fun i => ⟨sq_nonneg _,
      squared_coordinate_cap_of_paper_theta hr hθ0 hθ z hz i⟩,hzsum⟩
  have heq : ((2*Real.exp 1)^(1/2:ℝ))^(r*r) =
      (2*Real.exp 1)^((r:ℝ)*((r:ℝ)/2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    ring
  rw [heq]
  exact h
end GaussianMixedNormHelpers
#print axioms GaussianMixedNormHelpers.paper_capped_determinant_explicit_constant
#print axioms GaussianMixedNormHelpers.paper_capped_determinant_exists_constant
