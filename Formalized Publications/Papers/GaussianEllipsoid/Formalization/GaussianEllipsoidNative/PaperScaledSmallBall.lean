import AllRowsScaledSmallBall
import PaperThetaCap

noncomputable section
open MeasureTheory Finset GaussianMixedNormHelpers
namespace GaussianEllipsoid.SmallBall

theorem scaled_coordinate_cap_of_paper_theta {r n : ℕ} (hr : 0 < r)
    {σ θ : ℝ} (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (u : Fin n → ℝ) (hu : Real.sqrt (r:ℝ)*‖u‖/σ ≤ θ) :
    ∀ i, (u i)^2 ≤ σ^2*(2*(r:ℝ))⁻¹ := by
  have hn : Real.sqrt (r:ℝ)*‖σ⁻¹ • u‖ ≤ θ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ),
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hu
  have h := squared_coordinate_cap_of_paper_theta hr hθ0 hθ (σ⁻¹ • u) hn
  intro i
  have hh := mul_le_mul_of_nonneg_left (h i) (sq_nonneg σ)
  simpa only [Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 2 hσ.ne'), one_mul] using hh

/-- Paper Corollary5.5 with the exact theta-normalized coefficient assumption. -/
theorem paper_scaled_frobenius_small_ball (r n : ℕ) (hr : 0 < r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (u : Fin n → ℝ) {σ d t : ℝ} (hσ : 0 < σ) (hd : 0 < d) (ht : 0 < t)
    (husum : ∑ i, (u i)^2 = σ^2) (hu : Real.sqrt (r:ℝ)*‖u‖/σ ≤ θ)
    (C : FrobeniusMatrix r r) :
    (bilinearGaussianSampleLaw r n).real
      {p | ‖bilinearScaled d r n u p-C‖ ≤ t*σ*(r:ℝ)/Real.sqrt d} ≤ (4*t)^(r*r) :=
  gaussian_bilinear_scaled_frobenius_smallball_all_rows r n hr u hσ hd ht husum
    (scaled_coordinate_cap_of_paper_theta hr hσ hθ0 hθ u hu) C

/-- The same scaled estimate after conditioning on an independent external
sigma-field represented by the first factor of a product sample space. -/
theorem paper_conditional_scaled_frobenius_small_ball
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (r n : ℕ) (hr : 0 < r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (u : Ω → Fin n → ℝ) (σ : Ω → ℝ) (C : Ω → FrobeniusMatrix r r)
    {d t : ℝ} (hd : 0 < d) (ht : 0 < t)
    (hu : ∀ᵐ ω ∂μ, 0 < σ ω ∧ (∑ i, (u ω i)^2 = (σ ω)^2) ∧
      Real.sqrt (r:ℝ)*‖u ω‖/σ ω ≤ θ) :
    ∀ᵐ ω ∂μ, (bilinearGaussianSampleLaw r n).real
      {p | ‖bilinearScaled d r n (u ω) p-C ω‖ ≤ t*σ ω*(r:ℝ)/Real.sqrt d} ≤ (4*t)^(r*r) := by
  filter_upwards [hu] with ω hω
  exact paper_scaled_frobenius_small_ball r n hr hθ0 hθ (u ω) hω.1 hd ht hω.2.1 hω.2.2 (C ω)
end GaussianEllipsoid.SmallBall
#print axioms GaussianEllipsoid.SmallBall.paper_scaled_frobenius_small_ball
#print axioms GaussianEllipsoid.SmallBall.paper_conditional_scaled_frobenius_small_ball
