import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! Deterministic two-sphere net estimate for the genuine Euclidean operator
norm of a continuous linear map. No entrywise matrix norm is used. -/

open scoped InnerProductSpace

namespace GaussianTensorMoments

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Dual characterization of a vector norm by real unit-vector pairings. -/
theorem norm_le_of_unit_inner_bound {y : E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ u : E, ‖u‖ = 1 → |⟪u,y⟫_ℝ| ≤ C) : ‖y‖ ≤ C := by
  by_cases hy : y = 0
  · simpa [hy] using hC
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hu : ‖‖y‖⁻¹ • y‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hny]
  have hh := h (‖y‖⁻¹ • y) hu
  have heq : ⟪‖y‖⁻¹ • y,y⟫_ℝ = ‖y‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
    field_simp
  simpa [heq, abs_of_nonneg (norm_nonneg y)] using hh

/-- Two radius-1/4 nets of the real unit spheres control a linear map by twice
its maximum absolute bilinear pairing on their Cartesian product. -/
theorem opNorm_le_two_of_sphere_nets
    (A : F →L[ℝ] E) (s : Finset E) (t : Finset F)
    (hsnorm : ∀ u ∈ s, ‖u‖ = 1) (htnorm : ∀ v ∈ t, ‖v‖ = 1)
    (hsnet : ∀ u : E, ‖u‖ = 1 → ∃ u₀ ∈ s, ‖u-u₀‖ ≤ 1/4)
    (htnet : ∀ v : F, ‖v‖ = 1 → ∃ v₀ ∈ t, ‖v-v₀‖ ≤ 1/4)
    {B : ℝ} (hB : 0 ≤ B)
    (hpair : ∀ u ∈ s, ∀ v ∈ t, |⟪u,A v⟫_ℝ| ≤ B) : ‖A‖ ≤ 2*B := by
  have hunit (u : E) (hu : ‖u‖ = 1) (v : F) (hv : ‖v‖ = 1) :
      |⟪u,A v⟫_ℝ| ≤ B + (1/2)*‖A‖ := by
    obtain ⟨u₀, hu₀, hdu⟩ := hsnet u hu
    obtain ⟨v₀, hv₀, hdv⟩ := htnet v hv
    have heq : ⟪u,A v⟫_ℝ =
        ⟪u-u₀,A v⟫_ℝ + ⟪u₀,A (v-v₀)⟫_ℝ + ⟪u₀,A v₀⟫_ℝ := by
      rw [map_sub, inner_sub_right, inner_sub_left]
      ring
    have hb₁ : |⟪u-u₀,A v⟫_ℝ| ≤ (1/4)*‖A‖ := by
      calc
        _ ≤ ‖u-u₀‖ * ‖A v‖ := abs_real_inner_le_norm _ _
        _ ≤ (1/4) * (‖A‖ * ‖v‖) := mul_le_mul hdu (A.le_opNorm v)
          (norm_nonneg _) (by norm_num)
        _ = _ := by rw [hv]; ring
    have hb₂ : |⟪u₀,A (v-v₀)⟫_ℝ| ≤ (1/4)*‖A‖ := by
      calc
        _ ≤ ‖u₀‖ * ‖A (v-v₀)‖ := abs_real_inner_le_norm _ _
        _ = ‖A (v-v₀)‖ := by rw [hsnorm u₀ hu₀, one_mul]
        _ ≤ ‖A‖ * ‖v-v₀‖ := A.le_opNorm _
        _ ≤ ‖A‖ * (1/4) := mul_le_mul_of_nonneg_left hdv (norm_nonneg _)
        _ = _ := by ring
    rw [heq]
    exact (abs_add_three _ _ _).trans (by linarith [hpair u₀ hu₀ v₀ hv₀])
  have hA : ‖A‖ ≤ B+(1/2)*‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro v hv
    apply norm_le_of_unit_inner_bound (by positivity)
    exact fun u hu => hunit u hu v hv
  linarith

#print axioms opNorm_le_two_of_sphere_nets

end GaussianTensorMoments
