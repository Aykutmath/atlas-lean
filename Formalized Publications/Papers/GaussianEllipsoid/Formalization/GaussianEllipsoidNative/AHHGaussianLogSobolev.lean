import AHHGaussianEntropyDerivative
import AHHGaussianFisherContraction

/-! Sharp Gaussian log-Sobolev inequality for uniformly positive bounded C¹
tests, derived by Gaussian rotation, integration by parts and weighted Jensen.
This module does not assert a nonsmooth or sphere log-Sobolev inequality. -/
noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set Filter
open GaussianTensorMoments BMSmoothQuadraticComposition GaussianCovarianceRotation
open AHHGaussianSemigroup AHHGaussianLogTest AHHGaussianEntropyDerivative
open AHHGaussianFisherContraction
open scoped BigOperators BoundedContinuousFunction Topology

namespace AHHGaussianLogSobolev
variable {d : ℕ}

/-- The sharp Fisher-information form of Gaussian log-Sobolev for the actual
finite product standard Gaussian law. All analytic inputs are proved. -/
theorem gaussian_logSobolev (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hf : ∀ x, c ≤ F.value x) :
    (∫ x, F.value x * Real.log (F.value x) ∂γ d) -
        (∫ x, F.value x ∂γ d) * Real.log (∫ x, F.value x ∂γ d) ≤
      (1/2 : ℝ) * ∫ x, (∑ i, (F.gradient i x)^2) / F.value x ∂γ d := by
  let H := fun t => ∫ x, average F.value t x * Real.log (average F.value t x) ∂γ d
  let I := fun t => ∫ x, (∑ i, (average (F.gradient i) t x)^2) / average F.value t x ∂γ d
  let E := ∫ x, (∑ i, (F.gradient i x)^2) / F.value x ∂γ d
  have hd (t : ℝ) : HasDerivAt H (-Real.sin t * Real.cos t * I t) t := by
    have h := hasDerivAt_entropy_logOneTest F hc hf t
    rw [entropy_velocity_eq F hc hf t] at h
    exact h
  have hbound (t : ℝ) : I t ≤ E := average_fisher_integral_le F hc hf t
  have hjd (t : ℝ) : HasDerivAt (fun t => H t - (Real.cos t)^2 * (E/2))
      (Real.sin t * Real.cos t * (E-I t)) t := by
    convert! (hd t).sub (((Real.hasDerivAt_cos t).pow 2).mul_const (E/2)) using 1 <;> ring
  have hmono : MonotoneOn (fun t => H t - (Real.cos t)^2 * (E/2)) (Icc 0 (Real.pi/2)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    · intro t ht
      exact (hjd t).continuousAt.continuousWithinAt
    · intro t ht
      exact (hjd t).hasDerivWithinAt
    · intro t ht
      have hti : t ∈ Icc 0 (Real.pi/2) := interior_subset ht
      have hs : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi hti.1
        (by linarith [hti.2, Real.pi_pos])
      have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hti.1, Real.pi_pos], hti.2⟩
      exact mul_nonneg (mul_nonneg hs hcos) (sub_nonneg.mpr (hbound t))
  have h := hmono (show (0 : ℝ) ∈ Icc 0 (Real.pi/2) from ⟨le_rfl, by positivity⟩)
    (show Real.pi/2 ∈ Icc 0 (Real.pi/2) from ⟨by positivity, le_rfl⟩) (by positivity)
  have hzero : H 0 = ∫ x, F.value x * Real.log (F.value x) ∂γ d := by
    simp only [H, AHHGaussianSemigroup.average_zero]
  have hlast : H (Real.pi/2) =
      (∫ x, F.value x ∂γ d) * Real.log (∫ x, F.value x ∂γ d) := by
    simp only [H, average_pi_div_two, integral_const, probReal_univ, one_smul]
  change H 0 - (Real.cos 0)^2 * (E/2) ≤ H (Real.pi/2) - (Real.cos (Real.pi/2))^2 * (E/2) at h
  rw [hzero, hlast, Real.cos_zero, Real.cos_pi_div_two] at h
  dsimp only [E] at h
  linarith

#print axioms gaussian_logSobolev
end AHHGaussianLogSobolev
