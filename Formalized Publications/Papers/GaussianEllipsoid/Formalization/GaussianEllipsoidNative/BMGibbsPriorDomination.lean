import BoundedGibbsTilt
import BMFiniteGibbsTest

open GaussianEllipsoidCandidate
open scoped BoundedContinuousFunction
namespace BMFiniteGibbsTest
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Gibbs weights retain their prior masses in the uniform bound. -/
theorem probability_le_prior (D : Data κ) (y : κ → ℝ) (a : κ) :
    probability D y a ≤ Real.exp (2*D.beta*‖D.potential‖)*D.weight a := by
  exact boundedGibbsWeight_le D.weight (fun a => D.potential (y a))
    D.weight_nonneg D.weight_sum D.beta_nonneg
    (fun a => by simpa only [Real.norm_eq_abs] using D.potential.norm_coe_le_norm (y a)) a

/-- Pairwise Gibbs weights are bounded by the product prior, with no
state-count factor. This is the off-diagonal Hessian input. -/
theorem probability_pair_le_prior (D : Data κ) (y : κ → ℝ) (a b : κ) :
    probability D y a * probability D y b ≤
      Real.exp (4*D.beta*‖D.potential‖) * (D.weight a * D.weight b) := by
  have h := mul_le_mul (probability_le_prior D y a) (probability_le_prior D y b)
    (probability_nonneg D y b)
    (mul_nonneg (Real.exp_nonneg _) (D.weight_nonneg a))
  have he : (Real.exp (2*D.beta*‖D.potential‖)*D.weight a)*
      (Real.exp (2*D.beta*‖D.potential‖)*D.weight b) =
      Real.exp (4*D.beta*‖D.potential‖)*(D.weight a*D.weight b) := by
    calc
      _ = (Real.exp (2*D.beta*‖D.potential‖)*Real.exp (2*D.beta*‖D.potential‖))*
          (D.weight a*D.weight b) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
  rwa [he] at h

theorem prior_pair_sum (D : Data κ) : (∑ a, ∑ b, D.weight a*D.weight b) = 1 := by
  simp only [← Finset.mul_sum, D.weight_sum, mul_one]

/-- Nonnegative pair remainder domination against a deterministic product
prior; it remains valid for every sample-dependent vector y. -/
theorem probability_pair_remainder_le (D : Data κ) (y : κ → ℝ) (R : κ → κ → ℝ)
    (hR : ∀ a b, 0 ≤ R a b) :
    (∑ a, ∑ b, probability D y a*probability D y b*R a b) ≤
      Real.exp (4*D.beta*‖D.potential‖)*(∑ a, ∑ b, D.weight a*D.weight b*R a b) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (probability_pair_le_prior D y a b) (hR a b)

/-- The first derivative has a prior-weighted uniform norm bound. -/
theorem gradient_norm_le_prior (D : Data κ) (a : κ) (y : κ → ℝ) :
    ‖gradient D a y‖ ≤
      D.beta*Real.exp (2*D.beta*‖D.potential‖)*D.weight a*‖D.potentialDeriv‖ := by
  calc
    _ = D.beta*probability D y a*‖D.potentialDeriv (y a)‖ := by
      simp only [gradient, norm_mul, norm_neg, Real.norm_eq_abs,
        abs_of_nonneg D.beta_nonneg, abs_of_nonneg (probability_nonneg D y a)]
    _ ≤ (D.beta*(Real.exp (2*D.beta*‖D.potential‖)*D.weight a))*‖D.potentialDeriv‖ :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (probability_le_prior D y a) D.beta_nonneg)
        (D.potentialDeriv.norm_coe_le_norm _) (norm_nonneg _)
        (mul_nonneg D.beta_nonneg (mul_nonneg (Real.exp_nonneg _) (D.weight_nonneg a)))
    _ = _ := by ring

theorem boundedGradient_norm_le_prior (D : Data κ) (a : κ) :
    ‖boundedGradient D a‖ ≤
      D.beta*Real.exp (2*D.beta*‖D.potential‖)*D.weight a*‖D.potentialDeriv‖ := by
  have hC : 0 ≤ D.beta*Real.exp (2*D.beta*‖D.potential‖)*D.weight a*‖D.potentialDeriv‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg D.beta_nonneg (Real.exp_nonneg _))
      (D.weight_nonneg a)) (norm_nonneg _)
  apply (BoundedContinuousFunction.norm_le hC).2
  exact gradient_norm_le_prior D a

#print axioms boundedGradient_norm_le_prior
#print axioms probability_le_prior
#print axioms probability_pair_le_prior
#print axioms prior_pair_sum
#print axioms probability_pair_remainder_le
#print axioms gradient_norm_le_prior
end BMFiniteGibbsTest
