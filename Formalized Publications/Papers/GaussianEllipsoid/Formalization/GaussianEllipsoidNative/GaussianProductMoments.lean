import GaussianPolynomialMoments
import GaussianProductLinearForms
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Exact actual product-Gaussian monomial moments, including arbitrary repeated
endpoint labels. This is the analytic side of Wick's pairing identity. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal BigOperators Nat

namespace GaussianTensorMoments

variable {ι : Type*} [Fintype ι]

/-- Fubini factorization under the concrete iid Gaussian product measure. -/
theorem gaussianProductLaw_integral_prod (f : ι → ℝ → ℝ) :
    (∫ x, ∏ i, f i (x i) ∂gaussianProductLaw ι) =
      ∏ i, ∫ x : ℝ, f i x ∂gaussianReal 0 1 := by
  exact integral_fintype_prod_eq_prod f (μ := fun _ => gaussianReal 0 1)

/-- Integrability of any coordinate monomial under that product measure. -/
theorem gaussianProductLaw_integrable_monomial (k : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ k i) (gaussianProductLaw ι) := by
  exact Integrable.fintype_prod_dep (μ := fun _ => gaussianReal 0 1)
    (fun i => standardGaussian_integrable_pow (k i))

/-- Exact monomial moment as a product of genuine scalar Gaussian moments. -/
theorem gaussianProductLaw_monomial_moment (k : ι → ℕ) :
    (∫ x, ∏ i, x i ^ k i ∂gaussianProductLaw ι) =
      ∏ i, ∫ x : ℝ, x ^ k i ∂gaussianReal 0 1 :=
  gaussianProductLaw_integral_prod _

/-- Scalar closed Gaussian moment, with the odd case explicit. -/
theorem standardGaussian_moment_parity (k : ℕ) :
    (∫ x : ℝ, x^k ∂gaussianReal 0 1) =
      if Even k then ((k-1)‼ : ℝ) else 0 := by
  split_ifs with hk
  · obtain ⟨j, hj⟩ := hk
    rw [show k=2*j by omega]
    exact standardGaussian_moment_even j
  · have ho : Odd k := Nat.not_even_iff_odd.mp hk
    obtain ⟨j, hj⟩ := ho
    rw [show k=2*j+1 by omega]
    exact standardGaussian_moment_odd j

/-- Closed form for every multivariate coordinate monomial. -/
theorem gaussianProductLaw_monomial_moment_closed (k : ι → ℕ) :
    (∫ x, ∏ i, x i ^ k i ∂gaussianProductLaw ι) =
      ∏ i, if Even (k i) then (((k i-1)‼) : ℝ) else 0 := by
  rw [gaussianProductLaw_monomial_moment]
  simp_rw [standardGaussian_moment_parity]

/-- Product regrouping by label multiplicity. Distinct endpoints may carry
the same label; this is precisely the repeated-coordinate case in Wick. -/
theorem prod_endpoints_eq_fiber_powers {E : Type*} [Fintype E]
    (label : E → ι) (x : ι → ℝ) :
    (∏ e, x (label e)) = ∏ i, x i ^ Nat.card {e // label e = i} := by
  classical
  simpa [Nat.card_eq_fintype_card] using (Fintype.prod_fiberwise' label x).symm

/-- The full actual endpoint monomial is integrable, including repeated labels. -/
theorem gaussianProductLaw_integrable_endpoints {E : Type*} [Fintype E]
    (label : E → ι) :
    Integrable (fun x : ι → ℝ => ∏ e, x (label e)) (gaussianProductLaw ι) := by
  simp_rw [prod_endpoints_eq_fiber_powers]
  exact gaussianProductLaw_integrable_monomial _

/-- Analytic Wick side in closed form, with no assumed Gaussian moment law. -/
theorem gaussianProductLaw_endpoint_moment {E : Type*} [Fintype E]
    (label : E → ι) :
    (∫ x, ∏ e, x (label e) ∂gaussianProductLaw ι) =
      ∏ i, if Even (Nat.card {e // label e = i}) then
        (((Nat.card {e // label e = i}-1)‼) : ℝ) else 0 := by
  simp_rw [prod_endpoints_eq_fiber_powers]
  exact gaussianProductLaw_monomial_moment_closed _

#print axioms gaussianProductLaw_integrable_monomial
#print axioms gaussianProductLaw_endpoint_moment

end GaussianTensorMoments
