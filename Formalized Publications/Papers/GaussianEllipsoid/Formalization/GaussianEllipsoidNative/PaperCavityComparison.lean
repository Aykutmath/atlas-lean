import PaperCavityProduct
import PaperC3GibbsReplacement

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMProductLogPartition PaperGibbsThird PaperRowSecondStein
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.PaperCavityProduct
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Complete C3 product comparison: every single-row estimate is proved from the actual Gaussian laws. -/
theorem actual_cavity_freeEnergy_comparison_succ {d m : ℕ}
    (D : Data3 κ) (hβ : 0 < D.beta)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose=R a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i)=Matrix.trace (R a*R b))
    {τ : ℝ} (hτ : 0 ≤ τ) (hop : ∀ a, spectralNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusSq (R a) ≤ 1)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) :
    |(∫ x : Fin (n+1) → (Fin d → ℝ), UCActualFreeEnergy.freeEnergy D.toData
        (fun i => polynomialFamily (fun a => rowPoly (R a)) (x i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d)))-
      ∫ z : Fin (n+1) → (Fin m → ℝ), UCActualFreeEnergy.freeEnergy D.toData
        (fun i => polynomialFamily (fun a => linearPolynomial (B a)) (z i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin m))| ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (‖D.potentialThird‖+D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^2*‖D.potentialDeriv‖^3) := by
  let ε := (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
    (D.beta*‖D.potentialThird‖+D.beta^2*‖D.potentialDeriv‖*‖D.potentialSecond‖+
      D.beta^3*‖D.potentialDeriv‖^3)
  have hrow (u : Fin n → κ → ℝ) (v : κ → ℝ) :
      |(∫ x, logPartition (otherRowsPrior3 D u).toData
          (polynomialFamily (fun a => rowPoly (R a)) x+v) ∂gaussianProductLaw (Fin d))-
        ∫ z, logPartition (otherRowsPrior3 D u).toData
          (polynomialFamily (fun a => linearPolynomial (B a)) z+v) ∂gaussianProductLaw (Fin m)| ≤ ε :=
    PaperC3GibbsReplacement.one_row_logPartition_shifted_replacement
      (otherRowsPrior3 D u) hunit R hR B hCov v hτ hop hfrob
  have h := full_freeEnergy_comparison_of_row_bound D hβ
    (fun a => rowPoly (R a)) (fun a => linearPolynomial (B a)) n c ε hrow
  apply h.trans_eq
  dsimp [ε]
  field_simp
  <;> ring

/-- All positive row counts, without an n+1 representation in the public statement. -/
theorem actual_cavity_freeEnergy_comparison {d m n : ℕ} (hn : 0 < n)
    (D : Data3 κ) (hβ : 0 < D.beta)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose=R a)
    (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i)=Matrix.trace (R a*R b))
    {τ : ℝ} (hτ : 0 ≤ τ) (hop : ∀ a, spectralNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusSq (R a) ≤ 1) (c : Fin n → κ → ℝ) :
    |(∫ x : Fin n → (Fin d → ℝ), UCActualFreeEnergy.freeEnergy D.toData
        (fun i => polynomialFamily (fun a => rowPoly (R a)) (x i)+c i)
          ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin d)))-
      ∫ z : Fin n → (Fin m → ℝ), UCActualFreeEnergy.freeEnergy D.toData
        (fun i => polynomialFamily (fun a => linearPolynomial (B a)) (z i)+c i)
          ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin m))| ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (‖D.potentialThird‖+D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^2*‖D.potentialDeriv‖^3) := by
  cases n with
  | zero => omega
  | succ k => exact actual_cavity_freeEnergy_comparison_succ D hβ hunit R hR B hCov hτ hop hfrob k c

#print axioms actual_cavity_freeEnergy_comparison
end GaussianEllipsoid.PaperCavityProduct
