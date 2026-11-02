import PaperCavityUniform
import PaperCavityEndpointBridge

noncomputable section
open MeasureTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth PaperGibbsThird PaperRowSecondStein
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.PaperCavityProduct
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

theorem eval_rowPoly_eq_quadratic {d : ℕ} (R : Square d) (w : Vector d) :
    MvPolynomial.eval w (rowPoly R)=(quadratic R w-Matrix.trace R)/Real.sqrt 2 := by
  rw [PaperCavityEndpointBridge.eval_rowPoly]
  have he : (∑ i,∑ j,R i j*(w i*w j))=quadratic R w := by
    rw [quadratic_eq_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]

/-- Paper-facing finite-L_j C3 cavity comparison. The source's exact rank-one
normalization, finite uniform prior, n-row shifts, Frobenius/operator bounds,
and free-energy normalization all appear literally. The Gaussian comparison
rows are the canonical full-entry Frobenius-isonormal realization. -/
theorem paper_cavity_comparison_finite_derivatives {d n : ℕ} (hn : 0 < n)
    (D : Data3 κ) (hβ : 0 < D.beta)
    (hunit : ∀ t,0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (R : κ → Square d) (hR : ∀ a,(R a).transpose=R a)
    {τ : ℝ} (hop : ∀ a,matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a,frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ) :
    |(∫ x : Fin n → Vector d, paperFreeEnergy D.beta D.potential
        (fun i a => (quadratic (R a) (x i)-Matrix.trace (R a))/Real.sqrt 2+c i a)
          ∂Measure.pi (fun _ : Fin n => gaussianVectorLaw d))-
      ∫ z : Fin n → (Fin (d*d) → ℝ), paperFreeEnergy D.beta D.potential
        (fun i a => UCNormalizedRows.gaussianRow (R a) (z i)+c i a)
          ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))| ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (‖D.potentialThird‖+D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^2*‖D.potentialDeriv‖^3) := by
  simpa only [polynomialFamily,ContinuousMap.coe_mk,eval_rowPoly_eq_quadratic,
    Pi.add_def,gaussianVectorLaw,gaussianProductLaw] using!
    paper_uniform_cavity_comparison hn D hβ hunit R hR hop hfrob c

#print axioms paper_cavity_comparison_finite_derivatives
end GaussianEllipsoid.PaperCavityProduct
