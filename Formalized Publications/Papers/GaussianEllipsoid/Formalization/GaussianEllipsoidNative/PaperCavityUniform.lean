import PaperCavityComparison
import PaperCavityEndpointBridge

/-! New reconstruction of the uniform-prior, literal endpoint bridge. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest
open BMProductLogPartition PaperGibbsThird PaperRowSecondStein
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.PaperCavityProduct
variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]

def paperFreeEnergy {n : ℕ} (β : ℝ) (ell : ℝ → ℝ) (X : Fin n → κ → ℝ) : ℝ :=
  -Real.log ((∑ a, Real.exp (-β * ∑ i, ell (X i a))) / (Fintype.card κ : ℝ)) / (β*n)

def uniformPrior3 (D : Data3 κ) : Data3 κ :=
  { D with
    weight := fun _ => (Fintype.card κ : ℝ)⁻¹
    weight_nonneg := fun _ => by positivity
    weight_sum := by
      have hc : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
      simp [hc] }

lemma uniformPrior3_freeEnergy (D : Data3 κ) {n : ℕ} (X : Fin n → κ → ℝ) :
    UCActualFreeEnergy.freeEnergy (uniformPrior3 D).toData X =
      paperFreeEnergy D.beta D.potential X := by
  simp only [UCActualFreeEnergy.freeEnergy, fullLogPartition, fullPartition, rowSum,
    uniformPrior3, paperFreeEnergy, ← Finset.mul_sum, div_eq_mul_inv, mul_comm]

def fullEntryCoefficients {d : ℕ} (A : Square d) (k : Fin (d*d)) : ℝ :=
  A (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

lemma fullEntryCoefficients_covariance {d : ℕ} (A B : Square d) (hB : B.transpose=B) :
    (∑ k, fullEntryCoefficients A k * fullEntryCoefficients B k) = Matrix.trace (A*B) := by
  rw [← (finProdFinEquiv : Fin d × Fin d ≃ Fin (d*d)).sum_comp]
  simp only [fullEntryCoefficients, Equiv.symm_apply_apply, Fintype.sum_prod_type]
  have hb (i j : Fin d) : B j i=B i j := congrFun (congrFun hB i) j
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hb]

lemma fullEntryCoefficients_eval {d : ℕ} (A : Square d) (z : Fin (d*d) → ℝ) :
    MvPolynomial.eval z (linearPolynomial (fullEntryCoefficients A)) = UCNormalizedRows.gaussianRow A z := by
  simp [linearPolynomial, fullEntryCoefficients, UCNormalizedRows.gaussianRow,
    MvPolynomial.smul_eq_C_mul]

theorem paper_uniform_cavity_comparison {d n : ℕ} (hn : 0 < n)
    (D : Data3 κ) (hβ : 0 < D.beta)
    (hunit : ∀ t, 0 ≤ D.potential t ∧ D.potential t ≤ 1)
    (R : κ → Square d) (hR : ∀ a, (R a).transpose=R a)
    {τ : ℝ} (hop : ∀ a, matrixOpNorm (R a) ≤ τ)
    (hfrob : ∀ a, frobeniusNorm (R a) ≤ 1) (c : Fin n → κ → ℝ) :
    |(∫ x : Fin n → (Fin d → ℝ), paperFreeEnergy D.beta D.potential
        (fun i => polynomialFamily (fun a => rowPoly (R a)) (x i)+c i)
          ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin d)))-
      ∫ z : Fin n → (Fin (d*d) → ℝ), paperFreeEnergy D.beta D.potential
        (fun i a => UCNormalizedRows.gaussianRow (R a) (z i)+c i a)
          ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin (d*d)))| ≤
      (3*Real.pi*Real.sqrt 2*Real.sqrt 3)*Real.exp (3*D.beta)*τ*
        (‖D.potentialThird‖+D.beta*‖D.potentialDeriv‖*‖D.potentialSecond‖+
          D.beta^2*‖D.potentialDeriv‖^3) := by
  have hτ : 0 ≤ τ := (matrixOpNorm_nonneg (R (Classical.arbitrary κ))).trans (hop _)
  have hop' (a : κ) : spectralNorm (R a) ≤ τ := by
    rw [UCNormalizedRows.spectralNorm_eq_matrixOpNorm]
    exact hop a
  have hfrob' (a : κ) : frobeniusSq (R a) ≤ 1 := by
    unfold frobeniusSq
    rw [← frobeniusNorm_sq]
    have h := pow_le_pow_left₀ (frobeniusNorm_nonneg _) (hfrob a) 2
    simpa using h
  have h := actual_cavity_freeEnergy_comparison hn (uniformPrior3 D) hβ hunit R hR
    (fun a => fullEntryCoefficients (R a))
    (fun a b => fullEntryCoefficients_covariance _ _ (hR b)) hτ hop' hfrob' c
  simp only [uniformPrior3_freeEnergy, polynomialFamily, ContinuousMap.coe_mk,
    fullEntryCoefficients_eval, Pi.add_apply, Pi.add_def] at h
  simpa only [uniformPrior3, polynomialFamily, ContinuousMap.coe_mk, Pi.add_def] using h

#print axioms paper_uniform_cavity_comparison
end GaussianEllipsoid.PaperCavityProduct
