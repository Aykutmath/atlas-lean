import UCNormalizedRows
import UCShiftedProductReplacement
import BMActualFiniteReplacement
import GaussianEllipsoid.FreeEnergy

/-! Actual iid-product, finite-candidate free-energy universality at the
UC scale. The bound is uniform in row shifts and candidate count. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMProductLogPartition BMActualFiniteReplacement BMFiniteProductReplacement
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCActualFreeEnergy
variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}

/-- Uniform one-row error constant, independent of every Gibbs prior weight. -/
def comparisonConstant (D : Data2 κ) : ℝ :=
  (Real.pi/2)*Real.sqrt 2*(diagonalPriorConstant D + pairPriorConstant D)

@[simp] theorem comparisonConstant_otherRowsPrior (D : Data2 κ) {n : ℕ}
    (u : Fin n → κ → ℝ) : comparisonConstant (otherRowsPrior2 D u) = comparisonConstant D := rfl

def quadraticRow (A : κ → Square d) (x : Vector d) : κ → ℝ :=
  fun a => (quadratic (A a) x-Matrix.trace (A a))/Real.sqrt 2

def linearRow (A : κ → Square d) (z : Fin (d*d) → ℝ) : κ → ℝ :=
  fun a => UCNormalizedRows.gaussianRow (A a) z

theorem quadraticRow_continuous (A : κ → Square d) (hd : 0 < d) :
    Continuous (quadraticRow A) := by
  have he : quadraticRow A = polynomialFamily
      (fun a => normalizedQuadratic d (UCNormalizedRows.scaled (A a))) := by
    funext x a
    exact (UCNormalizedRows.eval_scaled hd (A a) x).symm
  rw [he]
  exact (polynomialFamily _).continuous

theorem linearRow_continuous (A : κ → Square d) (hd : 0 < d) :
    Continuous (linearRow A) := by
  have he : linearRow A = polynomialFamily
      (fun a => linearPolynomial (BMGaussianEquivalent.gaussianCoefficients (UCNormalizedRows.scaled (A a)))) := by
    funext z a
    exact (UCNormalizedRows.eval_gaussian_scaled hd (A a) z).symm
  rw [he]
  exact (polynomialFamily _).continuous

/-- Complete expectation comparison under the two actual independent row
laws, with all single-row comparisons already proved. -/
theorem actual_logPartition_comparison (D : Data2 κ) (A : κ → Square d)
    (hAsym : ∀ a, (A a).transpose = A a) (hd : 0 < d)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hOp : ∀ a, matrixOpNorm (A a) ≤ τ) (hF : ∀ a, frobeniusNorm (A a) ≤ 1)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) :
    |(∫ x : Sample d (n+1), fullLogPartition D.toData
        (fun i => quadraticRow A (x i)+c i) ∂gaussianSampleLaw d (n+1)) -
      ∫ z : Fin (n+1) → (Fin (d*d) → ℝ), fullLogPartition D.toData
        (fun i => linearRow A (z i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin (d*d)))| ≤
      (n+1 : ℕ)*(comparisonConstant D*τ) := by
  let μ := gaussianVectorLaw d
  let ν := gaussianProductLaw (Fin (d*d))
  have hrow (u : Fin n → κ → ℝ) (v : κ → ℝ) :
      |(∫ x : Vector d × (Fin (d*d) → ℝ),
          logPartition (otherRowsPrior2 D u).toData (quadraticRow A x.1+v) ∂μ.prod ν) -
        ∫ x : Vector d × (Fin (d*d) → ℝ),
          logPartition (otherRowsPrior2 D u).toData (linearRow A x.2+v) ∂μ.prod ν| ≤
        comparisonConstant D*τ := by
    rw [integral_fun_fst (fun x => logPartition (otherRowsPrior2 D u).toData (quadraticRow A x+v)),
      integral_fun_snd (fun x => logPartition (otherRowsPrior2 D u).toData (linearRow A x+v))]
    simpa only [probReal_univ, one_smul, quadraticRow, linearRow, Pi.add_def,
      comparisonConstant, diagonalPriorConstant, pairPriorConstant,
      otherRowsPrior2, otherRowsPrior, μ, ν] using
      UCNormalizedRows.actual_diffuse_row_replacement (otherRowsPrior2 D u) v A hAsym hd τ hτ hOp hF
  have h := UCShiftedProductReplacement.full_logPartition_shifted_replacement (μ.prod ν) D
    (fun x => quadraticRow A x.1) (fun x => linearRow A x.2)
    ((quadraticRow_continuous A hd).comp continuous_fst)
    ((linearRow_continuous A hd).comp continuous_snd) n c (comparisonConstant D*τ) hrow
  have hq : AEStronglyMeasurable (fun x : Fin (n+1) → Vector d =>
      fullLogPartition D.toData (fun i => quadraticRow A (x i)+c i))
      (Measure.pi fun _ : Fin (n+1) => μ) := by
    apply Continuous.aestronglyMeasurable
    apply (fullLogPartition_continuous D.toData (n+1)).comp
    exact continuous_pi fun i => ((quadraticRow_continuous A hd).comp
      (continuous_apply i)).add continuous_const
  have hg : AEStronglyMeasurable (fun x : Fin (n+1) → (Fin (d*d) → ℝ) =>
      fullLogPartition D.toData (fun i => linearRow A (x i)+c i))
      (Measure.pi fun _ : Fin (n+1) => ν) := by
    apply Continuous.aestronglyMeasurable
    apply (fullLogPartition_continuous D.toData (n+1)).comp
    exact continuous_pi fun i => ((linearRow_continuous A hd).comp
      (continuous_apply i)).add continuous_const
  rw [integral_pi_fst μ ν (n+1) _ hq, integral_pi_snd μ ν (n+1) _ hg] at h
  exact h

/-- Normalized finite-prior free energy. -/
def freeEnergy (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) : ℝ :=
  -(fullLogPartition D y)/(D.beta*n)

/-- Dimension-free normalized expectation comparison, with all row,
probability, and covariance machinery instantiated to the actual laws. -/
theorem actual_freeEnergy_comparison (D : Data2 κ) (hβ : 0 < D.beta)
    (A : κ → Square d) (hAsym : ∀ a, (A a).transpose = A a) (hd : 0 < d)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hOp : ∀ a, matrixOpNorm (A a) ≤ τ) (hF : ∀ a, frobeniusNorm (A a) ≤ 1)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) :
    |(∫ x : Sample d (n+1), freeEnergy D.toData
        (fun i => quadraticRow A (x i)+c i) ∂gaussianSampleLaw d (n+1)) -
      ∫ z : Fin (n+1) → (Fin (d*d) → ℝ), freeEnergy D.toData
        (fun i => linearRow A (z i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin (d*d)))| ≤
      (comparisonConstant D/D.beta)*τ := by
  have h := normalized_expectation_comparison hβ
    (by positivity : (0:ℝ) < (n+1:ℕ))
    (actual_logPartition_comparison D A hAsym hd τ hτ hOp hF n c)
  simp only [freeEnergy, integral_div, integral_neg]
  apply h.trans_eq
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  have hb : D.beta ≠ 0 := ne_of_gt hβ
  field_simp

#print axioms actual_logPartition_comparison
#print axioms actual_freeEnergy_comparison
end GaussianEllipsoid.UCActualFreeEnergy
