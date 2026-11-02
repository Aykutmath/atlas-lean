import PaperGibbsThird
import UCShiftedProductReplacement
import BMActualFiniteReplacement
import UCActualFreeEnergy

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMProductLogPartition BMActualFiniteReplacement BMFiniteProductReplacement
open scoped BigOperators BoundedContinuousFunction
namespace GaussianEllipsoid.PaperCavityProduct
open PaperGibbsThird
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The actual conditional Gibbs prior from all other rows, retaining the same C3 loss. -/
def otherRowsPrior3 (D : Data3 κ) {n : ℕ} (u : Fin n → κ → ℝ) : Data3 κ :=
  { D with toData2 := otherRowsPrior2 D.toData2 u }

/-- Product-law telescope with arbitrary deterministic row/candidate shifts.
This is an internal conditional lemma; the actual C3 row theorem is instantiated separately. -/
theorem full_logPartition_comparison_of_row_bound {d m : ℕ}
    (D : Data3 κ) (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) (ε : ℝ)
    (hrow : ∀ u : Fin n → κ → ℝ, ∀ v : κ → ℝ,
      |(∫ x, logPartition (otherRowsPrior3 D u).toData (polynomialFamily q x+v)
          ∂gaussianProductLaw (Fin d))-
        ∫ z, logPartition (otherRowsPrior3 D u).toData (polynomialFamily g z+v)
          ∂gaussianProductLaw (Fin m)| ≤ ε) :
    |(∫ x : Fin (n+1) → (Fin d → ℝ), fullLogPartition D.toData
        (fun i => polynomialFamily q (x i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d)))-
      ∫ z : Fin (n+1) → (Fin m → ℝ), fullLogPartition D.toData
        (fun i => polynomialFamily g (z i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin m))| ≤ (n+1:ℕ)*ε := by
  let μ := gaussianProductLaw (Fin d)
  let ν := gaussianProductLaw (Fin m)
  have hrow' (u : Fin n → κ → ℝ) (v : κ → ℝ) :
      |(∫ x : (Fin d → ℝ) × (Fin m → ℝ),
          logPartition (otherRowsPrior2 D.toData2 u).toData (polynomialFamily q x.1+v) ∂μ.prod ν)-
        ∫ x : (Fin d → ℝ) × (Fin m → ℝ),
          logPartition (otherRowsPrior2 D.toData2 u).toData (polynomialFamily g x.2+v) ∂μ.prod ν| ≤ ε := by
    rw [integral_fun_fst (fun x => logPartition (otherRowsPrior2 D.toData2 u).toData
        (polynomialFamily q x+v)),
      integral_fun_snd (fun z => logPartition (otherRowsPrior2 D.toData2 u).toData
        (polynomialFamily g z+v))]
    simpa only [probReal_univ,one_smul,otherRowsPrior3,μ,ν] using hrow u v
  have h := UCShiftedProductReplacement.full_logPartition_shifted_replacement (μ.prod ν) D.toData2
    (fun x => polynomialFamily q x.1) (fun x => polynomialFamily g x.2)
    ((polynomialFamily q).continuous.comp continuous_fst)
    ((polynomialFamily g).continuous.comp continuous_snd) n c ε hrow'
  have hq : AEStronglyMeasurable (fun x : Fin (n+1) → (Fin d → ℝ) =>
      fullLogPartition D.toData (fun i => polynomialFamily q (x i)+c i))
      (Measure.pi fun _ : Fin (n+1) => μ) := by
    apply Continuous.aestronglyMeasurable
    apply (fullLogPartition_continuous D.toData (n+1)).comp
    exact continuous_pi fun i => ((polynomialFamily q).continuous.comp
      (continuous_apply i)).add continuous_const
  have hg : AEStronglyMeasurable (fun x : Fin (n+1) → (Fin m → ℝ) =>
      fullLogPartition D.toData (fun i => polynomialFamily g (x i)+c i))
      (Measure.pi fun _ : Fin (n+1) => ν) := by
    apply Continuous.aestronglyMeasurable
    apply (fullLogPartition_continuous D.toData (n+1)).comp
    exact continuous_pi fun i => ((polynomialFamily g).continuous.comp
      (continuous_apply i)).add continuous_const
  rw [integral_pi_fst μ ν (n+1) _ hq,integral_pi_snd μ ν (n+1) _ hg] at h
  exact h

/-- Normalization cancels the number of replacement steps exactly. -/
theorem full_freeEnergy_comparison_of_row_bound {d m : ℕ}
    (D : Data3 κ) (hβ : 0 < D.beta)
    (q : κ → MvPolynomial (Fin d) ℝ) (g : κ → MvPolynomial (Fin m) ℝ)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) (ε : ℝ)
    (hrow : ∀ u : Fin n → κ → ℝ, ∀ v : κ → ℝ,
      |(∫ x, logPartition (otherRowsPrior3 D u).toData (polynomialFamily q x+v)
          ∂gaussianProductLaw (Fin d))-
        ∫ z, logPartition (otherRowsPrior3 D u).toData (polynomialFamily g z+v)
          ∂gaussianProductLaw (Fin m)| ≤ ε) :
    |(∫ x : Fin (n+1) → (Fin d → ℝ), UCActualFreeEnergy.freeEnergy D.toData
        (fun i => polynomialFamily q (x i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d)))-
      ∫ z : Fin (n+1) → (Fin m → ℝ), UCActualFreeEnergy.freeEnergy D.toData
        (fun i => polynomialFamily g (z i)+c i)
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin m))| ≤ ε/D.beta := by
  have h := normalized_expectation_comparison hβ
    (by positivity : (0:ℝ)<(n+1:ℕ))
    (full_logPartition_comparison_of_row_bound D q g n c ε hrow)
  simp only [UCActualFreeEnergy.freeEnergy,integral_div,integral_neg]
  apply h.trans_eq
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by positivity
  field_simp

#print axioms full_logPartition_comparison_of_row_bound
#print axioms full_freeEnergy_comparison_of_row_bound
end GaussianEllipsoid.PaperCavityProduct
