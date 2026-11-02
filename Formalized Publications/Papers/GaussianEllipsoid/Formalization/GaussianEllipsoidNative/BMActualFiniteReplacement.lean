import BMFiniteGibbsReplacement
import BMGibbsRowReplacement

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMAffineSmooth BMFiniteGibbsTest BMFiniteGibbsHessian
open BMProductLogPartition BMFiniteGibbsReplacement BMGibbsRowReplacement
open scoped BigOperators BoundedContinuousFunction

namespace BMActualFiniteReplacement
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Integration through a measure-preserving map does not require injectivity
when the target integrand is measurable. -/
theorem integral_comp_measurePreserving {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    {μ : Measure U} {ν : Measure V} {f : U → V} (hf : MeasurePreserving f μ ν)
    (H : V → ℝ) (hH : AEStronglyMeasurable H ν) :
    (∫ u, H (f u) ∂μ) = ∫ v, H v ∂ν := by
  have h := integral_map hf.aemeasurable (hf.map_eq.symm ▸ hH)
  rw [hf.map_eq] at h
  exact h.symm

theorem integral_pi_fst {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (H : (Fin n → U) → ℝ) (hH : AEStronglyMeasurable H (Measure.pi fun _ : Fin n => μ)) :
    (∫ x : Fin n → U × V, H (fun i => (x i).1) ∂Measure.pi (fun _ : Fin n => μ.prod ν)) =
      ∫ u : Fin n → U, H u ∂Measure.pi (fun _ : Fin n => μ) := by
  have hp : MeasurePreserving (@Prod.fst U V) (μ.prod ν) μ := ⟨measurable_fst,by simp⟩
  exact integral_comp_measurePreserving
    (measurePreserving_pi (fun _ : Fin n => μ.prod ν) (fun _ : Fin n => μ) (fun _ => hp)) H hH

theorem integral_pi_snd {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (μ : Measure U) (ν : Measure V) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (n : ℕ) (H : (Fin n → V) → ℝ) (hH : AEStronglyMeasurable H (Measure.pi fun _ : Fin n => ν)) :
    (∫ x : Fin n → U × V, H (fun i => (x i).2) ∂Measure.pi (fun _ : Fin n => μ.prod ν)) =
      ∫ u : Fin n → V, H u ∂Measure.pi (fun _ : Fin n => ν) := by
  have hp : MeasurePreserving (@Prod.snd U V) (μ.prod ν) ν := ⟨measurable_snd,by simp⟩
  exact integral_comp_measurePreserving
    (measurePreserving_pi (fun _ : Fin n => μ.prod ν) (fun _ : Fin n => ν) (fun _ => hp)) H hH

@[simp] theorem replacementError_otherRowsPrior2 (D : Data2 κ) {n : ℕ}
    (u : Fin n → κ → ℝ) (K : ℝ) (d : ℕ) :
    replacementError (otherRowsPrior2 D u) K d = replacementError D K d := rfl

/-- State-count-free replacement under the two actual iid Gaussian source laws.
The quadratic source is the centered rank-one matrix model; the comparison
source consists of the stated covariance-matched linear Gaussian forms.
This theorem calls the fully proved one-row Stein theorem. -/
theorem actual_finite_logPartition_replacement {d m : ℕ}
    (D : Data2 κ) (A : κ → Matrix (Fin d) (Fin d) ℝ)
    (hAsym : ∀ a, (A a).transpose = A a) (B : κ → Fin m → ℝ)
    (hCov : ∀ a b, (∑ i, B a i*B b i) = 2/(d:ℝ)*Matrix.trace (A a*A b))
    (hd : 0 < d) {K : ℝ} (hK : 0 ≤ K) (hA : ∀ a, spectralNorm (A a) ≤ K)
    (n : ℕ) :
    |(∫ x : Fin (n+1) → (Fin d → ℝ), fullLogPartition D.toData
        (fun i => polynomialFamily (fun a => normalizedQuadratic d (A a)) (x i))
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin d))) -
      ∫ z : Fin (n+1) → (Fin m → ℝ), fullLogPartition D.toData
        (fun i => polynomialFamily (fun a => linearPolynomial (B a)) (z i))
          ∂Measure.pi (fun _ : Fin (n+1) => gaussianProductLaw (Fin m))| ≤
      (n+1 : ℕ)*replacementError D K d := by
  let q := polynomialFamily (fun a => normalizedQuadratic d (A a))
  let g := polynomialFamily (fun a => linearPolynomial (B a))
  let μ := gaussianProductLaw (Fin d)
  let ν := gaussianProductLaw (Fin m)
  have hrow (u : Fin n → κ → ℝ) :
      |(∫ x : (Fin d → ℝ) × (Fin m → ℝ),
          logPartition (otherRowsPrior2 D u).toData (q x.1) ∂μ.prod ν) -
        ∫ x : (Fin d → ℝ) × (Fin m → ℝ),
          logPartition (otherRowsPrior2 D u).toData (g x.2) ∂μ.prod ν| ≤ replacementError D K d := by
    rw [integral_fun_fst (fun x => logPartition (otherRowsPrior2 D u).toData (q x)),
      integral_fun_snd (fun x => logPartition (otherRowsPrior2 D u).toData (g x))]
    simpa only [probReal_univ,one_smul,replacementError_otherRowsPrior2] using
      one_row_gibbs_replacement (otherRowsPrior2 D u) A hAsym B hCov hd hK hA
  have h := full_logPartition_replacement (μ.prod ν) D (fun z => q z.1) (fun z => g z.2)
    (q.continuous.comp continuous_fst) (g.continuous.comp continuous_snd) n
    (replacementError D K d) hrow
  have hq : AEStronglyMeasurable (fun x : Fin (n+1) → (Fin d → ℝ) =>
      fullLogPartition D.toData (fun i => q (x i))) (Measure.pi fun _ : Fin (n+1) => μ) := by
    apply Continuous.aestronglyMeasurable
    apply (fullLogPartition_continuous D.toData (n+1)).comp
    exact continuous_pi fun i => q.continuous.comp (continuous_apply i)
  have hg : AEStronglyMeasurable (fun x : Fin (n+1) → (Fin m → ℝ) =>
      fullLogPartition D.toData (fun i => g (x i))) (Measure.pi fun _ : Fin (n+1) => ν) := by
    apply Continuous.aestronglyMeasurable
    apply (fullLogPartition_continuous D.toData (n+1)).comp
    exact continuous_pi fun i => g.continuous.comp (continuous_apply i)
  rw [integral_pi_fst μ ν (n+1) _ hq,integral_pi_snd μ ν (n+1) _ hg] at h
  exact h

#print axioms actual_finite_logPartition_replacement
end BMActualFiniteReplacement
