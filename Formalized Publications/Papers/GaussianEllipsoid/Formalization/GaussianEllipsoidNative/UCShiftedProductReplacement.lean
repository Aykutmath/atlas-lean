import BMFiniteGibbsReplacement

/-! Independent-row replacement with arbitrary deterministic shifts depending
on both the row and the candidate. No conditional-law premise is used. -/
noncomputable section
open MeasureTheory BMFiniteGibbsTest BMFiniteGibbsHessian BMProductLogPartition
open BMFiniteProductReplacement BMFiniteGibbsReplacement
open scoped BigOperators BoundedContinuousFunction

namespace GaussianEllipsoid.UCShiftedProductReplacement
variable {κ X : Type*} [Fintype κ] [DecidableEq κ]
variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]

/-- Adding the fixed shift commutes with removing/reinserting the current row. -/
theorem insertNth_add_shift {n : ℕ} (i : Fin (n+1)) (x : κ → ℝ)
    (u : Fin n → κ → ℝ) (c : Fin (n+1) → κ → ℝ) :
    i.insertNth x u + c = i.insertNth (x+c i) (fun j => u j+c (i.succAbove j)) := by
  apply funext
  rw [Fin.forall_iff_succAbove i]
  constructor
  · simp
  · intro j
    simp

/-- State-count-free full-product telescope including row-dependent shifts. -/
theorem full_logPartition_shifted_replacement (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data2 κ) (q g : X → κ → ℝ) (hq : Continuous q) (hg : Continuous g)
    (n : ℕ) (c : Fin (n+1) → κ → ℝ) (ε : ℝ)
    (hrow : ∀ u : Fin n → κ → ℝ, ∀ v : κ → ℝ,
      |(∫ x, logPartition (otherRowsPrior2 D u).toData (q x+v) ∂μ) -
        ∫ x, logPartition (otherRowsPrior2 D u).toData (g x+v) ∂μ| ≤ ε) :
    |(∫ x : Fin (n+1) → X, fullLogPartition D.toData (fun i => q (x i)+c i)
        ∂Measure.pi (fun _ : Fin (n+1) => μ)) -
      ∫ x : Fin (n+1) → X, fullLogPartition D.toData (fun i => g (x i)+c i)
        ∂Measure.pi (fun _ : Fin (n+1) => μ)| ≤ (n+1 : ℕ)*ε := by
  let F := fun k (x : Fin (n+1) → X) =>
    fullLogPartition D.toData (hybridRows q g k x + c)
  have hF (k : ℕ) (_hk : k ≤ n+1) : Integrable (F k) (Measure.pi fun _ : Fin (n+1) => μ) := by
    apply (integrable_const (D.beta*((n+1:ℕ)*‖D.potential‖))).mono'
    · exact ((fullLogPartition_continuous D.toData (n+1)).comp
        ((hybridRows_continuous q g hq hg (n+1) k).add continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => fullLogPartition_abs_le D.toData _
  have hr (i : Fin (n+1)) (u : Fin n → X) :
      |(∫ x, F (i.val+1) (i.insertNth x u) ∂μ) -
        ∫ x, F i.val (i.insertNth x u) ∂μ| ≤ ε := by
    simp only [F, hybridRows_after, hybridRows_before, insertNth_add_shift,
      fullLogPartition_insertNth]
    rw [integral_add (integrable_const _)
        (logPartition_comp_integrable μ _ (fun x => q x+c i) (hq.add continuous_const)),
      integral_add (integrable_const _)
        (logPartition_comp_integrable μ _ (fun x => g x+c i) (hg.add continuous_const))]
    simpa only [add_sub_add_left_eq_sub] using!
      hrow (fun j => otherHybridRows q g i u j + c (i.succAbove j)) (c i)
  have h := finite_product_telescoping μ F ε hF hr
  have hn (x : Fin (n+1) → X) : hybridRows q g (n+1) x = fun i => q (x i) := by
    funext i
    simp [hybridRows,i.isLt]
  have hz (x : Fin (n+1) → X) : hybridRows q g 0 x = fun i => g (x i) := by
    funext i
    simp [hybridRows]
  simpa only [F, hn, hz, Pi.add_def] using h

#print axioms full_logPartition_shifted_replacement
end GaussianEllipsoid.UCShiftedProductReplacement
