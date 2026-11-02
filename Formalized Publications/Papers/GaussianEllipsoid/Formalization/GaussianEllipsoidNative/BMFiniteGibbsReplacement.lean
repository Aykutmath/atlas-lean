import BMProductLogPartition

noncomputable section
open MeasureTheory BMFiniteGibbsTest BMFiniteGibbsHessian BMProductLogPartition
open BMFiniteProductReplacement
open scoped BigOperators BoundedContinuousFunction

namespace BMFiniteGibbsReplacement
variable {κ X : Type*} [Fintype κ] [DecidableEq κ]
variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]

/-- First k rows are quadratic, the remaining rows Gaussian. Both observables
are realized on a common independent source row. -/
def hybridRows (q g : X → κ → ℝ) {n : ℕ} (k : ℕ) (x : Fin n → X) : Fin n → κ → ℝ :=
  fun i => if i.val < k then q (x i) else g (x i)

def otherHybridRows (q g : X → κ → ℝ) {n : ℕ} (i : Fin (n+1))
    (u : Fin n → X) : Fin n → κ → ℝ :=
  fun j => if (i.succAbove j).val < i.val then q (u j) else g (u j)

theorem hybridRows_continuous (q g : X → κ → ℝ) (hq : Continuous q) (hg : Continuous g)
    (n k : ℕ) : Continuous (hybridRows q g (n := n) k) := by
  apply continuous_pi
  intro i
  unfold hybridRows
  split_ifs
  · exact hq.comp (continuous_apply i)
  · exact hg.comp (continuous_apply i)

theorem hybridRows_before {n : ℕ} (q g : X → κ → ℝ) (i : Fin (n+1))
    (u : Fin n → X) (x : X) :
    hybridRows q g i.val (i.insertNth x u) = i.insertNth (g x) (otherHybridRows q g i u) := by
  apply funext
  rw [Fin.forall_iff_succAbove i]
  constructor
  · simp [hybridRows]
  · intro l
    simp [hybridRows,otherHybridRows]

theorem hybridRows_after {n : ℕ} (q g : X → κ → ℝ) (i : Fin (n+1))
    (u : Fin n → X) (x : X) :
    hybridRows q g (i.val+1) (i.insertNth x u) = i.insertNth (q x) (otherHybridRows q g i u) := by
  apply funext
  rw [Fin.forall_iff_succAbove i]
  constructor
  · simp [hybridRows]
  · intro l
    have hne : (i.succAbove l).val ≠ i.val := by
      intro h
      exact i.succAbove_ne l (Fin.eq_of_val_eq h)
    have he : (i.succAbove l).val < i.val+1 ↔ (i.succAbove l).val < i.val := by omega
    simp [hybridRows,otherHybridRows,he]

theorem fullLogPartition_hybrid_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (q g : X → κ → ℝ) (hq : Continuous q) (hg : Continuous g)
    (n k : ℕ) : Integrable (fun x : Fin n → X => fullLogPartition D (hybridRows q g k x))
      (Measure.pi fun _ : Fin n => μ) := by
  apply (integrable_const (D.beta*(n*‖D.potential‖))).mono'
  · exact ((fullLogPartition_continuous D n).comp (hybridRows_continuous q g hq hg n k)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => fullLogPartition_abs_le D _

theorem logPartition_comp_integrable (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data κ) (q : X → κ → ℝ) (hq : Continuous q) :
    Integrable (fun x => logPartition D (q x)) μ := by
  apply (integrable_const (D.beta*‖D.potential‖)).mono'
  · exact ((logPartition_continuous D).comp hq).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => logPartition_norm_le D _

/-- Finite-prior, actual-product replacement for the full log partition.
The one-row comparison is required only at explicit Gibbs priors generated
from fixed other rows; these priors are probability vectors by construction. -/
theorem full_logPartition_replacement (μ : Measure X) [IsProbabilityMeasure μ]
    (D : Data2 κ) (q g : X → κ → ℝ) (hq : Continuous q) (hg : Continuous g)
    (n : ℕ) (ε : ℝ)
    (hrow : ∀ u : Fin n → κ → ℝ,
      |(∫ x, logPartition (otherRowsPrior2 D u).toData (q x) ∂μ) -
        ∫ x, logPartition (otherRowsPrior2 D u).toData (g x) ∂μ| ≤ ε) :
    |(∫ x : Fin (n+1) → X, fullLogPartition D.toData (fun i => q (x i))
        ∂Measure.pi (fun _ : Fin (n+1) => μ)) -
      ∫ x : Fin (n+1) → X, fullLogPartition D.toData (fun i => g (x i))
        ∂Measure.pi (fun _ : Fin (n+1) => μ)| ≤ (n+1 : ℕ)*ε := by
  let F := fun k (x : Fin (n+1) → X) => fullLogPartition D.toData (hybridRows q g k x)
  have hF (k : ℕ) (_hk : k ≤ n+1) : Integrable (F k) (Measure.pi fun _ : Fin (n+1) => μ) :=
    fullLogPartition_hybrid_integrable μ D.toData q g hq hg (n+1) k
  have hr (i : Fin (n+1)) (u : Fin n → X) :
      |(∫ x, F (i.val+1) (i.insertNth x u) ∂μ) -
        ∫ x, F i.val (i.insertNth x u) ∂μ| ≤ ε := by
    simp only [F,hybridRows_after,hybridRows_before,fullLogPartition_insertNth]
    rw [integral_add (integrable_const _) (logPartition_comp_integrable μ _ q hq),
      integral_add (integrable_const _) (logPartition_comp_integrable μ _ g hg)]
    simpa only [add_sub_add_left_eq_sub] using! hrow (otherHybridRows q g i u)
  have h := finite_product_telescoping μ F ε hF hr
  have hn (x : Fin (n+1) → X) : hybridRows q g (n+1) x = fun i => q (x i) := by
    funext i
    simp [hybridRows,i.isLt]
  have hz (x : Fin (n+1) → X) : hybridRows q g 0 x = fun i => g (x i) := by
    funext i
    simp [hybridRows]
  simpa only [F,hn,hz] using h

#print axioms full_logPartition_replacement
end BMFiniteGibbsReplacement
