import BMFiniteGibbsHessian
import BMFiniteProductReplacement

noncomputable section
open MeasureTheory BMFiniteGibbsTest BMFiniteGibbsHessian
open scoped BigOperators BoundedContinuousFunction

namespace BMProductLogPartition
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def rowSum (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) (a : κ) : ℝ :=
  ∑ i, D.potential (y i a)

def fullPartition (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) : ℝ :=
  ∑ a, D.weight a * Real.exp (-D.beta*rowSum D y a)

def fullLogPartition (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) : ℝ :=
  Real.log (fullPartition D y)

theorem rowSum_abs_le (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) (a : κ) :
    |rowSum D y a| ≤ n*‖D.potential‖ := by
  calc
    _ ≤ ∑ i, |D.potential (y i a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖D.potential‖ := Finset.sum_le_sum fun i _ => D.potential.norm_coe_le_norm _
    _ = _ := by simp

theorem fullPartition_lower (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) :
    Real.exp (-D.beta*(n*‖D.potential‖)) ≤ fullPartition D y := by
  calc
    _ = ∑ a, D.weight a * Real.exp (-D.beta*(n*‖D.potential‖)) := by
      rw [← Finset.sum_mul,D.weight_sum,one_mul]
    _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (rowSum_abs_le D y a)).2,D.beta_nonneg]))
      (D.weight_nonneg a)

theorem fullPartition_upper (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) :
    fullPartition D y ≤ Real.exp (D.beta*(n*‖D.potential‖)) := by
  calc
    _ ≤ ∑ a, D.weight a * Real.exp (D.beta*(n*‖D.potential‖)) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [(abs_le.mp (rowSum_abs_le D y a)).1,D.beta_nonneg]))
        (D.weight_nonneg a)
    _ = _ := by rw [← Finset.sum_mul,D.weight_sum,one_mul]

theorem fullPartition_pos (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) :
    0 < fullPartition D y := (Real.exp_pos _).trans_le (fullPartition_lower D y)

theorem fullLogPartition_abs_le (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) :
    |fullLogPartition D y| ≤ D.beta*(n*‖D.potential‖) := by
  have hl := Real.log_le_log (Real.exp_pos _) (fullPartition_lower D y)
  have hu := Real.log_le_log (fullPartition_pos D y) (fullPartition_upper D y)
  rw [Real.log_exp] at hl hu
  exact abs_le.mpr ⟨by simpa [fullLogPartition] using hl,hu⟩

theorem fullPartition_continuous (D : Data κ) (n : ℕ) :
    Continuous (fullPartition D (n := n)) := by
  apply continuous_finset_sum
  intro a ha
  apply continuous_const.mul
  apply Real.continuous_exp.comp
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i hi
  exact D.potential.continuous.comp ((continuous_apply a).comp (continuous_apply i))

theorem fullLogPartition_continuous (D : Data κ) (n : ℕ) :
    Continuous (fullLogPartition D (n := n)) :=
  (fullPartition_continuous D n).log (fun y => ne_of_gt (fullPartition_pos D y))

/-- The prior formed from all other rows is a literal finite probability vector. -/
def otherRowsPrior (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) : Data κ :=
  { D with
    weight := fun a => (D.weight a*Real.exp (-D.beta*rowSum D y a))/fullPartition D y
    weight_nonneg := fun a => div_nonneg (mul_nonneg (D.weight_nonneg a) (Real.exp_pos _).le)
      (fullPartition_pos D y).le
    weight_sum := by
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt (fullPartition_pos D y)) }

def otherRowsPrior2 (D : Data2 κ) {n : ℕ} (y : Fin n → κ → ℝ) : Data2 κ :=
  { D with toData := otherRowsPrior D.toData y }

@[simp] theorem otherRowsPrior_potential (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) :
    (otherRowsPrior D y).potential = D.potential := rfl

@[simp] theorem otherRowsPrior_beta (D : Data κ) {n : ℕ} (y : Fin n → κ → ℝ) :
    (otherRowsPrior D y).beta = D.beta := rfl

/-- Exact factorization, including the original normalization factor. -/
theorem fullPartition_insertNth (D : Data κ) {n : ℕ} (i : Fin (n+1))
    (u : Fin n → κ → ℝ) (x : κ → ℝ) :
    fullPartition D (i.insertNth x u) =
      fullPartition D u * partition (otherRowsPrior D u) x := by
  unfold fullPartition partition otherRowsPrior
  simp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hs : rowSum D (i.insertNth x u) a = D.potential (x a)+rowSum D u a := by
    unfold rowSum
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
  rw [hs, mul_add,Real.exp_add]
  have hz := ne_of_gt (fullPartition_pos D u)
  dsimp only [fullPartition] at hz
  dsimp only [fullPartition]
  field_simp [hz]
  <;> ring_nf
  simp only [neg_mul] at hz
  simp only [mul_assoc, mul_inv_cancel₀ hz, mul_one]

/-- Exact leave-one-row log-partition identity. The fixed-other-row term cancels
between the two one-row expectations. -/
theorem fullLogPartition_insertNth (D : Data κ) {n : ℕ} (i : Fin (n+1))
    (u : Fin n → κ → ℝ) (x : κ → ℝ) :
    fullLogPartition D (i.insertNth x u) =
      fullLogPartition D u + logPartition (otherRowsPrior D u) x := by
  unfold fullLogPartition logPartition
  rw [fullPartition_insertNth,Real.log_mul (ne_of_gt (fullPartition_pos D u))
    (ne_of_gt (partition_pos (otherRowsPrior D u) x))]

#print axioms fullLogPartition_insertNth
#print axioms fullLogPartition_abs_le
#print axioms otherRowsPrior2
end BMProductLogPartition
