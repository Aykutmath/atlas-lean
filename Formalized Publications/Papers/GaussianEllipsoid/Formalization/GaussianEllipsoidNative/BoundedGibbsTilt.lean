import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

open MeasureTheory
namespace GaussianEllipsoidCandidate

noncomputable def boundedGibbsPartition {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) (β : ℝ) : ℝ := ∑ i, ρ i * Real.exp (-β * e i)

noncomputable def boundedGibbsWeight {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) (β : ℝ) (i : ι) : ℝ :=
  ρ i * Real.exp (-β * e i) / boundedGibbsPartition ρ e β

/-- The finite prior may have zero masses. No lower mass per state is needed. -/
theorem boundedGibbsPartition_lower {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) {β M : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hβ : 0 ≤ β) (he : ∀ i, e i ≤ M) :
    Real.exp (-β*M) ≤ boundedGibbsPartition ρ e β := by
  calc
    _ = ∑ i, ρ i * Real.exp (-β*M) := by rw [← Finset.sum_mul, hρsum, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hρ i)
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (he i) hβ]

theorem boundedGibbsPartition_pos {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) {β M : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hβ : 0 ≤ β) (he : ∀ i, e i ≤ M) :
    0 < boundedGibbsPartition ρ e β :=
  (Real.exp_pos _).trans_le (boundedGibbsPartition_lower ρ e hρ hρsum hβ he)

/-- Bounded energy controls each tilted mass by a fixed multiple of its
original prior mass, uniformly in the number of states. -/
theorem boundedGibbsWeight_le {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) {β M : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hβ : 0 ≤ β) (he : ∀ i, |e i| ≤ M) (i : ι) :
    boundedGibbsWeight ρ e β i ≤ Real.exp (2*β*M) * ρ i := by
  have hlo := boundedGibbsPartition_lower ρ e hρ hρsum hβ
    (fun i => (le_abs_self _).trans (he i))
  have hp := boundedGibbsPartition_pos ρ e hρ hρsum hβ
    (fun i => (le_abs_self _).trans (he i))
  unfold boundedGibbsWeight
  apply (div_le_iff₀ hp).2
  calc
    ρ i * Real.exp (-β*e i) ≤ ρ i * Real.exp (β*M) := by
      apply mul_le_mul_of_nonneg_left _ (hρ i)
      apply Real.exp_le_exp.mpr
      have hh := (abs_le.mp (he i)).1
      nlinarith [mul_le_mul_of_nonneg_left hh hβ]
    _ = (Real.exp (2*β*M)*ρ i)*Real.exp (-β*M) := by
      have hx : Real.exp (2*β*M)*Real.exp (-β*M) = Real.exp (β*M) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hx]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (mul_nonneg (Real.exp_nonneg _) (hρ i))

theorem boundedGibbsWeight_nonneg {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) {β M : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hβ : 0 ≤ β) (he : ∀ i, e i ≤ M) (i : ι) :
    0 ≤ boundedGibbsWeight ρ e β i := by
  unfold boundedGibbsWeight
  exact div_nonneg (mul_nonneg (hρ i) (Real.exp_nonneg _))
    (boundedGibbsPartition_pos ρ e hρ hρsum hβ he).le

theorem boundedGibbsWeight_sum {ι : Type*} [Fintype ι]
    (ρ e : ι → ℝ) {β M : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hβ : 0 ≤ β) (he : ∀ i, e i ≤ M) :
    ∑ i, boundedGibbsWeight ρ e β i = 1 := by
  unfold boundedGibbsWeight
  rw [← Finset.sum_div]
  exact div_self (boundedGibbsPartition_pos ρ e hρ hρsum hβ he).ne'

/-- Nonnegative weighted remainders are dominated by their prior averages,
without taking a maximum over Gibbs states. -/
theorem boundedGibbs_remainder_domination {ι : Type*} [Fintype ι]
    (ρ e R : ι → ℝ) {β M : ℝ} (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hβ : 0 ≤ β) (he : ∀ i, |e i| ≤ M) (hR : ∀ i, 0 ≤ R i) :
    (∑ i, boundedGibbsWeight ρ e β i * R i) ≤
      Real.exp (2*β*M) * ∑ i, ρ i * R i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (boundedGibbsWeight_le ρ e hρ hρsum hβ he i) (hR i)

#print axioms boundedGibbsPartition_lower
#print axioms boundedGibbsPartition_pos
#print axioms boundedGibbsWeight_le
#print axioms boundedGibbsWeight_nonneg
#print axioms boundedGibbsWeight_sum
#print axioms boundedGibbs_remainder_domination
end GaussianEllipsoidCandidate
