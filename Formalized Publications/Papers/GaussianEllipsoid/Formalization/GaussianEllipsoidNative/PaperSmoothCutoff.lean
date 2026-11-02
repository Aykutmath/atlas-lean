import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open scoped BigOperators
namespace PaperSmoothCutoff

/-- A smooth extension to all of ℝ of the paper's cutoff χ on [0,∞). -/
def chi (s : ℝ) : ℝ := Real.smoothTransition ((4*s-1)/3)

theorem chi_contDiff {m : ℕ∞} : ContDiff ℝ m chi := by
  unfold chi
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem chi_nonneg (s : ℝ) : 0 ≤ chi s := Real.smoothTransition.nonneg _
theorem chi_le_one (s : ℝ) : chi s ≤ 1 := Real.smoothTransition.le_one _
theorem chi_zero {s : ℝ} (hs : s ≤ 1/4) : chi s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem chi_one {s : ℝ} (hs : 1 ≤ s) : chi s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

/-- The paper's literal ℓ(t) = χ(t²/a²). -/
def loss (a t : ℝ) : ℝ := chi (t^2/a^2)

theorem loss_contDiff (a : ℝ) {m : ℕ∞} : ContDiff ℝ m (loss a) := by
  unfold loss
  exact chi_contDiff.comp (by fun_prop)

theorem loss_C3 (a : ℝ) : ContDiff ℝ 3 (loss a) := loss_contDiff a

theorem loss_nonneg (a t : ℝ) : 0 ≤ loss a t := chi_nonneg _
theorem loss_le_one (a t : ℝ) : loss a t ≤ 1 := chi_le_one _

theorem loss_zero {a t : ℝ} (ha : 0 < a) (ht : |t| ≤ a/2) : loss a t = 0 := by
  apply chi_zero
  apply (div_le_iff₀ (sq_pos_of_pos ha)).2
  have hsq : |t|^2 ≤ (a/2)^2 := sq_le_sq₀ (abs_nonneg t) (by positivity) |>.2 ht
  rw [sq_abs] at hsq
  nlinarith

theorem loss_one {a t : ℝ} (ha : 0 < a) (ht : a ≤ |t|) : loss a t = 1 := by
  apply chi_one
  apply (le_div_iff₀ (sq_pos_of_pos ha)).2
  have hsq : a^2 ≤ |t|^2 := (sq_le_sq₀ (le_of_lt ha) (abs_nonneg t)).2 ht
  simpa using hsq

/-- This is a function-growth bound; it is not a bound on derivatives. -/
theorem loss_linear_bound {a : ℝ} (ha : 0 < a) (t : ℝ) :
    loss a t ≤ (2/a)*|t| := by
  by_cases ht : |t| ≤ a/2
  · rw [loss_zero ha ht]
    positivity
  · have h : 1 ≤ (2/a)*|t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      linarith
    exact (loss_le_one a t).trans h

/-- Counting coordinates above a gives the paper's empirical loss floor. -/
theorem average_ge_fraction {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a)
    (r : Fin n → ℝ) :
    ((Finset.univ.filter (fun i => a ≤ |r i|)).card : ℝ)/(n:ℝ) ≤
      (∑ i, loss a (r i))/(n:ℝ) := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    ((Finset.univ.filter (fun i => a ≤ |r i|)).card : ℝ) =
        ∑ i ∈ Finset.univ.filter (fun i => a ≤ |r i|), loss a (r i) := by
      symm
      calc
        _ = ∑ _i ∈ Finset.univ.filter (fun i => a ≤ |r i|), (1:ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact loss_one ha (Finset.mem_filter.mp hi).2
        _ = _ := by simp
    _ ≤ ∑ i, loss a (r i) := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (by intros; exact loss_nonneg _ _)

theorem average_ge_of_count {n : ℕ} (hn : 0 < n) {a θ : ℝ} (ha : 0 < a)
    (r : Fin n → ℝ)
    (hcount : θ*(n:ℝ) < ((Finset.univ.filter (fun i => a ≤ |r i|)).card : ℝ)) :
    θ ≤ (∑ i, loss a (r i))/(n:ℝ) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  exact (le_of_lt ((lt_div_iff₀ hn').2 hcount)).trans (average_ge_fraction hn ha r)

#print axioms chi_contDiff
#print axioms loss_C3
#print axioms loss_zero
#print axioms loss_one
#print axioms loss_linear_bound
#print axioms average_ge_fraction
#print axioms average_ge_of_count
end PaperSmoothCutoff
