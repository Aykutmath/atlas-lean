import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

noncomputable section
namespace GaussianEllipsoid

/-- Exact exponential decay for the sparse-prefix support and quarter-net union. -/
theorem sparse_support_entropy_bound (A : ℝ) (hA : 0 < A)
    (d n : ℕ) (hd : 8192 ≤ d) (hAd : 9*(A+1) ≤ (d:ℝ))
    (hn : (n:ℝ) ≤ A*(d:ℝ)^2) :
    4*(9*((n:ℝ)+1))^(Nat.floor ((d:ℝ)/(8192*Real.log (d:ℝ)))) *
      Real.exp (-((2*(d/4):ℕ):ℝ)/256) ≤ Real.exp (-(d:ℝ)/2048) := by
  let m : ℕ := Nat.floor ((d:ℝ)/(8192*Real.log (d:ℝ)))
  let h : ℕ := 2*(d/4)
  have hdR : (8192:ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0:ℝ) < d := by linarith
  have hlog : 0 < Real.log (d:ℝ) := Real.log_pos (by linarith)
  have hb : 0 < 9*((n:ℝ)+1) := by positivity
  have hn1 : (n:ℝ)+1 ≤ (A+1)*(d:ℝ)^2 := by nlinarith
  have hbase : 9*((n:ℝ)+1) ≤ (d:ℝ)^3 := by
    calc
      _ ≤ 9*((A+1)*(d:ℝ)^2) := mul_le_mul_of_nonneg_left hn1 (by norm_num)
      _ = (9*(A+1))*(d:ℝ)^2 := by ring
      _ ≤ (d:ℝ)*(d:ℝ)^2 := mul_le_mul_of_nonneg_right hAd (sq_nonneg _)
      _ = _ := by ring
  have hlbase : Real.log (9*((n:ℝ)+1)) ≤ 3*Real.log (d:ℝ) := by
    have hh := Real.log_le_log hb hbase
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hml : (m:ℝ) ≤ (d:ℝ)/(8192*Real.log (d:ℝ)) := by
    exact Nat.floor_le (by positivity)
  have hmexp : (m:ℝ)*Real.log (9*((n:ℝ)+1)) ≤ 3*(d:ℝ)/8192 := by
    calc
      _ ≤ (m:ℝ)*(3*Real.log (d:ℝ)) := mul_le_mul_of_nonneg_left hlbase (by positivity)
      _ ≤ ((d:ℝ)/(8192*Real.log (d:ℝ)))*(3*Real.log (d:ℝ)) :=
        mul_le_mul_of_nonneg_right hml (by positivity)
      _ = _ := by field_simp <;> ring
  have hhNat : d ≤ 3*h := by dsimp [h]; omega
  have hhR : (d:ℝ) ≤ 3*(h:ℝ) := by exact_mod_cast hhNat
  have hlog4 : Real.log (4:ℝ) ≤ 2 := by
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have he : Real.log (4:ℝ) = 2*Real.log 2 := by
      rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hexp : Real.log 4+(m:ℝ)*Real.log (9*((n:ℝ)+1))-(h:ℝ)/256 ≤ -(d:ℝ)/2048 := by
    linarith
  have heq : 4*(9*((n:ℝ)+1))^m * Real.exp (-(h:ℝ)/256) =
      Real.exp (Real.log 4+(m:ℝ)*Real.log (9*((n:ℝ)+1))-(h:ℝ)/256) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
      Real.exp_log (by norm_num : (0:ℝ)<4), Real.exp_nat_mul, Real.exp_log hb]
    rw [neg_div]
  change 4*(9*((n:ℝ)+1))^m * Real.exp (-(h:ℝ)/256) ≤ _
  rw [heq]
  exact Real.exp_le_exp.mpr hexp

/-- A concrete natural starting dimension depending only on the fixed aspect bound. -/
def sparseEntropyCutoff (A : ℝ) : ℕ := max 8192 (Nat.ceil (9*(A+1)))

theorem sparse_support_entropy_eventual (A : ℝ) (hA : 0 < A)
    (d n : ℕ) (hd : sparseEntropyCutoff A ≤ d)
    (hn : (n:ℝ) ≤ A*(d:ℝ)^2) :
    4*(9*((n:ℝ)+1))^(Nat.floor ((d:ℝ)/(8192*Real.log (d:ℝ)))) *
      Real.exp (-((2*(d/4):ℕ):ℝ)/256) ≤ Real.exp (-(d:ℝ)/2048) := by
  apply sparse_support_entropy_bound A hA d n
  · exact (le_max_left _ _).trans hd
  · have hceil : Nat.ceil (9*(A+1)) ≤ d := (le_max_right _ _).trans hd
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  · exact hn

#print axioms sparse_support_entropy_bound
#print axioms sparse_support_entropy_eventual
end GaussianEllipsoid
