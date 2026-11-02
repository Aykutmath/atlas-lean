import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace GaussianEllipsoid

def fourAdicRadius (R : ℝ) (j : ℕ) : ℝ := 2 * R / (2 : ℝ) ^ j

def fourAdicError (ε : ℝ) (J j : ℕ) : ℝ := (ε / 4) * (2 : ℝ) ^ j / (2 : ℝ) ^ J

lemma geometric_two_sum (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j = 2 ^ (J + 1) - 1 := by
  induction J with
  | zero => norm_num
  | succ J ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma geometric_four_sum (J : ℕ) :
    3 * (∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j) + 1 = 4 ^ (J + 1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ]
    nlinarith [show (4 : ℝ) ^ (J + 1 + 1) = 4 ^ (J + 1) * 4 from pow_succ 4 (J + 1)]

theorem sum_fourAdicError_lt {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), fourAdicError ε J j < ε / 2 := by
  simp only [fourAdicError, ← Finset.sum_div, ← Finset.mul_sum, geometric_two_sum]
  have hp : (0 : ℝ) < 2 ^ J := by positivity
  apply (div_lt_iff₀ hp).mpr
  rw [pow_succ]
  nlinarith

/-- Exact finite weighted-geometric identity used to sum covering entropies. -/
theorem fourAdic_weighted_sum_identity (J : ℕ) :
    9 * (∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j * (5 + 2 * (J : ℝ) - 2 * j)) +
      6 * J + 23 = 68 * 4 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hterm (j : ℕ) :
        (4 : ℝ) ^ j * (5 + 2 * ((J + 1 : ℕ) : ℝ) - 2 * j) =
        (4 : ℝ) ^ j * (5 + 2 * (J : ℝ) - 2 * j) + 2 * 4 ^ j := by push_cast; ring
    simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hgeo := geometric_four_sum J
    push_cast
    rw [pow_succ] at hgeo ⊢
    nlinarith

theorem fourAdic_weighted_sum_le (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), (4 : ℝ) ^ j * (5 + 2 * (J : ℝ) - 2 * j) ≤ 8 * 4 ^ J := by
  have h := fourAdic_weighted_sum_identity J
  have hp : (0 : ℝ) < 4 ^ J := by positivity
  have hj : (0 : ℝ) ≤ J := by positivity
  nlinarith

/-- A deliberately conservative logarithmic bound, avoiding numerical exp/log
approximations while retaining the final universal constant 256. -/
theorem fourAdic_log_base_le {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (J j : ℕ) (hj : j ≤ J) (hscale : 2 * R ≤ ε * (2 : ℝ) ^ J) :
    Real.log (1 + 4 * fourAdicRadius R j / fourAdicError ε J j) ≤
      5 + 2 * (J : ℝ) - 2 * (j : ℝ) := by
  have hpj : (0 : ℝ) < 2 ^ j := by positivity
  have hpJ : (0 : ℝ) < 2 ^ J := by positivity
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
  have hbase : 1 + 4 * fourAdicRadius R j / fourAdicError ε J j ≤
      32 * ((2 : ℝ) ^ J) ^ 2 / ((2 : ℝ) ^ j) ^ 2 := by
    dsimp [fourAdicRadius, fourAdicError]
    have heq : 4 * (2 * R / (2 : ℝ) ^ j) / (ε / 4 * 2 ^ j / 2 ^ J) =
        32 * R * 2 ^ J / (ε * (2 ^ j) ^ 2) := by field_simp <;> ring
    rw [heq]
    have hm : 32 * R * 2 ^ J ≤ 16 * ε * (2 ^ J) ^ 2 := by nlinarith
    have hpowsq := pow_le_pow_left₀ hpj.le hpow 2
    have hnum : ε * (2 ^ j) ^ 2 + 32 * R * 2 ^ J ≤ 32 * ε * (2 ^ J) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hpowsq hε.le]
    have hnorm : 1 + 32 * R * 2 ^ J / (ε * (2 ^ j) ^ 2) =
        (ε * (2 ^ j) ^ 2 + 32 * R * 2 ^ J) / (ε * (2 ^ j) ^ 2) := by field_simp
    rw [hnorm]
    calc
      (ε * (2 ^ j) ^ 2 + 32 * R * 2 ^ J) / (ε * (2 ^ j) ^ 2) ≤
          (32 * ε * (2 ^ J) ^ 2) / (ε * (2 ^ j) ^ 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = 32 * (2 ^ J) ^ 2 / (2 ^ j) ^ 2 := by field_simp <;> ring
  have hpos : 0 < 1 + 4 * fourAdicRadius R j / fourAdicError ε J j := by
    dsimp [fourAdicRadius, fourAdicError]; positivity
  have hlog := Real.log_le_log hpos hbase
  have hlog2 : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hweight : 0 ≤ 5 + 2 * (J : ℝ) - 2 * (j : ℝ) := by
    have : (j : ℝ) ≤ J := by exact_mod_cast hj
    linarith
  calc
    Real.log (1 + 4 * fourAdicRadius R j / fourAdicError ε J j) ≤
        Real.log (32 * ((2 : ℝ) ^ J) ^ 2 / ((2 : ℝ) ^ j) ^ 2) := hlog
    _ = (5 + 2 * (J : ℝ) - 2 * (j : ℝ)) * Real.log 2 := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)]
      have h32 : Real.log 32 = 5 * Real.log 2 := by
        convert Real.log_pow 2 5 using 1 <;> norm_num
      rw [h32]
      simp only [Real.log_pow]
      push_cast
      ring
    _ ≤ 5 + 2 * (J : ℝ) - 2 * (j : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hlog2 hweight


theorem fourAdic_entropy_sum_le {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (r J : ℕ) (hscale : 2 * R ≤ ε * (2 : ℝ) ^ J) :
    ∑ j ∈ Finset.range (J + 1),
      ((2 * r * 4 ^ j : ℕ) : ℝ) *
        Real.log (1 + 4 * fourAdicRadius R j / fourAdicError ε J j) ≤
      16 * r * (4 : ℝ) ^ J := by
  calc
    ∑ j ∈ Finset.range (J + 1), ((2 * r * 4 ^ j : ℕ) : ℝ) *
        Real.log (1 + 4 * fourAdicRadius R j / fourAdicError ε J j) ≤
        ∑ j ∈ Finset.range (J + 1), (2 * r : ℝ) * (4 : ℝ) ^ j *
          (5 + 2 * (J : ℝ) - 2 * (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j ≤ J := by have := Finset.mem_range.mp hj; omega
      convert mul_le_mul_of_nonneg_left (fourAdic_log_base_le hR hε J j hj' hscale)
        (by positivity : (0 : ℝ) ≤ ((2 * r * 4 ^ j : ℕ) : ℝ)) using 1 <;> push_cast <;> ring
    _ = (2 * r : ℝ) * ∑ j ∈ Finset.range (J + 1),
          (4 : ℝ) ^ j * (5 + 2 * (J : ℝ) - 2 * (j : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (2 * r : ℝ) * (8 * (4 : ℝ) ^ J) :=
      mul_le_mul_of_nonneg_left (fourAdic_weighted_sum_le J) (by positivity)
    _ = 16 * r * (4 : ℝ) ^ J := by ring

theorem exists_fourAdic_scale {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R) :
    ∃ J : ℕ, 2 * R ≤ ε * (2 : ℝ) ^ J ∧ (4 : ℝ) ^ J ≤ 16 * R ^ 2 / ε ^ 2 := by
  have hx : 1 ≤ 2 * R / ε := by apply (le_div_iff₀ hε).mpr; linarith
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨n + 1, ?_, ?_⟩
  · have := (div_lt_iff₀ hε).mp hn'
    nlinarith
  · have hu : (2 : ℝ) ^ (n + 1) ≤ 4 * R / ε := by
      rw [pow_succ]
      calc (2 : ℝ) ^ n * 2 ≤ (2 * R / ε) * 2 := mul_le_mul_of_nonneg_right hn (by norm_num)
           _ = 4 * R / ε := by ring
    have hu2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1)) hu 2
    have hid : (4 : ℝ) ^ (n + 1) = ((2 : ℝ) ^ (n + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm (n + 1) 2, pow_mul]
      norm_num
    rw [hid]
    calc ((2 : ℝ) ^ (n + 1)) ^ 2 ≤ (4 * R / ε) ^ 2 := hu2
         _ = 16 * R ^ 2 / ε ^ 2 := by ring

end GaussianEllipsoid
#print axioms GaussianEllipsoid.sum_fourAdicError_lt
#print axioms GaussianEllipsoid.fourAdic_weighted_sum_le
#print axioms GaussianEllipsoid.fourAdic_log_base_le

#print axioms GaussianEllipsoid.fourAdic_entropy_sum_le
#print axioms GaussianEllipsoid.exists_fourAdic_scale
