import UCQuadraticMGF
import Mathlib.MeasureTheory.Integral.Pi

/-! An actual iid-product Chernoff bound for every symmetric Frobenius-unit
center. The constants are universal and dimension-free. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace GaussianEllipsoid.UCQuadraticSampleTail

/-- Exponential moment of the full actual independent-row absolute sum. -/
theorem sample_exp_abs_sum {d n : ℕ} (hd : 0 < d) (A : Square d)
    (hA : A.transpose = A) (hF : frobeniusNorm A ≤ 1) :
    Integrable (fun x : Sample d n => Real.exp ((∑ i, |measurementQ x A i|)/8))
      (gaussianSampleLaw d n) ∧
    (∫ x : Sample d n, Real.exp ((∑ i, |measurementQ x A i|)/8) ∂gaussianSampleLaw d n)
      ≤ Real.exp (2*(n:ℝ)) := by
  have hrow := UCQuadraticMGF.quadratic_exp_abs hd A hA hF
  let f : Vector d → ℝ := fun z => Real.exp (|(quadratic A z-Matrix.trace A)/Real.sqrt 2|/8)
  have he (x : Sample d n) : Real.exp ((∑ i, |measurementQ x A i|)/8) = ∏ i, f (x i) := by
    rw [Finset.sum_div, Real.exp_sum]
    rfl
  simp_rw [he]
  refine ⟨Integrable.fintype_prod_dep (fun _ : Fin n => hrow.1), ?_⟩
  rw [show (gaussianSampleLaw d n) = Measure.pi (fun _ : Fin n => gaussianVectorLaw d) from rfl,
    integral_fintype_prod_eq_prod (fun _ : Fin n => f), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hnn : 0 ≤ ∫ z, f z ∂gaussianVectorLaw d := integral_nonneg fun z => Real.exp_nonneg _
  calc
    _ ≤ (2*Real.exp 1)^n := pow_le_pow_left₀ hnn hrow.2 n
    _ ≤ (Real.exp 2)^n := by
      apply pow_le_pow_left₀ (by positivity)
      have hh : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
      calc
        2*Real.exp 1 ≤ Real.exp 1*Real.exp 1 := mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
        _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- Universal per-center exponential tail for the averaged absolute quadratic
row values. -/
theorem sample_mean_abs_tail {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (A : Square d)
    (hA : A.transpose = A) (hF : frobeniusNorm A ≤ 1) (b : ℝ) :
    (gaussianSampleLaw d n).real {x | b < (1/(n:ℝ))*∑ i, |measurementQ x A i|} ≤
      Real.exp ((n:ℝ)*(2-b/8)) := by
  have hi := sample_exp_abs_sum hd A hA hF (n := n)
  let Y : Sample d n → ℝ := fun x => ∑ i, |measurementQ x A i|
  have hi' : Integrable (fun x => Real.exp ((1/8:ℝ)*Y x)) (gaussianSampleLaw d n) := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul, Y] using hi.1
  have ht := measure_ge_le_exp_mul_mgf (μ := gaussianSampleLaw d n) (X := Y)
    ((n:ℝ)*b) (t := 1/8) (by norm_num) hi'
  have hm : mgf Y (gaussianSampleLaw d n) (1/8) ≤ Real.exp (2*(n:ℝ)) := by
    simpa only [mgf, Y, div_eq_mul_inv, mul_comm, one_mul] using hi.2
  have he : (gaussianSampleLaw d n).real {x | b < (1/(n:ℝ))*∑ i, |measurementQ x A i|} ≤
      (gaussianSampleLaw d n).real {x | (n:ℝ)*b ≤ Y x} := by
    refine measureReal_mono (μ := gaussianSampleLaw d n) ?_
    intro x hx
    change b < (1/(n:ℝ))*Y x at hx
    change (n:ℝ)*b ≤ Y x
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    have hh := (lt_div_iff₀ hn').mp (show b < Y x/(n:ℝ) by simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul,mul_one] using hx)
    linarith
  apply he.trans (ht.trans _)
  calc
    _ ≤ Real.exp (-(1/8:ℝ)*((n:ℝ)*b))*Real.exp (2*(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

#print axioms sample_mean_abs_tail
end GaussianEllipsoid.UCQuadraticSampleTail
