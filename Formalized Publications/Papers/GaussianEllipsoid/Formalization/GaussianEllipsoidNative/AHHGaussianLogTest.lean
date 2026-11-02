import GaussianCovarianceRotation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Bounded logarithm and reciprocal compositions for uniformly positive
bounded continuously differentiable tests. -/
noncomputable section
open MeasureTheory
open BMSmoothQuadraticComposition GaussianCovarianceRotation
open scoped BigOperators BoundedContinuousFunction

namespace AHHGaussianLogTest
variable {d : ℕ}

/-- A scalar logarithm bound requiring just an interval bounded away from zero. -/
theorem norm_log_le_of_bounds {a c M : ℝ} (hc : 0 < c)
    (hca : c ≤ a) (haM : a ≤ M) :
    ‖Real.log a‖ ≤ |Real.log c| + |Real.log M| := by
  have hlow := Real.log_le_log hc hca
  have hhigh := Real.log_le_log (hc.trans_le hca) haM
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log c)]

/-- An explicit uniform bound for the logarithm of a positive bounded function. -/
theorem norm_log_le (f : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ f x) (x : Raw d) :
    ‖Real.log (f x)‖ ≤ |Real.log c| + |Real.log (‖f‖ + 1)| := by
  have hlow : Real.log c ≤ Real.log (f x) := Real.log_le_log hc (hcf x)
  have hupper : f x ≤ ‖f‖ + 1 := by
    have hnorm := f.norm_coe_le_norm x
    have habs := le_abs_self (f x)
    rw [Real.norm_eq_abs] at hnorm
    linarith
  have hhigh : Real.log (f x) ≤ Real.log (‖f‖ + 1) :=
    Real.log_le_log (hc.trans_le (hcf x)) hupper
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log c), abs_nonneg (Real.log (‖f‖ + 1))]
  · linarith [le_abs_self (Real.log (‖f‖ + 1)), abs_nonneg (Real.log c)]

/-- The logarithm as a genuine bounded continuous function. -/
def logBounded (f : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ f x) : Raw d →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => Real.log (f x))
    (f.continuous.log (fun x => (hc.trans_le (hcf x)).ne'))
    (|Real.log c| + |Real.log (‖f‖ + 1)|) (norm_log_le f hc hcf)

@[simp] theorem logBounded_apply (f : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ f x) (x : Raw d) :
    logBounded f hc hcf x = Real.log (f x) := rfl

/-- The reciprocal as a genuine bounded continuous function. -/
def reciprocalBounded (f : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ f x) : Raw d →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (f x)⁻¹)
    (f.continuous.inv₀ (fun x => (hc.trans_le (hcf x)).ne')) (1 / c) (by
      intro x
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hc.trans_le (hcf x)))]
      simpa only [one_div] using one_div_le_one_div_of_le hc (hcf x))

@[simp] theorem reciprocalBounded_apply (f : Raw d →ᵇ ℝ) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ f x) (x : Raw d) :
    reciprocalBounded f hc hcf x = (f x)⁻¹ := rfl

/-- The logarithm of a uniformly positive smooth test is again a smooth test. -/
def logTest (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ F.value x) : SmoothTest (Fin d) where
  value := logBounded F.value hc hcf
  gradient i := F.gradient i * reciprocalBounded F.value hc hcf
  hasFDeriv x := by
    have h := (F.hasFDeriv x).log (hc.trans_le (hcf x)).ne'
    convert! h using 1
    ext v
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, BoundedContinuousFunction.mul_apply,
      reciprocalBounded_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

@[simp] theorem logTest_value (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ F.value x) (x : Raw d) :
    (logTest F hc hcf).value x = Real.log (F.value x) := rfl

@[simp] theorem logTest_gradient (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ F.value x) (i : Fin d) (x : Raw d) :
    (logTest F hc hcf).gradient i x = F.gradient i x / F.value x := by
  rfl

/-- Adding a constant preserves the smooth-test gradient. -/
def addConstTest (F : SmoothTest (Fin d)) (a : ℝ) : SmoothTest (Fin d) where
  value := F.value + BoundedContinuousFunction.const (Raw d) a
  gradient := F.gradient
  hasFDeriv x := by
    simpa only [BoundedContinuousFunction.add_apply, BoundedContinuousFunction.const_apply]
      using! (F.hasFDeriv x).add_const a

@[simp] theorem addConstTest_value (F : SmoothTest (Fin d)) (a : ℝ) (x : Raw d) :
    (addConstTest F a).value x = F.value x + a := rfl

@[simp] theorem addConstTest_gradient (F : SmoothTest (Fin d)) (a : ℝ)
    (i : Fin d) (x : Raw d) :
    (addConstTest F a).gradient i x = F.gradient i x := rfl

/-- The test appearing in the derivative of `u * log u`. -/
def logOneTest (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ F.value x) : SmoothTest (Fin d) :=
  addConstTest (logTest F hc hcf) 1

@[simp] theorem logOneTest_value (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ F.value x) (x : Raw d) :
    (logOneTest F hc hcf).value x = Real.log (F.value x) + 1 := rfl

@[simp] theorem logOneTest_gradient (F : SmoothTest (Fin d)) {c : ℝ} (hc : 0 < c)
    (hcf : ∀ x, c ≤ F.value x) (i : Fin d) (x : Raw d) :
    (logOneTest F hc hcf).gradient i x = F.gradient i x / F.value x := rfl

#print axioms norm_log_le_of_bounds
#print axioms norm_log_le
#print axioms logBounded
#print axioms reciprocalBounded
#print axioms logTest
#print axioms addConstTest
#print axioms logOneTest
end AHHGaussianLogTest
