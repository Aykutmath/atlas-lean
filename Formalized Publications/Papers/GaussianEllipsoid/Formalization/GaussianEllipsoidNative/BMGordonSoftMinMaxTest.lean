import BMGordonSoftMinMaxHessian
import BMGordonAffineInterpolation

noncomputable section
open scoped BigOperators BoundedContinuousFunction

namespace BMGordonSoftMinMax
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]

lemma continuous_innerWeight (β : ℝ) (a : I × J) :
    Continuous (fun x => innerWeight β x a) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_innerWeight β x a).continuousAt

lemma continuous_gradient (β : ℝ) (a : I × J) :
    Continuous (fun x => gradient β x a) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_gradient β x a).continuousAt

lemma continuous_hessian (β : ℝ) (a b : I × J) :
    Continuous (fun x => hessian β x a b) := by
  have hg (c : I × J) := continuous_gradient β c
  have hq (c : I × J) := continuous_innerWeight β c
  unfold hessian
  split_ifs <;> fun_prop

lemma continuous_softMinMax (β : ℝ) (hβ : β ≠ 0) :
    Continuous (softMinMax β : (I × J → ℝ) → ℝ) :=
  continuous_iff_continuousAt.mpr fun x => (hasFDerivAt_softMinMax β hβ x).continuousAt

def gradientBCF (β : ℝ) (a : I × J) : (I × J → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => gradient β x a)
    (continuous_gradient β a) 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (gradient_pos β x a)]
      exact gradient_le_one β x a)

def hessianBCF (β : ℝ) (a b : I × J) : (I × J → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => hessian β x a b)
    (continuous_hessian β a b) (4 * |β|) (fun x => by
      rw [Real.norm_eq_abs]
      exact abs_hessian_le β x a b)

/-- Each coordinate of the gradient is a genuine bounded C¹ test. -/
def gradientTest (β : ℝ) (a : I × J) :
    BMSmoothQuadraticComposition.SmoothTest (I × J) where
  value := gradientBCF β a
  gradient := hessianBCF β a
  hasFDeriv x := hasFDerivAt_gradient_hessian β x a

/-- The actual nested log-sum-exp, packaged for the Gaussian interpolation theorem. -/
def softMinMaxTest (β : ℝ) (hβ : β ≠ 0) : BMGordonAffineInterpolation.C2Test (I × J) where
  value := ⟨softMinMax β, continuous_softMinMax β hβ⟩
  gradient := gradientTest β
  hasFDeriv x := hasFDerivAt_softMinMax β hβ x

@[simp] theorem softMinMaxTest_value (β : ℝ) (hβ : β ≠ 0) (x : I × J → ℝ) :
    (softMinMaxTest β hβ).value x = softMinMax β x := rfl

@[simp] theorem softMinMaxTest_gradient_value (β : ℝ) (hβ : β ≠ 0)
    (a : I × J) (x : I × J → ℝ) :
    ((softMinMaxTest β hβ).gradient a).value x = gradient β x a := rfl

@[simp] theorem softMinMaxTest_hessian_value (β : ℝ) (hβ : β ≠ 0)
    (a b : I × J) (x : I × J → ℝ) :
    (((softMinMaxTest β hβ).gradient a).gradient b) x = hessian β x a b := rfl

#print axioms softMinMaxTest
#print axioms hasFDerivAt_gradient_hessian
#print axioms hessian_nonneg_of_row_ne
#print axioms abs_hessian_le

end BMGordonSoftMinMax
