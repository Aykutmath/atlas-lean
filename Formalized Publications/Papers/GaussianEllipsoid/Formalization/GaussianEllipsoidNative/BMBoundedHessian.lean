import BMFiniteGibbsHessian
import BMAbsoluteSteinRemainder

open BMFiniteGibbsTest BMSmoothQuadraticComposition
open scoped BoundedContinuousFunction
namespace BMFiniteGibbsHessian
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

noncomputable def boundedProbability (D : Data κ) (a : κ) : (κ → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun y => probability D y a)
    (continuous_iff_continuousAt.mpr (fun y => (hasFDerivAt_probability D a y).continuousAt)) 1
    (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (probability_nonneg D y a)] using
      probability_le_one D y a)

theorem boundedProbability_norm_le_prior (D : Data κ) (a : κ) :
    ‖boundedProbability D a‖ ≤ Real.exp (2*D.beta*‖D.potential‖)*D.weight a := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (Real.exp_nonneg _) (D.weight_nonneg a))).2
  intro y
  change |probability D y a| ≤ _
  rw [abs_of_nonneg (probability_nonneg D y a)]
  exact probability_le_prior D y a

noncomputable def boundedDerivCoordinate (D : Data2 κ) (a : κ) : (κ → ℝ) →ᵇ ℝ :=
  D.potentialDeriv.compContinuous ⟨fun y => y a, continuous_apply a⟩

noncomputable def boundedSecondCoordinate (D : Data2 κ) (a : κ) : (κ → ℝ) →ᵇ ℝ :=
  D.potentialSecond.compContinuous ⟨fun y => y a, continuous_apply a⟩

noncomputable def boundedDiagonal (D : Data2 κ) (a : κ) : (κ → ℝ) →ᵇ ℝ :=
  boundedProbability D.toData a *
    (D.beta^2 • (boundedDerivCoordinate D a)^2 - D.beta • boundedSecondCoordinate D a)

noncomputable def boundedPair (D : Data2 κ) (a b : κ) : (κ → ℝ) →ᵇ ℝ :=
  D.beta^2 • (boundedProbability D.toData a * boundedProbability D.toData b *
    boundedDerivCoordinate D a * boundedDerivCoordinate D b)

noncomputable def boundedHessian (D : Data2 κ) (a b : κ) : (κ → ℝ) →ᵇ ℝ :=
  (if a=b then boundedDiagonal D a else 0) - boundedPair D a b

@[simp] theorem boundedDiagonal_apply (D : Data2 κ) (a : κ) (y : κ → ℝ) :
    boundedDiagonal D a y = probability D.toData y a *
      (D.beta^2*(D.potentialDeriv (y a))^2-D.beta*D.potentialSecond (y a)) := rfl

@[simp] theorem boundedPair_apply (D : Data2 κ) (a b : κ) (y : κ → ℝ) :
    boundedPair D a b y = D.beta^2*probability D.toData y a*probability D.toData y b*
      D.potentialDeriv (y a)*D.potentialDeriv (y b) := by
  change D.beta^2*(probability D.toData y a*probability D.toData y b*
    D.potentialDeriv (y a)*D.potentialDeriv (y b)) = _
  ring

@[simp] theorem boundedHessian_apply (D : Data2 κ) (a b : κ) (y : κ → ℝ) :
    boundedHessian D a b y = hessian D a b y := by
  simp only [boundedHessian, hessian, BoundedContinuousFunction.sub_apply]
  split_ifs <;> simp

/-- Actual bounded-C¹ test for each finite Gibbs gradient coordinate. -/
noncomputable def gradientSmoothTest (D : Data2 κ) (a : κ) : SmoothTest κ where
  value := boundedGradient D.toData a
  gradient b := boundedHessian D a b
  hasFDeriv y := by
    simpa only [boundedHessian_apply] using! hasFDerivAt_gradient D a y

#print axioms boundedProbability_norm_le_prior
#print axioms boundedDiagonal_apply
#print axioms boundedPair_apply
#print axioms boundedHessian_apply
#print axioms gradientSmoothTest
end BMFiniteGibbsHessian
