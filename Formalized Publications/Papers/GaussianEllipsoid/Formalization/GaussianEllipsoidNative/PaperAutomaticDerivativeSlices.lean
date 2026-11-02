import PaperUnboundedPotentialStein
import Mathlib.Analysis.Calculus.ContDiff.Comp
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory GaussianTensorMoments BMQuadraticStein BMSmoothQuadraticComposition
open PaperCavityThird PaperMatrixSecondStein PaperUnboundedPotentialStein
open scoped BigOperators BoundedContinuousFunction ContDiff
namespace PaperAutomaticDerivativeSlices
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
abbrev V (κ : Type*) := κ → ℝ

def direction (a : κ) : V κ := Pi.single a 1

theorem direction_norm_le (a : κ) : ‖direction a‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro b
  by_cases h : b = a <;> simp [direction, Pi.single_apply, h, Ne.symm, eq_comm]

/-- Only source hypotheses: C3 regularity and finite bounds on DΦ,D²Φ,D³Φ.
There is deliberately no boundedness assumption on Φ itself. -/
structure BoundedDerivatives (Φ : V κ → ℝ) where
  smooth : ContDiff ℝ 3 Φ
  C1 : ℝ
  C2 : ℝ
  C3 : ℝ
  bound1 : ∀ y, ‖iteratedFDeriv ℝ 1 Φ y‖ ≤ C1
  bound2 : ∀ y, ‖iteratedFDeriv ℝ 2 Φ y‖ ≤ C2
  bound3 : ∀ y, ‖iteratedFDeriv ℝ 3 Φ y‖ ≤ C3

def coordinateSlice (Φ : V κ → ℝ) (n : ℕ) (u : Fin n → κ) : V κ → ℝ :=
  fun y => iteratedFDeriv ℝ n Φ y (fun i => direction (u i))

theorem coordinateSlice_continuous (Φ : V κ → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (u : Fin n → κ) : Continuous (coordinateSlice Φ n u) := by
  have h := (hΦ.iteratedFDeriv_right (i := n) (m := 0) (by simpa using hn)).continuous
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => V κ) ℝ
    (fun i => direction (u i))).continuous.comp h

theorem coordinateSlice_differentiable (Φ : V κ → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (n : ℕ) (hn : (n : ℕ∞ω) + 1 ≤ 3) (u : Fin n → κ) (y : V κ) :
    DifferentiableAt ℝ (coordinateSlice Φ n u) y := by
  have h := (hΦ.iteratedFDeriv_right (i := n) (m := 1) (by simpa [add_comm] using hn)).differentiable (by norm_num)
  exact (h y).continuousMultilinear_apply_const _

theorem fderiv_coordinateSlice_apply (Φ : V κ → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (n : ℕ) (hn : (n : ℕ∞ω) + 1 ≤ 3) (u : Fin n → κ) (y : V κ) (b : κ) :
    (fderiv ℝ (coordinateSlice Φ n u) y) (direction b) =
      coordinateSlice Φ (n+1) (Fin.cons b u) y := by
  have h := (hΦ.iteratedFDeriv_right (i := n) (m := 1) (by simpa [add_comm] using hn)).differentiable (by norm_num)
  unfold coordinateSlice
  rw [fderiv_continuousMultilinear_apply_const_apply (h y)]
  simp only [iteratedFDeriv_succ_apply_left, Fin.cons_zero]
  congr 1

theorem coordinateSlice_norm_le (Φ : V κ → ℝ) (n : ℕ) (u : Fin n → κ)
    {C : ℝ} (hC : ∀ y, ‖iteratedFDeriv ℝ n Φ y‖ ≤ C) (y : V κ) :
    ‖coordinateSlice Φ n u y‖ ≤ C := by
  have h := ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hC y)
    (fun i : Fin n => direction_norm_le (u i))
  simpa only [coordinateSlice, Finset.prod_const_one, mul_one] using h

def boundedSlice (Φ : V κ → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (u : Fin n → κ) (C : ℝ)
    (hC : ∀ y, ‖iteratedFDeriv ℝ n Φ y‖ ≤ C) : V κ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (coordinateSlice Φ n u)
    (coordinateSlice_continuous Φ hΦ n hn u) C (coordinateSlice_norm_le Φ n u hC)

@[simp] theorem boundedSlice_coe (Φ : V κ → ℝ) (hΦ : ContDiff ℝ 3 Φ)
    (n : ℕ) (hn : (n : ℕ∞ω) ≤ 3) (u : Fin n → κ) (C : ℝ)
    (hC : ∀ y, ‖iteratedFDeriv ℝ n Φ y‖ ≤ C) :
    (boundedSlice Φ hΦ n hn u C hC : V κ → ℝ) = coordinateSlice Φ n u := rfl

def oneDirection (a : κ) : Fin 1 → κ := Fin.cons a Fin.elim0
def twoDirections (a b : κ) : Fin 2 → κ := Fin.cons b (oneDirection a)
def threeDirections (a b c : κ) : Fin 3 → κ := Fin.cons c (twoDirections a b)

def gradient {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (a : κ) : V κ →ᵇ ℝ :=
  boundedSlice Φ D.smooth 1 (by norm_num) (oneDirection a) D.C1 D.bound1
def hessian {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (a b : κ) : V κ →ᵇ ℝ :=
  boundedSlice Φ D.smooth 2 (by norm_num) (twoDirections a b) D.C2 D.bound2
def third {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (a b c : κ) : V κ →ᵇ ℝ :=
  boundedSlice Φ D.smooth 3 (by norm_num) (threeDirections a b c) D.C3 D.bound3

/-- Every finite-coordinate linear functional expands in the standard directions. -/
theorem clm_expansion (L : V κ →L[ℝ] ℝ) :
    L = ∑ a, L (direction a) • (ContinuousLinearMap.proj a : V κ →L[ℝ] ℝ) := by
  ext z
  have hz : z = ∑ a, (z a) • direction a := by
    ext b
    simp [direction, Pi.single_apply, Finset.sum_apply, smul_eq_mul]
  conv_lhs => rw [hz]
  simp [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, mul_comm]

def gradientTest {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (a : κ) : SmoothTest κ where
  value := gradient D a
  gradient := hessian D a
  hasFDeriv y := by
    have h := (coordinateSlice_differentiable Φ D.smooth 1 (by norm_num) (oneDirection a) y).hasFDerivAt
    rw [clm_expansion (fderiv ℝ (coordinateSlice Φ 1 (oneDirection a)) y)] at h
    simp_rw [fderiv_coordinateSlice_apply Φ D.smooth 1 (by norm_num)] at h
    simpa only [gradient, hessian, boundedSlice_coe, twoDirections] using! h

def hessianTest {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (a b : κ) : SmoothTest κ where
  value := hessian D a b
  gradient := third D a b
  hasFDeriv y := by
    have h := (coordinateSlice_differentiable Φ D.smooth 2 (by norm_num) (twoDirections a b) y).hasFDerivAt
    rw [clm_expansion (fderiv ℝ (coordinateSlice Φ 2 (twoDirections a b)) y)] at h
    simp_rw [fderiv_coordinateSlice_apply Φ D.smooth 2 (by norm_num)] at h
    simpa only [hessian, third, boundedSlice_coe, threeDirections] using! h

/-- Automatic bounded C2 derivative-slice constructor from the literal C3 and
bounded derivative hypotheses; no derivative identities are supplied as premises. -/
def gradientTest2 {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (a : κ) : SmoothTest2 κ where
  first := gradientTest D a
  gradientTest := hessianTest D a
  gradient_value _ := rfl

theorem potential_hasFDeriv {Φ : V κ → ℝ} (D : BoundedDerivatives Φ) (y : V κ) :
    HasFDerivAt Φ (∑ a, ((gradientTest2 D a).first.value y) •
      (ContinuousLinearMap.proj a : V κ →L[ℝ] ℝ)) y := by
  have h := (D.smooth.differentiable (by norm_num) y).hasFDerivAt
  rw [clm_expansion (fderiv ℝ Φ y)] at h
  have he (a : κ) : (fderiv ℝ Φ y) (direction a) = coordinateSlice Φ 1 (oneDirection a) y := by
    have hh := fderiv_coordinateSlice_apply Φ D.smooth 0 (by norm_num) Fin.elim0 y a
    have hzero : coordinateSlice Φ 0 Fin.elim0 = Φ := by
      funext x
      simp [coordinateSlice,iteratedFDeriv_zero_apply]
    rw [hzero] at hh
    simpa only [coordinateSlice,oneDirection] using hh
  simp_rw [he] at h
  simpa only [gradientTest2, gradientTest, gradient, boundedSlice_coe] using! h

/-- The generic second-chaos gradient identity from actual C3 regularity and
bounded first/second/third derivatives only. In particular affine, unbounded
potentials are admitted. All derivative-slice construction is automatic. -/
theorem automatic_second_stein {d : ℕ} (Φ : V κ → ℝ) (D : BoundedDerivatives Φ)
    (A : κ → Matrix (Fin d) (Fin d) ℝ) (a : κ) :
    (∫ w, MvPolynomial.eval w (centeredQuadratic (A a)) *
      (fderiv ℝ Φ (polynomialFamily (fun b => centeredQuadratic (A b)) w)) (Pi.single a 1)
        ∂gaussianProductLaw (Fin d)) =
      ∑ b, (Matrix.trace (kernelMatrix (A a) (A b)) *
        boundedExpectation (composedGradient (gradientTest2 D a).first (fun c => centeredQuadratic (A c)) b) 1 +
        ∑ c, boundedExpectation
          (composedGradient ((gradientTest2 D a).gradientTest b) (fun e => centeredQuadratic (A e)) c)
          (rawQuadratic (kernelMatrix (kernelMatrix (A a) (A b)) (A c)))) :=
  derivative_slice_second_stein Φ (gradientTest2 D) (potential_hasFDeriv D) A a

#print axioms gradientTest2
#print axioms potential_hasFDeriv
#print axioms automatic_second_stein
end PaperAutomaticDerivativeSlices
