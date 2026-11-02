import PaperSmoothCutoff
import PaperGibbsThird
import GaussianEllipsoid.Gibbs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.ContinuousMap.CompactlySupported
noncomputable section
open scoped BigOperators BoundedContinuousFunction CompactlySupported ContDiff
open PaperSmoothCutoff PaperGibbsThird GaussianEllipsoid.FiniteGibbs
namespace PaperSmoothCutoffData3

def residual (a : ℝ) : ℝ → ℝ := fun t => loss a t - 1

theorem residual_contDiff (a : ℝ) : ContDiff ℝ ∞ (residual a) :=
  (loss_contDiff a).sub contDiff_const

/-- The actual paper cutoff minus one is zero outside [-a,a]. -/
theorem residual_hasCompactSupport {a : ℝ} (ha : 0 < a) : HasCompactSupport (residual a) := by
  apply HasCompactSupport.intro (K := Set.Icc (-a) a) isCompact_Icc
  intro t ht
  have hta : a ≤ |t| := by
    by_contra h
    have hh : |t| < a := lt_of_not_ge h
    exact ht ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩
  simp [residual, loss_one ha hta]

def rawDerivative (a : ℝ) (n : ℕ) : ℝ → ℝ := deriv^[n] (residual a)

theorem rawDerivative_contDiff (a : ℝ) (n : ℕ) : ContDiff ℝ ∞ (rawDerivative a n) :=
  ContDiff.iterate_deriv n (residual_contDiff a)

theorem rawDerivative_hasCompactSupport {a : ℝ} (ha : 0 < a) (n : ℕ) :
    HasCompactSupport (rawDerivative a n) := by
  induction n with
  | zero => simpa [rawDerivative] using residual_hasCompactSupport ha
  | succ n ih =>
    simpa only [rawDerivative, Function.iterate_succ_apply'] using ih.deriv

theorem hasDerivAt_rawDerivative (a : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (rawDerivative a n) (rawDerivative a (n+1) t) t := by
  have h := ((rawDerivative_contDiff a n).differentiable (by simp) t).hasDerivAt
  simpa only [rawDerivative, Function.iterate_succ_apply'] using! h

def compactDerivative (a : ℝ) (ha : 0 < a) (n : ℕ) : C_c(ℝ, ℝ) where
  toFun := rawDerivative a n
  continuous_toFun := (rawDerivative_contDiff a n).continuous
  hasCompactSupport' := rawDerivative_hasCompactSupport ha n

def boundedDerivative (a : ℝ) (ha : 0 < a) (n : ℕ) : ℝ →ᵇ ℝ :=
  (compactDerivative a ha n).toBoundedContinuousFunction

@[simp] theorem boundedDerivative_apply (a : ℝ) (ha : 0 < a) (n : ℕ) (t : ℝ) :
    boundedDerivative a ha n t = rawDerivative a n t := rfl

@[simp] theorem boundedDerivative_coe (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (boundedDerivative a ha n : ℝ → ℝ) = rawDerivative a n := rfl

/-- The original chi(t²/a²) loss, with no replacement by another smoothing. -/
def boundedLoss (a : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (loss a) (loss_C3 a).continuous 1
    (fun t => by simpa only [Real.norm_eq_abs, abs_of_nonneg (loss_nonneg a t)] using loss_le_one a t)

@[simp] theorem boundedLoss_apply (a t : ℝ) : boundedLoss a t = loss a t := rfl

theorem rawDerivative_one (a : ℝ) : rawDerivative a 1 = deriv (loss a) := by
  change deriv (fun t : ℝ => loss a t - 1) = deriv (loss a)
  exact deriv_sub_const_fun 1
theorem rawDerivative_two (a : ℝ) : rawDerivative a 2 = deriv (deriv (loss a)) := by
  change deriv (deriv (fun t : ℝ => loss a t - 1)) = deriv (deriv (loss a))
  rw [deriv_sub_const_fun]
theorem rawDerivative_three (a : ℝ) : rawDerivative a 3 = deriv (deriv (deriv (loss a))) := by
  change deriv (deriv (deriv (fun t : ℝ => loss a t - 1))) = deriv (deriv (deriv (loss a)))
  rw [deriv_sub_const_fun]

/-- Construct actual finite-prior C³ Gibbs data from the paper's cutoff. Every
boundedness and derivative field is proved from smoothness and compact support. -/
def data3 {κ : Type*} [Fintype κ] (ν : Law κ) (β : ℝ) (hβ : 0 ≤ β)
    (a : ℝ) (ha : 0 < a) : Data3 κ where
  weight := ν.weight
  weight_nonneg := ν.nonneg
  weight_sum := ν.total
  potential := boundedLoss a
  potentialDeriv := boundedDerivative a ha 1
  hasDeriv t := by
    change HasDerivAt (loss a) (rawDerivative a 1 t) t
    rw [rawDerivative_one]
    exact ((loss_C3 a).differentiable (by norm_num) t).hasDerivAt
  beta := β
  beta_nonneg := hβ
  potentialSecond := boundedDerivative a ha 2
  hasDeriv_second t := by
    simpa only [boundedDerivative_coe, boundedDerivative_apply] using! hasDerivAt_rawDerivative a 1 t
  potentialThird := boundedDerivative a ha 3
  hasDeriv_third t := by
    simpa only [boundedDerivative_coe, boundedDerivative_apply] using! hasDerivAt_rawDerivative a 2 t

@[simp] theorem data3_potential {κ : Type*} [Fintype κ] (ν : Law κ) (β : ℝ) (hβ : 0 ≤ β)
    (a : ℝ) (ha : 0 < a) (t : ℝ) : (data3 ν β hβ a ha).potential t = loss a t := rfl

theorem data3_unit {κ : Type*} [Fintype κ] (ν : Law κ) (β : ℝ) (hβ : 0 ≤ β)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    0 ≤ (data3 ν β hβ a ha).potential t ∧ (data3 ν β hβ a ha).potential t ≤ 1 :=
  ⟨loss_nonneg a t, loss_le_one a t⟩

/-- Finite real sup-norm bounds for all three literal cutoff derivatives. -/
theorem finite_derivative_bounds (a : ℝ) (ha : 0 < a) :
    ∃ L₁ L₂ L₃ : ℝ, 0 ≤ L₁ ∧ 0 ≤ L₂ ∧ 0 ≤ L₃ ∧
      (∀ t, |deriv (loss a) t| ≤ L₁) ∧
      (∀ t, |deriv (deriv (loss a)) t| ≤ L₂) ∧
      (∀ t, |deriv (deriv (deriv (loss a))) t| ≤ L₃) := by
  refine ⟨‖boundedDerivative a ha 1‖, ‖boundedDerivative a ha 2‖, ‖boundedDerivative a ha 3‖,
    norm_nonneg _, norm_nonneg _, norm_nonneg _, ?_, ?_, ?_⟩
  · intro t
    simpa [rawDerivative_one, Real.norm_eq_abs] using (boundedDerivative a ha 1).norm_coe_le_norm t
  · intro t
    simpa [rawDerivative_two, Real.norm_eq_abs] using (boundedDerivative a ha 2).norm_coe_le_norm t
  · intro t
    simpa [rawDerivative_three, Real.norm_eq_abs] using (boundedDerivative a ha 3).norm_coe_le_norm t

#print axioms data3
#print axioms finite_derivative_bounds
end PaperSmoothCutoffData3
