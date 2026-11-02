/-
Kernel-checked standard Gaussian integrals, via derivatives of its known MGF.
These are scalar and marginal ingredients, not the complete quadratic-form
covariance or Hanson-Wright statements in the manuscript.
-/
import GaussianEllipsoid.GaussianProbability
import GaussianEllipsoid.Coordinates
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory

namespace GaussianMoments

def standardMGF (t : Real) : Real := Real.exp (t ^ 2 / 2)

theorem hasDerivAt_standardMGF (t : Real) :
    HasDerivAt standardMGF (t * standardMGF t) t := by
  show HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2)) (t * Real.exp (t ^ 2 / 2)) t
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) t t := by
    have h := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
    have hval : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by
      simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
      ring
    rw [hval] at h
    exact h
  have h := h2.exp
  change HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2))
    (Real.exp (t ^ 2 / 2) * t) t at h
  have hval : Real.exp (t ^ 2 / 2) * t = t * Real.exp (t ^ 2 / 2) := by ring
  rw [hval] at h
  exact h

theorem deriv_standardMGF :
    deriv standardMGF = fun t => t * standardMGF t := by
  funext t
  exact (hasDerivAt_standardMGF t).deriv

theorem hasDerivAt_first (t : Real) :
    HasDerivAt (fun s => s * standardMGF s)
      ((t ^ 2 + 1) * standardMGF t) t := by
  have h := (hasDerivAt_id' t).mul (hasDerivAt_standardMGF t)
  change HasDerivAt ((fun x : ℝ => x) * standardMGF)
    (1 * standardMGF t + t * (t * standardMGF t)) t at h
  have hval : 1 * standardMGF t + t * (t * standardMGF t)
      = (t ^ 2 + 1) * standardMGF t := by ring
  rw [hval] at h
  exact h

theorem deriv_first :
    deriv (fun t => t * standardMGF t) =
      fun t => (t ^ 2 + 1) * standardMGF t := by
  funext t
  exact (hasDerivAt_first t).deriv

theorem hasDerivAt_second (t : Real) :
    HasDerivAt (fun s => (s ^ 2 + 1) * standardMGF s)
      ((t ^ 3 + 3 * t) * standardMGF t) t := by
  have h := ((hasDerivAt_pow 2 t).add_const 1).mul
    (hasDerivAt_standardMGF t)
  change HasDerivAt ((fun x : ℝ => x ^ 2 + 1) * standardMGF)
    ((((2 : ℕ) : ℝ) * t ^ (2 - 1)) * standardMGF t
      + (t ^ 2 + 1) * (t * standardMGF t)) t at h
  have hval : ((((2 : ℕ) : ℝ) * t ^ (2 - 1)) * standardMGF t
      + (t ^ 2 + 1) * (t * standardMGF t))
      = (t ^ 3 + 3 * t) * standardMGF t := by
    simp only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    ring
  rw [hval] at h
  exact h

theorem deriv_second :
    deriv (fun t => (t ^ 2 + 1) * standardMGF t) =
      fun t => (t ^ 3 + 3 * t) * standardMGF t := by
  funext t
  exact (hasDerivAt_second t).deriv

theorem hasDerivAt_third (t : Real) :
    HasDerivAt (fun s => (s ^ 3 + 3 * s) * standardMGF s)
      ((t ^ 4 + 6 * t ^ 2 + 3) * standardMGF t) t := by
  have h := ((hasDerivAt_pow 3 t).add
    ((hasDerivAt_id' t).const_mul 3)).mul (hasDerivAt_standardMGF t)
  change HasDerivAt ((fun x : ℝ => x ^ 3 + 3 * x) * standardMGF)
    (((((3 : ℕ) : ℝ) * t ^ (3 - 1)) + 3 * 1) * standardMGF t
      + (t ^ 3 + 3 * t) * (t * standardMGF t)) t at h
  have hval : (((((3 : ℕ) : ℝ) * t ^ (3 - 1)) + 3 * 1) * standardMGF t
      + (t ^ 3 + 3 * t) * (t * standardMGF t))
      = (t ^ 4 + 6 * t ^ 2 + 3) * standardMGF t := by
    simp only [Nat.reduceSub, Nat.cast_ofNat, mul_one]
    ring
  rw [hval] at h
  exact h

theorem deriv_third :
    deriv (fun t => (t ^ 3 + 3 * t) * standardMGF t) =
      fun t => (t ^ 4 + 6 * t ^ 2 + 3) * standardMGF t := by
  funext t
  exact (hasDerivAt_third t).deriv

/-- The MGF-to-moment identity is applied to the actual Gaussian measure. -/
theorem standard_integral_pow_eq_deriv (k : Nat) :
    integral (gaussianReal 0 1) (fun x : Real => x ^ k) =
      iteratedDeriv k standardMGF 0 := by
  show integral (gaussianReal 0 1) (fun x : Real => x ^ k) =
    iteratedDeriv k (fun t : Real => Real.exp (t ^ 2 / 2)) 0
  have h : iteratedDeriv k (mgf (fun x : Real => x) (gaussianReal 0 1)) 0 =
      integral (gaussianReal 0 1) (fun x : Real => x ^ k) :=
    iteratedDeriv_mgf_zero (by simp) k
  rw [mgf_fun_id_gaussianReal] at h
  simpa using h.symm

theorem standard_integrable_pow (k : Nat) :
    Integrable (fun x : Real => x ^ k) (gaussianReal 0 1) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : Real => x) (by simp) k

theorem standard_first_moment :
    integral (gaussianReal 0 1) (fun x : Real => x) = 0 := by
  simp

theorem standard_second_moment :
    integral (gaussianReal 0 1) (fun x : Real => x ^ 2) = 1 := by
  rw [standard_integral_pow_eq_deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_standardMGF, deriv_first]
  norm_num [standardMGF, Real.exp_zero]

theorem standard_third_moment :
    integral (gaussianReal 0 1) (fun x : Real => x ^ 3) = 0 := by
  rw [standard_integral_pow_eq_deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_standardMGF, deriv_first, deriv_second]
  norm_num [standardMGF, Real.exp_zero]

theorem standard_fourth_moment :
    integral (gaussianReal 0 1) (fun x : Real => x ^ 4) = 3 := by
  rw [standard_integral_pow_eq_deriv]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero,
    deriv_standardMGF, deriv_first, deriv_second, deriv_third]
  norm_num [standardMGF, Real.exp_zero]

theorem standard_centered_square_mean :
    integral (gaussianReal 0 1) (fun x : Real => x ^ 2 - 1) = 0 := by
  rw [integral_sub (standard_integrable_pow 2) (integrable_const 1)]
  simp [standard_second_moment]

theorem standard_centered_square_second_moment :
    integral (gaussianReal 0 1) (fun x : Real => (x ^ 2 - 1) ^ 2) = 2 := by
  have h4 : Integrable (fun x : Real => x ^ 4) (gaussianReal 0 1) :=
    standard_integrable_pow 4
  have h2 : Integrable (fun x : Real => x ^ 2) (gaussianReal 0 1) :=
    standard_integrable_pow 2
  have h2c : Integrable (fun x : Real => 2 * x ^ 2) (gaussianReal 0 1) :=
    h2.const_mul 2
  have hsub : Integrable (fun x : Real => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) :=
    h4.sub h2c
  have h1 : Integrable (fun _ : Real => (1 : Real)) (gaussianReal 0 1) :=
    integrable_const 1
  have hconst : integral (gaussianReal 0 1) (fun _ : Real => (1 : Real)) = 1 := by
    simp
  have heq : (fun x : Real => (x ^ 2 - 1) ^ 2) =
      (fun x : Real => x ^ 4 - 2 * x ^ 2 + 1) := by
    funext x
    ring
  have hfinal : (3 : ℝ) - 2 * 1 + 1 = 2 := by norm_num
  rw [heq, integral_add hsub h1, integral_sub h4 h2c, integral_const_mul,
    standard_fourth_moment, standard_second_moment, hconst, hfinal]

theorem coordinate_integrable_pow {d : Nat} (j : Fin d) (k : Nat) :
    Integrable (fun x : Vector d => (x j) ^ k) (gaussianVectorLaw d) := by
  exact (gaussianCoordinate_measurePreserving j).integrable_comp_of_integrable
    (standard_integrable_pow k)

theorem coordinate_first_moment {d : Nat} (j : Fin d) :
    integral (gaussianVectorLaw d) (fun x => x j) = 0 := by
  have h := integral_gaussianCoordinate j (fun x : ℝ => x) (by fun_prop)
  rw [standard_first_moment] at h
  simpa using h

theorem coordinate_second_moment {d : Nat} (j : Fin d) :
    integral (gaussianVectorLaw d) (fun x => (x j) ^ 2) = 1 := by
  rw [integral_gaussianCoordinate j (fun x => x ^ 2) (by fun_prop)]
  exact standard_second_moment

theorem coordinate_fourth_moment {d : Nat} (j : Fin d) :
    integral (gaussianVectorLaw d) (fun x => (x j) ^ 4) = 3 := by
  rw [integral_gaussianCoordinate j (fun x => x ^ 4) (by fun_prop)]
  exact standard_fourth_moment

/-- This is a finite sum of squares, independently of the default Pi sup norm. -/
theorem squared_euclidean_length_mean (d : Nat) :
    integral (gaussianVectorLaw d)
      (fun x => Finset.univ.sum (fun j : Fin d => (x j) ^ 2)) = (d : Real) := by
  rw [integral_finsetSum Finset.univ
    (fun j _ => coordinate_integrable_pow j 2)]
  simp [coordinate_second_moment]

theorem sample_coordinate_second_moment {d n : Nat} (i : Fin n) (j : Fin d) :
    integral (gaussianSampleLaw d n) (fun x => (x i j) ^ 2) = 1 := by
  rw [integral_gaussianRow i (fun x => (x j) ^ 2) (by fun_prop)]
  exact coordinate_second_moment j

theorem coordinate_product_integrable {d : Nat} (i j : Fin d) :
    Integrable (fun x : Vector d => x i * x j) (gaussianVectorLaw d) := by
  by_cases hij : i = j
  case pos =>
    subst j
    simpa [pow_two] using coordinate_integrable_pow i 2
  case neg =>
    have hi : Integrable (fun x : Vector d => x i) (gaussianVectorLaw d) := by
      simpa using coordinate_integrable_pow i 1
    have hj : Integrable (fun x : Vector d => x j) (gaussianVectorLaw d) := by
      simpa using coordinate_integrable_pow j 1
    exact ((gaussianCoordinates_independent d).indepFun hij).integrable_mul hi hj

/-- The actual coordinate covariance matrix is the identity. -/
theorem coordinate_product_mean {d : Nat} (i j : Fin d) :
    integral (gaussianVectorLaw d) (fun x => x i * x j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  case pos =>
    subst j
    simpa [pow_two] using coordinate_second_moment i
  case neg =>
    have h := ((gaussianCoordinates_independent d).indepFun hij).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
    simpa [hij, coordinate_first_moment] using h

theorem quadratic_eq_doubleSum {d : Nat} (S : Square d) (x : Vector d) :
    quadratic S x = Finset.univ.sum (fun i : Fin d =>
      Finset.univ.sum (fun j : Fin d => S i j * (x i * x j))) := by
  rw [quadratic_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadratic_integrable {d : Nat} (S : Square d) :
    Integrable (quadratic S) (gaussianVectorLaw d) := by
  change Integrable (fun x => quadratic S x) (gaussianVectorLaw d)
  simp_rw [quadratic_eq_doubleSum]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (coordinate_product_integrable i j).const_mul (S i j)))

/-- No symmetry is needed for the expectation of a quadratic form. -/
theorem quadratic_mean {d : Nat} (S : Square d) :
    integral (gaussianVectorLaw d) (quadratic S) = Matrix.trace S := by
  have heq : quadratic S = fun x => Finset.univ.sum (fun i : Fin d =>
      Finset.univ.sum (fun j : Fin d => S i j * (x i * x j))) := by
    funext x
    exact quadratic_eq_doubleSum S x
  rw [heq, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ =>
      (coordinate_product_integrable i j).const_mul (S i j)))]
  calc
    _ = Finset.univ.sum (fun i : Fin d => Finset.univ.sum (fun j : Fin d =>
        integral (gaussianVectorLaw d) (fun x => S i j * (x i * x j)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum Finset.univ (fun j _ =>
        (coordinate_product_integrable i j).const_mul (S i j))
    _ = Matrix.trace S := by
      simp [integral_const_mul, coordinate_product_mean, Matrix.trace]

theorem centered_quadratic_mean {d : Nat} (S : Square d) :
    integral (gaussianVectorLaw d)
      (fun x => quadratic S x - Matrix.trace S) = 0 := by
  rw [integral_sub (quadratic_integrable S) (integrable_const _)]
  simp [quadratic_mean]

end GaussianMoments
end GaussianEllipsoid
