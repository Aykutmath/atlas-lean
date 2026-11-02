import FourThirdScalarMoments
import FiniteProductMoment
import GaussianQuadraticSpectral
import GaussianRadialMoments

noncomputable section
open MeasureTheory Real GaussianTensorMoments GaussianMixedNormHelpers BMQuadraticSpectral
open scoped BigOperators ENNReal
open BMUniformMoment
namespace BMFourThirdMoment

/-- Genuine symmetric Gaussian quadratic measurements have the finite factorial
moment bound needed for a sample-size-order Markov argument. -/
theorem normalizedQuadratic_fractional_factorial_moment {d : ℕ} (hd : 0 < d)
    (T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d)
    (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1)
    (A : ℝ) (hA : 1 ≤ A) (k : ℕ) (hk : (k:ℝ) ≤ A*(d:ℝ)^2) :
    Integrable (fun x => (|normalizedQuadratic T x|^((4:ℝ)/3))^k)
      (euclideanGaussianLaw (Fin d)) ∧
    (∫ x, (|normalizedQuadratic T x|^((4:ℝ)/3))^k ∂euclideanGaussianLaw (Fin d)) ≤
      (k.factorial : ℝ)*(2*exp 1*(32+2304*A))^k := by
  have h := centeredDiagonal_fractional_factorial_moment (eigenWeight hT) (d:ℝ) A
    (by exact_mod_cast hd) hA (eigenWeight_abs_le hT hN) (sum_eigenWeight_sq_le hd hT hN) k hk
  have hl := (normalizedQuadratic_identDistrib hT).comp (u := fun z : ℝ => (|z|^((4:ℝ)/3))^k) (by fun_prop)
  refine ⟨hl.integrable_iff.mpr h.1, ?_⟩
  rw [integral_normalizedQuadratic_eq hT (fun z => (|z|^((4:ℝ)/3))^k)]
  exact h.2

/-- Actual iid samples: a fixed operator has exponentially small failure at a
constant fractional empirical-moment threshold. -/
theorem normalizedQuadratic_empirical_tail {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : BMQuadraticSpectral.Euclid d →L[ℝ] BMQuadraticSpectral.Euclid d)
    (hT : T.toLinearMap.IsSymmetric) (hN : ‖T‖ ≤ 1)
    (A t : ℝ) (hA : 1 ≤ A) (ht : 0 < t) (hwindow : (n:ℝ) ≤ A*(d:ℝ)^2) :
    (Measure.pi (fun _ : Fin n => euclideanGaussianLaw (Fin d))).real
      {x | t*n < ∑ i, |normalizedQuadratic T (x i)|^((4:ℝ)/3)} ≤
        (8*exp 1*(32+2304*A)/t)^n := by
  have hI (i : Fin n) (k : ℕ) (hk : k ≤ n) :=
    (normalizedQuadratic_fractional_factorial_moment hd T hT hN A hA k
      ((by exact_mod_cast hk : (k:ℝ)≤n).trans hwindow)).1
  have hM (i : Fin n) (k : ℕ) (hk : k ≤ n) :=
    (normalizedQuadratic_fractional_factorial_moment hd T hT hN A hA k
      ((by exact_mod_cast hk : (k:ℝ)≤n).trans hwindow)).2
  convert independent_sum_tail_le (euclideanGaussianLaw (Fin d)) n hn
    (fun _ x => |normalizedQuadratic T x|^((4:ℝ)/3)) (2*exp 1*(32+2304*A)) t
    (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) (by positivity) ht hI hM using 1 <;> congr 1 <;> ring

#print axioms normalizedQuadratic_fractional_factorial_moment
#print axioms normalizedQuadratic_empirical_tail
end BMFourThirdMoment
