import AHHNormalizedWordGluing
import AHHGaussianWordExpansion
import AHHGaussianTail
import AHHComplexExpectation
import AHHWordRecurrence

/-! Exact tensor moments for the manuscript's normalized covariance under its
actual four-real Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHH

theorem wordSum_eq_sum_ofFn {α : Type*} [Fintype α] (T : List α → ℝ) (k : ℕ) :
    wordSum T k = ∑ w : Fin k → α, T (List.ofFn w) := by
  classical
  unfold wordSum words
  exact Finset.sum_image (fun a _ b _ hab => List.ofFn_injective hab)

end AHH

namespace AHHGaussian
set_option backward.isDefEq.respectTransparency false

/-- The normalized two-factor projector on the actual sample space. -/
def normalizedTensorProjector (n h : ℕ) (x : FourEntries n h) (s : Fin n) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℂ :=
  Matrix.kroneckerMap (· * ·) (normalizedProjector n h x.1 s)
    (normalizedProjector n h x.2 s)

def normalizedTensorWordMatrix (n h : ℕ) (x : FourEntries n h) (w : List (Fin n)) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℂ :=
  (w.map (normalizedTensorProjector n h x)).prod

theorem normalizedTensorProjector_eq_actual (n h : ℕ) (x : FourEntries n h)
    (s : Fin n) :
    normalizedTensorProjector n h x s =
      AHHAlgebraBridges.projector (fun p => actualProductStates n h true true x s p) := by
  ext i j
  change (normalizedFactor n h true x.1 s i.1 * star (normalizedFactor n h true x.1 s j.1)) *
      (normalizedFactor n h true x.2 s i.2 * star (normalizedFactor n h true x.2 s j.2)) =
    (normalizedFactor n h true x.1 s i.1 * normalizedFactor n h true x.2 s i.2) *
      star (normalizedFactor n h true x.1 s j.1 * normalizedFactor n h true x.2 s j.2)
  rw [star_mul]
  ring

theorem actualComplexCovariance_eq_normalizedTensorSum (n h : ℕ) (x : FourEntries n h) :
    actualComplexCovariance n h true true x = ∑ s, normalizedTensorProjector n h x s := by
  rw [actualComplexCovariance_eq_sum_projectors]
  simp_rw [normalizedTensorProjector_eq_actual]

theorem normalizedTensorWordMatrix_eq (n h : ℕ) (x : FourEntries n h)
    (w : List (Fin n)) :
    normalizedTensorWordMatrix n h x w =
      Matrix.kroneckerMap (· * ·) (normalizedWordMatrix n h x.1 w)
        (normalizedWordMatrix n h x.2 w) := by
  induction w with
  | nil => simp [normalizedTensorWordMatrix, normalizedWordMatrix, Matrix.one_kronecker_one]
  | cons s w ih =>
    simp only [normalizedTensorWordMatrix, normalizedWordMatrix, List.map_cons, List.prod_cons] at *
    rw [ih, normalizedTensorProjector, ← Matrix.mul_kronecker_mul]

theorem normalizedTensorWordTrace_eq (n h : ℕ) (x : FourEntries n h)
    (w : List (Fin n)) :
    Matrix.trace (normalizedTensorWordMatrix n h x w) =
      Matrix.trace (normalizedWordMatrix n h x.1 w) *
        Matrix.trace (normalizedWordMatrix n h x.2 w) := by
  rw [normalizedTensorWordMatrix_eq, Matrix.trace_kronecker]

theorem normalizedTensorWordTrace_integrable (n h : ℕ) (w : List (Fin n)) :
    Integrable (fun x => Matrix.trace (normalizedTensorWordMatrix n h x w))
      (fourGaussianLaw n h) := by
  simp_rw [normalizedTensorWordTrace_eq]
  exact (normalizedWordTrace_integrable n h w).mul_prod (normalizedWordTrace_integrable n h w)

theorem normalizedTensorWordTrace_integral (n h : ℕ) (w : List (Fin n)) :
    (∫ x, Matrix.trace (normalizedTensorWordMatrix n h x w) ∂fourGaussianLaw n h) =
      (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h) ^ 2 := by
  simp_rw [normalizedTensorWordTrace_eq]
  rw [fourGaussianLaw, pow_two]
  exact integral_prod_mul (L := ℂ)
    (fun x : PairEntries n h => Matrix.trace (normalizedWordMatrix n h x w))
    (fun x : PairEntries n h => Matrix.trace (normalizedWordMatrix n h x w))

theorem actualComplexCovariance_pow_expansion (n h m : ℕ) (x : FourEntries n h) :
    actualComplexCovariance n h true true x ^ m =
      ∑ w : Fin m → Fin n, normalizedTensorWordMatrix n h x (List.ofFn w) := by
  rw [actualComplexCovariance_eq_normalizedTensorSum]
  exact AHH.sum_pow_eq_sum_wordProducts (normalizedTensorProjector n h x) m

theorem actualComplexCovariance_trace_pow_integrable (n h m : ℕ) :
    Integrable (fun x => Matrix.trace (actualComplexCovariance n h true true x ^ m))
      (fourGaussianLaw n h) := by
  simp_rw [actualComplexCovariance_pow_expansion, Matrix.trace_sum]
  exact integrable_finsetSum _ (fun w _ => normalizedTensorWordTrace_integrable n h (List.ofFn w))

/-- The actual normalized tensor trace moment is precisely the complete finite
sum of squares of actual one-factor normalized word means. -/
theorem actualComplexCovariance_trace_moment_eq_wordSum (n h m : ℕ) :
    (∫ x, (Matrix.trace (actualComplexCovariance n h true true x ^ m)).re
      ∂fourGaussianLaw n h) =
      AHH.wordSum (fun w : List (Fin n) => normalizedWordMean n h w ^ 2) m := by
  classical
  have hc : (∫ x, Matrix.trace (actualComplexCovariance n h true true x ^ m)
      ∂fourGaussianLaw n h) =
      ∑ w : Fin m → Fin n,
        (∫ x, Matrix.trace (normalizedWordMatrix n h x (List.ofFn w))
          ∂pairGaussianLaw n h) ^ 2 := by
    simp_rw [actualComplexCovariance_pow_expansion, Matrix.trace_sum]
    rw [integral_finsetSum _ (fun w _ => normalizedTensorWordTrace_integrable n h (List.ofFn w))]
    simp_rw [normalizedTensorWordTrace_integral]
  rw [← RCLike.re_eq_complex_re,
    integral_re (actualComplexCovariance_trace_pow_integrable n h m), hc]
  simp only [RCLike.re_eq_complex_re, Complex.re_sum, pow_two, Complex.mul_re,
    normalizedWordTrace_integral_im_zero, mul_zero, sub_zero]
  unfold normalizedWordMean
  exact (AHH.wordSum_eq_sum_ofFn
    (fun w : List (Fin n) =>
      (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h).re *
      (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h).re) m).symm

theorem actualComplexCovariance_posSemidef (n h : ℕ) (s t : Bool)
    (x : FourEntries n h) : (actualComplexCovariance n h s t x).PosSemidef :=
  AHHAlgebraBridges.complexCov_posSemidef _ _ _ _ _ _ _ _

theorem actualComplexCovariance_continuous (n h : ℕ) (s t : Bool) :
    Continuous (actualComplexCovariance n h s t) := by
  unfold actualComplexCovariance AHHAlgebraBridges.complexCov
  apply continuous_finset_sum
  intro i hi
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [AHHAlgebraBridges.projector, AHHAlgebraBridges.productState,
    AHHAlgebraBridges.pureTensor, AHHAlgebraBridges.complexFactor]
  fun_prop

/-- Exact PSD/Jensen power estimate, with all measurability and integrability
facts discharged for the actual normalized Gaussian ensemble. -/
theorem actualComplexCovariance_expectation_pow_le_wordSum (n h m : ℕ)
    (hh : 1 ≤ h) (hm : 1 ≤ m) :
    (∫ x, ‖AHHAlgebraBridges.cMatrixCLM (actualComplexCovariance n h true true x)‖
      ∂fourGaussianLaw n h) ^ m ≤
      AHH.wordSum (fun w : List (Fin n) => normalizedWordMean n h w ^ 2) m := by
  letI : NeZero h := ⟨by omega⟩
  have he := AHHAlgebraBridges.complex_expectation_pow_le_trace_moment
    (actualComplexCovariance n h true true)
    (actualComplexCovariance_continuous n h true true).aestronglyMeasurable
    (actualComplexCovariance_posSemidef n h true true) m hm
    (actualComplexCovariance_trace_pow_integrable n h m).re
  exact he.2.trans_eq (actualComplexCovariance_trace_moment_eq_wordSum n h m)

#print axioms actualComplexCovariance_trace_moment_eq_wordSum
#print axioms actualComplexCovariance_expectation_pow_le_wordSum
end AHHGaussian
