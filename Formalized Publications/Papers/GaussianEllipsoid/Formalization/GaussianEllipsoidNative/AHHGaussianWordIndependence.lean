import AHHGaussianWordPositivity
import Mathlib.Probability.Independence.Integration
import Mathlib.Topology.Algebra.MvPolynomial

/-! Disjoint projector-word traces are independent under the actual finite
product of scalar real Gaussian laws. No independence hypothesis is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace AHH
open GaussianTensorMoments

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

/-- All scalar Gaussian coordinates used by a word, with both real components. -/
def gaussianWordCoordinates (w : List ι) : Finset ((ι × n) × Bool) :=
  Finset.univ.filter (fun k => k.1.1 ∈ w)

@[simp] theorem mem_gaussianWordCoordinates (w : List ι) (k : (ι × n) × Bool) :
    k ∈ gaussianWordCoordinates (n := n) w ↔ k.1.1 ∈ w := by
  simp [gaussianWordCoordinates]

/-- Restore a coordinate block to the ambient space, setting unused entries to zero. -/
def restoreGaussianWordCoordinates (w : List ι)
    (x : gaussianWordCoordinates (n := n) w → ℝ) : ((ι × n) × Bool) → ℝ :=
  fun k => if h : k ∈ gaussianWordCoordinates w then x ⟨k, h⟩ else 0

theorem measurable_restoreGaussianWordCoordinates (w : List ι) :
    Measurable (restoreGaussianWordCoordinates (n := n) w) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases h : k ∈ gaussianWordCoordinates (n := n) w
  · simpa only [restoreGaussianWordCoordinates, dif_pos h] using
      (measurable_pi_apply (⟨k, h⟩ : gaussianWordCoordinates (n := n) w))
  · simpa only [restoreGaussianWordCoordinates, dif_neg h] using
      (measurable_const : Measurable (fun _ : gaussianWordCoordinates (n := n) w → ℝ => (0 : ℝ)))

/-- A word only depends on coordinates whose sample labels occur in that word. -/
theorem gaussianWordMatrix_congr_coordinates (w : List ι)
    (x y : ((ι × n) × Bool) → ℝ)
    (h : ∀ s ∈ w, ∀ i b, x ((s, i), b) = y ((s, i), b)) :
    gaussianWordMatrix x w = gaussianWordMatrix y w := by
  unfold gaussianWordMatrix
  congr 1
  apply List.map_congr_left
  intro s hs
  ext i j
  simp only [gaussianProjector, endpointValue, h s hs]

theorem gaussianWordMatrix_restore_coordinates (w : List ι)
    (x : ((ι × n) × Bool) → ℝ) :
    gaussianWordMatrix (restoreGaussianWordCoordinates w (fun k => x k)) w =
      gaussianWordMatrix x w := by
  apply gaussianWordMatrix_congr_coordinates
  intro s hs i b
  simp [restoreGaussianWordCoordinates, hs]

theorem continuous_gaussianWordTrace (w : List ι) :
    Continuous (fun x : ((ι × n) × Bool) → ℝ => Matrix.trace (gaussianWordMatrix x w)) := by
  simp_rw [← complexEval_gaussianWordTracePolynomial]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi (fun k => Complex.continuous_ofReal.comp (continuous_apply k)))

/-- Exact independence follows from iid scalar coordinates and literal word disjointness. -/
theorem gaussian_wordTrace_indepFun (w v : List ι) (hd : List.Disjoint w v) :
    IndepFun
      (fun x : ((ι × n) × Bool) → ℝ => Matrix.trace (gaussianWordMatrix x w))
      (fun x : ((ι × n) × Bool) → ℝ => Matrix.trace (gaussianWordMatrix x v))
      (gaussianProductLaw ((ι × n) × Bool)) := by
  have hcoords : Disjoint (gaussianWordCoordinates (n := n) w)
      (gaussianWordCoordinates (n := n) v) := by
    apply Finset.disjoint_left.mpr
    intro k hw hv
    exact hd (mem_gaussianWordCoordinates w k |>.mp hw)
      (mem_gaussianWordCoordinates v k |>.mp hv)
  have hind : iIndepFun (fun k (x : ((ι × n) × Bool) → ℝ) => x k)
      (gaussianProductLaw ((ι × n) × Bool)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hblock := hind.indepFun_finset _ _ hcoords (fun k => measurable_pi_apply k)
  have htrace (u : List ι) : Measurable
      (fun x : gaussianWordCoordinates (n := n) u → ℝ =>
        Matrix.trace (gaussianWordMatrix (restoreGaussianWordCoordinates u x) u)) :=
    (continuous_gaussianWordTrace u).measurable.comp
      (measurable_restoreGaussianWordCoordinates u)
  have h := hblock.comp (htrace w) (htrace v)
  simpa only [Function.comp_def, gaussianWordMatrix_restore_coordinates] using h

/-- Disjoint trace moments factor under the actual Gaussian product measure. -/
theorem gaussian_wordTrace_integral_mul_of_disjoint
    (w v : List ι) (hd : List.Disjoint w v) :
    (∫ x : ((ι × n) × Bool) → ℝ,
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v)
      ∂gaussianProductLaw ((ι × n) × Bool)) =
    (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x w)
      ∂gaussianProductLaw ((ι × n) × Bool)) *
    (∫ x : ((ι × n) × Bool) → ℝ, Matrix.trace (gaussianWordMatrix x v)
      ∂gaussianProductLaw ((ι × n) × Bool)) :=
  (gaussian_wordTrace_indepFun w v hd).integral_fun_mul_eq_mul_integral
    (gaussian_integrable_wordTrace w).aestronglyMeasurable
    (gaussian_integrable_wordTrace v).aestronglyMeasurable

end AHH
