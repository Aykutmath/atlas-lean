import AHHGaussianWordPositivity

/-! The tensor-word moment is the square of the one-factor moment under the
actual product measure. Both Bochner integrability and the Kronecker bridge are
proved, rather than supplied as ensemble hypotheses. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

namespace AHH
open GaussianTensorMoments

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]

abbrev GaussianCoordinates (ι n : Type*) := ((ι × n) × Bool) → ℝ

def gaussianTensorProjector (x y : GaussianCoordinates ι n) (s : ι) :
    Matrix (n × n) (n × n) ℂ :=
  Matrix.kroneckerMap (· * ·) (gaussianProjector x s) (gaussianProjector y s)

/-- The Kronecker projector is literally the outer product of the product
state's coordinates. -/
theorem gaussianTensorProjector_apply (x y : GaussianCoordinates ι n) (s : ι)
    (i j : n × n) :
    gaussianTensorProjector x y s i j =
      (endpointValue ((s, i.1), false) x * endpointValue ((s, i.2), false) y) *
      star (endpointValue ((s, j.1), false) x * endpointValue ((s, j.2), false) y) := by
  obtain ⟨i₁, i₂⟩ := i
  obtain ⟨j₁, j₂⟩ := j
  simp only [gaussianTensorProjector, Matrix.kronecker_apply, gaussianProjector, star_mul]
  ring

def gaussianTensorWordMatrix (x y : GaussianCoordinates ι n) (w : List ι) :
    Matrix (n × n) (n × n) ℂ :=
  (w.map (gaussianTensorProjector x y)).prod

theorem gaussianTensorWordMatrix_eq (x y : GaussianCoordinates ι n) (w : List ι) :
    gaussianTensorWordMatrix x y w = Matrix.kroneckerMap (· * ·) (gaussianWordMatrix x w) (gaussianWordMatrix y w) := by
  induction w with
  | nil => simp [gaussianTensorWordMatrix, gaussianWordMatrix, Matrix.one_kronecker_one]
  | cons s w ih =>
    simp only [gaussianTensorWordMatrix, gaussianWordMatrix, List.map_cons, List.prod_cons] at *
    rw [ih, gaussianTensorProjector, ← Matrix.mul_kronecker_mul]

theorem gaussianTensorWordTrace_eq (x y : GaussianCoordinates ι n) (w : List ι) :
    Matrix.trace (gaussianTensorWordMatrix x y w) =
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix y w) := by
  rw [gaussianTensorWordMatrix_eq, Matrix.trace_kronecker]

def gaussianTensorLaw : Measure (GaussianCoordinates ι n × GaussianCoordinates ι n) :=
  (gaussianProductLaw ((ι × n) × Bool)).prod (gaussianProductLaw ((ι × n) × Bool))

instance gaussianTensorLaw_probability :
    IsProbabilityMeasure (gaussianTensorLaw (ι := ι) (n := n)) := by
  unfold gaussianTensorLaw
  infer_instance

theorem gaussian_integrable_tensorWordTrace (w : List ι) :
    Integrable (fun z : GaussianCoordinates ι n × GaussianCoordinates ι n =>
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w)) gaussianTensorLaw := by
  simp_rw [gaussianTensorWordTrace_eq]
  exact (gaussian_integrable_wordTrace w).mul_prod (gaussian_integrable_wordTrace w)

/-- Exact independence and identical-law factorization, including the empty
word (whose tensor trace is the square of the local dimension). -/
theorem gaussian_tensorWordTrace_integral (w : List ι) :
    (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) ∂gaussianTensorLaw) =
        (∫ x : GaussianCoordinates ι n, Matrix.trace (gaussianWordMatrix x w)
          ∂gaussianProductLaw ((ι × n) × Bool)) ^ 2 := by
  simp_rw [gaussianTensorWordTrace_eq]
  rw [gaussianTensorLaw, pow_two]
  exact integral_prod_mul (L := ℂ)
    (μ := gaussianProductLaw ((ι × n) × Bool))
    (ν := gaussianProductLaw ((ι × n) × Bool))
    (fun x : GaussianCoordinates ι n => Matrix.trace (gaussianWordMatrix x w))
    (fun x : GaussianCoordinates ι n => Matrix.trace (gaussianWordMatrix x w))

theorem gaussian_tensorWordTrace_integral_re (w : List ι) :
    (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) ∂gaussianTensorLaw).re =
        (∫ x : GaussianCoordinates ι n, Matrix.trace (gaussianWordMatrix x w)
          ∂gaussianProductLaw ((ι × n) × Bool)).re ^ 2 := by
  rw [gaussian_tensorWordTrace_integral, pow_two, Complex.mul_re,
    gaussian_wordTrace_integral_im_zero]
  ring

theorem gaussian_tensorWordTrace_integral_re_nonneg (w : List ι) :
    0 ≤ (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) ∂gaussianTensorLaw).re := by
  rw [gaussian_tensorWordTrace_integral_re]
  exact sq_nonneg _

theorem gaussian_integrable_tensorWordTrace_mul (w v : List ι) :
    Integrable (fun z : GaussianCoordinates ι n × GaussianCoordinates ι n =>
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) *
        Matrix.trace (gaussianTensorWordMatrix z.1 z.2 v)) gaussianTensorLaw := by
  have hi := (gaussian_integrable_wordTrace_mul (n := n) w v).mul_prod
    (gaussian_integrable_wordTrace_mul (n := n) w v)
  apply hi.congr
  filter_upwards with z
  simp only [gaussianTensorWordTrace_eq]
  ring

theorem gaussian_tensorWordTrace_mul_integral (w v : List ι) :
    (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) *
        Matrix.trace (gaussianTensorWordMatrix z.1 z.2 v) ∂gaussianTensorLaw) =
      (∫ x : GaussianCoordinates ι n,
        Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v)
          ∂gaussianProductLaw ((ι × n) × Bool)) ^ 2 := by
  have he (z : GaussianCoordinates ι n × GaussianCoordinates ι n) :
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) *
        Matrix.trace (gaussianTensorWordMatrix z.1 z.2 v) =
      (Matrix.trace (gaussianWordMatrix z.1 w) * Matrix.trace (gaussianWordMatrix z.1 v)) *
        (Matrix.trace (gaussianWordMatrix z.2 w) * Matrix.trace (gaussianWordMatrix z.2 v)) := by
    simp only [gaussianTensorWordTrace_eq]
    ring
  simp_rw [he]
  rw [gaussianTensorLaw, pow_two]
  exact integral_prod_mul (L := ℂ)
    (μ := gaussianProductLaw ((ι × n) × Bool))
    (ν := gaussianProductLaw ((ι × n) × Bool))
    (fun x : GaussianCoordinates ι n =>
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v))
    (fun x : GaussianCoordinates ι n =>
      Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v))

theorem gaussian_tensorWordTrace_mul_integral_re (w v : List ι) :
    (∫ z : GaussianCoordinates ι n × GaussianCoordinates ι n,
      Matrix.trace (gaussianTensorWordMatrix z.1 z.2 w) *
        Matrix.trace (gaussianTensorWordMatrix z.1 z.2 v) ∂gaussianTensorLaw).re =
      (∫ x : GaussianCoordinates ι n,
        Matrix.trace (gaussianWordMatrix x w) * Matrix.trace (gaussianWordMatrix x v)
          ∂gaussianProductLaw ((ι × n) × Bool)).re ^ 2 := by
  rw [gaussian_tensorWordTrace_mul_integral, pow_two, Complex.mul_re,
    gaussian_wordTrace_mul_integral_im_zero]
  ring

end AHH
