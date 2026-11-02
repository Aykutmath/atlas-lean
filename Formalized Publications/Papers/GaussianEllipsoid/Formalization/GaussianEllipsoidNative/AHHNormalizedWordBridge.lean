import AHHGaussianModelBridge
import AHHGaussianWordPositivity

/-! Exact normalization transport from the actual complex Gaussian Wick model
into the manuscript's normalized-factor projector words. -/
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments
open scoped BigOperators
namespace AHHGaussian

/-- Splitting the real and imaginary entries is a genuine measurable equivalence. -/
def splitRealImagEquiv (n h : ℕ) :
    (((Fin n × Fin h) × Bool) → ℝ) ≃ᵐ PairEntries n h where
  toFun x := (fun ij => x (ij,false), fun ij => x (ij,true))
  invFun x := fun p => if p.2 then x.2 p.1 else x.1 p.1
  left_inv x := by
    funext p
    rcases p with ⟨ij,b⟩
    cases b <;> rfl
  right_inv x := rfl
  measurable_toFun := by
    change Measurable (fun x : ((Fin n × Fin h) × Bool) → ℝ =>
      (fun ij => x (ij,false), fun ij => x (ij,true)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : PairEntries n h => fun p : (Fin n × Fin h) × Bool =>
      if p.2 then x.2 p.1 else x.1 p.1)
    apply measurable_pi_iff.mpr
    intro p
    cases p.2 <;> dsimp <;> fun_prop

theorem splitRealImagEquiv_preserving (n h : ℕ) :
    MeasurePreserving (splitRealImagEquiv n h)
      (gaussianProductLaw ((Fin n × Fin h) × Bool)) (pairGaussianLaw n h) :=
  gaussian_bool_split_preserving

def normalizedProjector (n h : ℕ) (x : PairEntries n h) (i : Fin n) :
    Matrix (Fin h) (Fin h) ℂ :=
  AHHAlgebraBridges.projector (fun j => normalizedFactor n h true x i j)

def normalizedWordMatrix (n h : ℕ) (x : PairEntries n h) (w : List (Fin n)) :
    Matrix (Fin h) (Fin h) ℂ := (w.map (normalizedProjector n h x)).prod

/-- Rank-one projectors pick up the square of the normalization factor. -/
theorem projector_div_real {ι : Type*} (v : ι → ℂ) (r : ℝ) :
    AHHAlgebraBridges.projector (fun i => v i / (r : ℂ)) =
      ((r : ℂ)^2)⁻¹ • AHHAlgebraBridges.projector v := by
  ext i j
  change (v i / (r : ℂ)) * star (v j / (r : ℂ)) =
    ((r : ℂ)^2)⁻¹ * (v i * star (v j))
  simp only [Complex.star_def, map_div₀, map_mul, map_inv₀, Complex.conj_ofReal, div_eq_mul_inv, inv_pow]
  ring

/-- Literal pointwise equality for each source-normalized factor projector. -/
theorem normalizedProjector_split_eq (n h : ℕ)
    (x : ((Fin n × Fin h) × Bool) → ℝ) (i : Fin n) :
    normalizedProjector n h (splitRealImagEquiv n h x) i =
      ((2 * (h : ℂ))⁻¹) • AHH.gaussianProjector x i := by
  change AHHAlgebraBridges.projector
      (fun j : Fin h => _ / (Real.sqrt (2 * (h : ℝ)) : ℂ)) = _
  rw [projector_div_real]
  have hsqrt : (Real.sqrt (2 * (h : ℝ)) : ℂ)^2 = 2 * (h : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (Nat.cast_nonneg (2*h))
  rw [hsqrt]
  congr 1
  ext j k
  simp [AHHAlgebraBridges.projector, AHH.gaussianProjector, normalizedCoordinate,
    splitRealImagEquiv, AHH.endpointValue, AHH.imaginaryCoefficient, sign]

/-- Every occurrence in a word contributes exactly (2h)⁻¹. -/
theorem normalizedWordMatrix_split_eq (n h : ℕ)
    (x : ((Fin n × Fin h) × Bool) → ℝ) (w : List (Fin n)) :
    normalizedWordMatrix n h (splitRealImagEquiv n h x) w =
      ((2 * (h : ℂ))⁻¹)^w.length • AHH.gaussianWordMatrix x w := by
  induction w with
  | nil => simp [normalizedWordMatrix, AHH.gaussianWordMatrix]
  | cons i w ih =>
    change normalizedProjector n h (splitRealImagEquiv n h x) i *
      normalizedWordMatrix n h (splitRealImagEquiv n h x) w = _
    rw [normalizedProjector_split_eq, ih, smul_mul_smul]
    simp only [List.length_cons, AHH.gaussianWordMatrix, List.map_cons, List.prod_cons,
      pow_succ, mul_comm]

theorem normalizedWordTrace_split_eq (n h : ℕ)
    (x : ((Fin n × Fin h) × Bool) → ℝ) (w : List (Fin n)) :
    Matrix.trace (normalizedWordMatrix n h (splitRealImagEquiv n h x) w) =
      (((2 * (h : ℝ))⁻¹)^w.length : ℝ) * Matrix.trace (AHH.gaussianWordMatrix x w) := by
  rw [normalizedWordMatrix_split_eq, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- All normalized projector-word traces are integrable under the actual pair law. -/
theorem normalizedWordTrace_integrable (n h : ℕ) (w : List (Fin n)) :
    Integrable (fun x => Matrix.trace (normalizedWordMatrix n h x w)) (pairGaussianLaw n h) := by
  apply ((splitRealImagEquiv_preserving n h).integrable_comp_emb
    (splitRealImagEquiv n h).measurableEmbedding).mp
  change Integrable (fun x => Matrix.trace (normalizedWordMatrix n h (splitRealImagEquiv n h x) w)) _
  simp_rw [normalizedWordTrace_split_eq]
  exact (AHH.gaussian_integrable_wordTrace w).const_mul _

/-- Exact expectation identity, retaining the full normalization power. -/
theorem normalizedWordTrace_integral (n h : ℕ) (w : List (Fin n)) :
    (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h) =
      (((2 * (h : ℝ))⁻¹)^w.length : ℝ) *
        ∫ x : ((Fin n × Fin h) × Bool) → ℝ, Matrix.trace (AHH.gaussianWordMatrix x w)
          ∂gaussianProductLaw ((Fin n × Fin h) × Bool) := by
  rw [← (splitRealImagEquiv_preserving n h).integral_comp
    (splitRealImagEquiv n h).measurableEmbedding]
  simp_rw [normalizedWordTrace_split_eq]
  exact integral_const_mul _ _

theorem normalizedWordTrace_integral_im_zero (n h : ℕ) (w : List (Fin n)) :
    (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h).im = 0 := by
  rw [normalizedWordTrace_integral]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    AHH.gaussian_wordTrace_integral_im_zero, mul_zero, zero_mul, add_zero]

theorem normalizedWordTrace_integral_re_nonneg (n h : ℕ) (w : List (Fin n)) :
    0 ≤ (∫ x, Matrix.trace (normalizedWordMatrix n h x w) ∂pairGaussianLaw n h).re := by
  rw [normalizedWordTrace_integral]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (AHH.gaussian_wordTrace_integral_re_nonneg w)

/-- Products of traces retain the sum of their normalization exponents, even
when the two words share labels. -/
theorem normalizedWordTrace_mul_split_eq (n h : ℕ)
    (x : ((Fin n × Fin h) × Bool) → ℝ) (w v : List (Fin n)) :
    Matrix.trace (normalizedWordMatrix n h (splitRealImagEquiv n h x) w) *
      Matrix.trace (normalizedWordMatrix n h (splitRealImagEquiv n h x) v) =
      (((2 * (h : ℝ))⁻¹)^(w.length + v.length) : ℝ) *
        (Matrix.trace (AHH.gaussianWordMatrix x w) * Matrix.trace (AHH.gaussianWordMatrix x v)) := by
  rw [normalizedWordTrace_split_eq, normalizedWordTrace_split_eq, pow_add]
  push_cast
  ring

theorem normalizedWordTrace_mul_integrable (n h : ℕ) (w v : List (Fin n)) :
    Integrable (fun x => Matrix.trace (normalizedWordMatrix n h x w) *
      Matrix.trace (normalizedWordMatrix n h x v)) (pairGaussianLaw n h) := by
  apply ((splitRealImagEquiv_preserving n h).integrable_comp_emb
    (splitRealImagEquiv n h).measurableEmbedding).mp
  change Integrable (fun x => Matrix.trace (normalizedWordMatrix n h (splitRealImagEquiv n h x) w) *
    Matrix.trace (normalizedWordMatrix n h (splitRealImagEquiv n h x) v)) _
  simp_rw [normalizedWordTrace_mul_split_eq]
  exact (AHH.gaussian_integrable_wordTrace_mul w v).const_mul _

theorem normalizedWordTrace_mul_integral (n h : ℕ) (w v : List (Fin n)) :
    (∫ x, Matrix.trace (normalizedWordMatrix n h x w) *
      Matrix.trace (normalizedWordMatrix n h x v) ∂pairGaussianLaw n h) =
      (((2 * (h : ℝ))⁻¹)^(w.length + v.length) : ℝ) *
        ∫ x : ((Fin n × Fin h) × Bool) → ℝ,
          Matrix.trace (AHH.gaussianWordMatrix x w) * Matrix.trace (AHH.gaussianWordMatrix x v)
          ∂gaussianProductLaw ((Fin n × Fin h) × Bool) := by
  rw [← (splitRealImagEquiv_preserving n h).integral_comp
    (splitRealImagEquiv n h).measurableEmbedding]
  simp_rw [normalizedWordTrace_mul_split_eq]
  exact integral_const_mul _ _

theorem normalizedWordTrace_mul_integral_im_zero (n h : ℕ) (w v : List (Fin n)) :
    (∫ x, Matrix.trace (normalizedWordMatrix n h x w) *
      Matrix.trace (normalizedWordMatrix n h x v) ∂pairGaussianLaw n h).im = 0 := by
  rw [normalizedWordTrace_mul_integral]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    AHH.gaussian_wordTrace_mul_integral_im_zero, mul_zero, zero_mul, add_zero]

theorem normalizedWordTrace_mul_integral_re_nonneg (n h : ℕ) (w v : List (Fin n)) :
    0 ≤ (∫ x, Matrix.trace (normalizedWordMatrix n h x w) *
      Matrix.trace (normalizedWordMatrix n h x v) ∂pairGaussianLaw n h).re := by
  rw [normalizedWordTrace_mul_integral]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) (AHH.gaussian_wordTrace_mul_integral_re_nonneg w v)

#print axioms normalizedWordTrace_mul_integrable
#print axioms normalizedWordTrace_mul_integral
#print axioms normalizedWordTrace_mul_integral_re_nonneg

#print axioms normalizedProjector_split_eq
#print axioms normalizedWordTrace_integrable
#print axioms normalizedWordTrace_integral
#print axioms normalizedWordTrace_integral_re_nonneg
end AHHGaussian
