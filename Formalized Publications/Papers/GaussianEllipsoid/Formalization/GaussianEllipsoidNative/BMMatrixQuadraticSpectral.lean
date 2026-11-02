import GaussianQuadraticTail
import BMNormalizedStein
import Mathlib.Analysis.Matrix.Spectrum

noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments GaussianMixedNormHelpers Module
open scoped BigOperators InnerProductSpace
namespace BMQuadraticSpectral

/-- The ordinary-coordinate centered quadratic form appearing in BM. -/
def matrixQuadratic {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  ((∑ i, ∑ j, A i j * (x i * x j)) - Matrix.trace A) / Real.sqrt d

/-- Symmetry of the genuine Euclidean operator attached to a real symmetric matrix. -/
def matrixSymmetric {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = A) :
    ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A).toLinearMap.IsSymmetric := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  apply Matrix.isHermitian_iff_isSymmetric.mp
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA

/-- Matrix trace equals the trace of the actual Euclidean linear operator. -/
theorem trace_matrixCLM {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.trace ℝ (Euclid d) ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A).toLinearMap =
      Matrix.trace A := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]

/-- Exact coordinate evaluation of the genuine Euclidean quadratic observable. -/
theorem normalizedQuadratic_matrix_eq {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    normalizedQuadratic ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A)
      (((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)).symm).symm x) = matrixQuadratic A x := by
  unfold normalizedQuadratic matrixQuadratic
  rw [trace_matrixCLM, EuclideanSpace.inner_eq_star_dotProduct]
  congr 2
  change ∑ i, (∑ j, A i j * x j) * x i = ∑ i, ∑ j, A i j * (x i * x j)
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Exact adapter to the existing BM normalized multivariate polynomial observable. -/
theorem matrixQuadratic_eq_eval_normalizedQuadratic {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    matrixQuadratic A x = MvPolynomial.eval x (BMQuadraticStein.normalizedQuadratic d A) := by
  simp only [BMQuadraticStein.normalizedQuadratic, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, BMQuadraticStein.eval_centeredQuadratic,
    matrixQuadratic]
  ring

/-- Gaussian coordinate realization itself has exactly the Euclidean Gaussian distribution. -/
theorem euclideanCoordinates_identDistrib {d : ℕ} :
    IdentDistrib (((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)).symm).symm) (id : Euclid d → Euclid d)
      (gaussianProductLaw (Fin d)) (euclideanGaussianLaw (Fin d)) := by
  refine ⟨((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)).symm).symm.measurable.aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  rw [Measure.map_id]
  rfl

/-- The actual ordinary-coordinate quadratic form has the exact diagonal Gaussian law. -/
theorem matrixQuadratic_identDistrib {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) :
    IdentDistrib (matrixQuadratic A)
      (GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight (matrixSymmetric hA)))
      (gaussianProductLaw (Fin d)) (gaussianProductLaw (Fin d)) := by
  have hh := euclideanCoordinates_identDistrib.comp
    (continuous_normalizedQuadratic ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A)).measurable
  have hQ : normalizedQuadratic ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) A) ∘
      ((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)).symm).symm = matrixQuadratic A := by
    funext x
    exact normalizedQuadratic_matrix_eq A x
  rw [hQ, Function.comp_id] at hh
  exact hh.trans (normalizedQuadratic_identDistrib (matrixSymmetric hA))

/-- Actual spectral weights of a symmetric norm-bounded matrix obey both diagonal hypotheses. -/
theorem matrix_eigenWeight_bounds {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = A)
    (hN : BMQuadraticStein.spectralNorm A ≤ 1) :
    (∀ i, |eigenWeight (matrixSymmetric hA) i| ≤ 1/Real.sqrt d) ∧
      (∑ i, (eigenWeight (matrixSymmetric hA) i)^2) ≤ 1 :=
  ⟨eigenWeight_abs_le (matrixSymmetric hA) hN,
    sum_eigenWeight_sq_le hd (matrixSymmetric hA) hN⟩

/-- Exact distribution statement for the BM normalized-polynomial endpoint. -/
theorem eval_normalizedQuadratic_identDistrib {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.transpose = A) :
    IdentDistrib (fun x => MvPolynomial.eval x (BMQuadraticStein.normalizedQuadratic d A))
      (GaussianEllipsoidCandidate.centeredDiagonal (eigenWeight (matrixSymmetric hA)))
      (gaussianProductLaw (Fin d)) (gaussianProductLaw (Fin d)) := by
  simpa only [← matrixQuadratic_eq_eval_normalizedQuadratic] using matrixQuadratic_identDistrib hA

/-- Actual matrix quadratic gauge tail. All distribution and spectral hypotheses are proved. -/
theorem matrixQuadratic_gauge_tail_ennreal {d : ℕ} (hd : 0 < d)
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = A)
    (hN : BMQuadraticStein.spectralNorm A ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianProductLaw (Fin d))
      {x | t < min ((matrixQuadratic A x)^2) (Real.sqrt d * |matrixQuadratic A x|)/16} ≤
      ENNReal.ofReal (2*Real.exp (-t)) := by
  have he := (matrixQuadratic_identDistrib hA).measure_mem_eq
    (show MeasurableSet {s : ℝ | t < min (s^2) (Real.sqrt d * |s|)/16} from
      measurableSet_lt measurable_const (by fun_prop))
  simp only [Set.preimage_setOf_eq] at he
  rw [he]
  exact GaussianEllipsoidCandidate.centeredDiagonal_gauge_tail_ennreal
    (eigenWeight (matrixSymmetric hA)) (Nat.cast_pos.mpr hd)
    (matrix_eigenWeight_bounds hd hA hN).1 (matrix_eigenWeight_bounds hd hA hN).2 ht

#print axioms matrixQuadratic_identDistrib
#print axioms matrix_eigenWeight_bounds
#print axioms eval_normalizedQuadratic_identDistrib
#print axioms matrixQuadratic_gauge_tail_ennreal
end BMQuadraticSpectral
