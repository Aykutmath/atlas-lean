import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

noncomputable section
open Finset InnerProductSpace

namespace GaussianMixedNormHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Real Gram matrix of an ordered finite family. -/
def realGramMatrix {r : ℕ} (f : Fin r → E) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => inner (𝕜 := ℝ) (f i) (f j)

/-- Unit-upper-triangular coefficients reconstructing a family from its
unnormalized Gram–Schmidt residuals, including linearly dependent families. -/
def gramSchmidtCoefficients {r : ℕ} (f : Fin r → E) : Matrix (Fin r) (Fin r) ℝ :=
  (1 : Matrix (Fin r) (Fin r) ℝ) + Matrix.of (fun i j =>
    if i < j then inner (𝕜 := ℝ) (gramSchmidt ℝ f i) (f j) / ‖gramSchmidt ℝ f i‖ ^ 2 else 0)

theorem gramSchmidtCoefficients_diagonal {r : ℕ} (f : Fin r → E) (i : Fin r) :
    gramSchmidtCoefficients f i i = 1 := by
  simp [gramSchmidtCoefficients]

theorem gramSchmidtCoefficients_triangular {r : ℕ} (f : Fin r → E) :
    (gramSchmidtCoefficients f).BlockTriangular id := by
  intro i j hij
  have hji : ¬i < j := not_lt_of_ge (le_of_lt hij)
  have hne : i ≠ j := ne_of_gt hij
  simp [gramSchmidtCoefficients, Matrix.one_apply, hne, hji]

theorem gramSchmidtCoefficients_det {r : ℕ} (f : Fin r → E) :
    (gramSchmidtCoefficients f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (gramSchmidtCoefficients_triangular f)]
  simp [gramSchmidtCoefficients_diagonal]

/-- Exact reconstruction identity from Mathlib's recursive Gram–Schmidt process. -/
theorem gramSchmidt_reconstruction {r : ℕ} (f : Fin r → E) (j : Fin r) :
    f j = ∑ i, gramSchmidtCoefficients f i j • gramSchmidt ℝ f i := by
  rw [gramSchmidt_def'' ℝ f j]
  simp only [gramSchmidtCoefficients, Matrix.add_apply, Matrix.of_apply, add_smul, Finset.sum_add_distrib]
  simp [Matrix.one_apply, ite_smul, Finset.sum_ite, Finset.filter_gt_eq_Iio]

/-- Congruence formula for the Gram matrix under any exact coordinate expansion. -/
theorem realGramMatrix_of_expansion {r : ℕ} (f g : Fin r → E)
    (C : Matrix (Fin r) (Fin r) ℝ)
    (hC : ∀ j, f j = ∑ i, C i j • g i) :
    realGramMatrix f = C.transpose * realGramMatrix g * C := by
  ext i j
  change inner (𝕜 := ℝ) (f i) (f j) = _
  rw [hC i, hC j]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Matrix.mul_apply, Matrix.transpose_apply, realGramMatrix, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- Gram–Schmidt orthogonality makes the residual Gram matrix diagonal. -/
theorem realGramMatrix_gramSchmidt {r : ℕ} (f : Fin r → E) :
    realGramMatrix (gramSchmidt ℝ f) =
      Matrix.diagonal (fun i => ‖gramSchmidt ℝ f i‖ ^ 2) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realGramMatrix, real_inner_self_eq_norm_sq]
  · simp [realGramMatrix, Matrix.diagonal_apply, hij, gramSchmidt_orthogonal ℝ f hij]

/-- Deterministic Bartlett identity: the Gram determinant equals the product
of squared Gram–Schmidt residual norms. No full-rank or probability premise. -/
theorem det_realGramMatrix_eq_prod_gramSchmidt_norm_sq {r : ℕ} (f : Fin r → E) :
    (realGramMatrix f).det = ∏ i, ‖gramSchmidt ℝ f i‖ ^ 2 := by
  rw [realGramMatrix_of_expansion f (gramSchmidt ℝ f) (gramSchmidtCoefficients f)
      (gramSchmidt_reconstruction f),
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    gramSchmidtCoefficients_det, realGramMatrix_gramSchmidt, Matrix.det_diagonal]
  ring


/-- Span of the columns strictly before j. -/
def priorSpan {r : ℕ} (f : Fin r → E) (j : Fin r) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (fun i : Set.Iio j => f i))

/-- A linearly independent family's j earlier columns span exactly j dimensions. -/
theorem finrank_priorSpan {r : ℕ} (f : Fin r → E) (hf : LinearIndependent ℝ f)
    (j : Fin r) : Module.finrank ℝ (priorSpan f j) = (j : ℕ) := by
  unfold priorSpan
  simpa [Function.comp_def] using
    (finrank_span_eq_card (hf.comp (fun i : Set.Iio j => i.val) Subtype.val_injective))

/-- Exact residual dimension in an m-dimensional Euclidean ambient space. -/
theorem finrank_priorSpan_orthogonal {r m : ℕ}
    (f : Fin r → EuclideanSpace ℝ (Fin m)) (hf : LinearIndependent ℝ f)
    (j : Fin r) : Module.finrank ℝ (priorSpan f j)ᗮ = m - (j : ℕ) := by
  have hdim := (priorSpan f j).finrank_add_finrank_orthogonal
  rw [finrank_priorSpan f hf j, finrank_euclideanSpace, Fintype.card_fin] at hdim
  omega

/-- The zero-based Bartlett degrees of freedom for r rows in 2r columns. -/
theorem bartlett_residual_degrees {r : ℕ}
    (f : Fin r → EuclideanSpace ℝ (Fin (2 * r))) (hf : LinearIndependent ℝ f)
    (j : Fin r) :
    Module.finrank ℝ (priorSpan f j)ᗮ = 2 * r - (j : ℕ) ∧
      2 * r - (j : ℕ) = r + (r - (j : ℕ)) ∧ 0 < r - (j : ℕ) := by
  refine ⟨finrank_priorSpan_orthogonal f hf j, ?_, ?_⟩ <;> omega


/-- Rows of a real matrix represented in their true Euclidean inner-product space. -/
def matrixEuclideanRows {r m : ℕ} (G : Matrix (Fin r) (Fin m) ℝ) :
    Fin r → EuclideanSpace ℝ (Fin m) := fun i => (WithLp.equiv 2 (Fin m → ℝ)).symm (fun j => G i j)

theorem realGramMatrix_matrixEuclideanRows {r m : ℕ}
    (G : Matrix (Fin r) (Fin m) ℝ) :
    realGramMatrix (matrixEuclideanRows G) = G * G.transpose := by
  ext i j
  simp [realGramMatrix, matrixEuclideanRows, PiLp.inner_apply, Matrix.mul_apply,
    Matrix.transpose_apply, real_inner_comm, mul_comm]

/-- Deterministic Bartlett determinant identity in ordinary matrix notation. -/
theorem det_mul_transpose_eq_prod_gramSchmidt {r m : ℕ}
    (G : Matrix (Fin r) (Fin m) ℝ) :
    (G * G.transpose).det =
      ∏ i, ‖gramSchmidt ℝ (matrixEuclideanRows G) i‖ ^ 2 := by
  rw [← realGramMatrix_matrixEuclideanRows]
  exact det_realGramMatrix_eq_prod_gramSchmidt_norm_sq _

/-- The scaled covariance determinant equals its scaled residual product. -/
theorem det_scaled_mul_transpose_eq_prod_gramSchmidt {r m : ℕ}
    (G : Matrix (Fin r) (Fin m) ℝ) (c : ℝ) :
    (c • (G * G.transpose)).det =
      c ^ r * ∏ i, ‖gramSchmidt ℝ (matrixEuclideanRows G) i‖ ^ 2 := by
  rw [Matrix.det_smul, Fintype.card_fin, det_mul_transpose_eq_prod_gramSchmidt]

end GaussianMixedNormHelpers
