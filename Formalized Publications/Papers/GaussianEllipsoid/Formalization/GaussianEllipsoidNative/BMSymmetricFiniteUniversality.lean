import BMFiniteUniversality
import BMMatrixQuadraticSpectral
import OperatorFractionalNet
import GaussianUniformFractionalMoment

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory ProbabilityTheory GaussianTensorMoments BMQuadraticStein
open BMSmoothQuadraticComposition BMFiniteGibbsTest BMFiniteGibbsHessian
open BMFiniteGroundState BMFiniteUniversality BMGaussianEquivalent BMUniformMoment
open GaussianMixedNormHelpers Filter
open scoped BigOperators BoundedContinuousFunction

namespace BMSymmetricFiniteUniversality

/-- Coordinate matrix of a symmetric Euclidean operator, retaining exactly its
operator norm rather than the default entrywise matrix norm. -/
def matrixOf {d : ℕ} (T : SymOp d) : Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm T.val

@[simp] theorem toEuclideanCLM_matrixOf {d : ℕ} (T : SymOp d) :
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (matrixOf T) = T.val :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).apply_symm_apply T.val

@[simp] theorem spectralNorm_matrixOf {d : ℕ} (T : SymOp d) :
    spectralNorm (matrixOf T) = ‖T‖ := by
  simp only [spectralNorm,toEuclideanCLM_matrixOf]
  rfl

theorem matrixOf_transpose {d : ℕ} (T : SymOp d) :
    (matrixOf T).transpose = matrixOf T := by
  have h : (((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (matrixOf T)).toLinearMap).IsSymmetric := by
    rw [toEuclideanCLM_matrixOf]
    exact T.property
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] at h
  have hm := Matrix.isHermitian_iff_isSymmetric.mpr h
  simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using hm

theorem normalizedQuadratic_coordinate {d : ℕ} (T : SymOp d) (x : Fin d → ℝ) :
    BMQuadraticSpectral.normalizedQuadratic T.val ((MeasurableEquiv.toLp 2 ((Fin d) → ℝ)) x) =
      MvPolynomial.eval x (BMQuadraticStein.normalizedQuadratic d (matrixOf T)) := by
  rw [← toEuclideanCLM_matrixOf T]
  exact (BMQuadraticSpectral.normalizedQuadratic_matrix_eq (matrixOf T) x).trans
    (BMQuadraticSpectral.matrixQuadratic_eq_eval_normalizedQuadratic (matrixOf T) x)

/-- Full finite iid coordinate-to-Euclidean Gaussian integral identity. -/
theorem integral_euclidean_rows (d n : ℕ)
    (H : (Fin n → BMQuadraticSpectral.Euclid d) → ℝ) :
    (∫ x : Fin n → (Fin d → ℝ),
      H (fun i => (MeasurableEquiv.toLp 2 ((Fin d) → ℝ)) (x i))
        ∂Measure.pi (fun _ : Fin n => gaussianProductLaw (Fin d))) =
      ∫ x, H x ∂gaussianSampleLaw d n := by
  let e := (MeasurableEquiv.toLp 2 ((Fin d) → ℝ))
  letI : ∀ _i : Fin n, SigmaFinite (euclideanGaussianLaw (Fin d)) := fun _ => inferInstance
  have hp : MeasurePreserving e (gaussianProductLaw (Fin d)) (euclideanGaussianLaw (Fin d)) :=
    ⟨e.measurable,rfl⟩
  have hp' : MeasurePreserving (MeasurableEquiv.piCongrRight (fun _i : Fin n => e))
      (Measure.pi fun _ : Fin n => gaussianProductLaw (Fin d)) (gaussianSampleLaw d n) :=
    measurePreserving_pi (fun _ : Fin n => gaussianProductLaw (Fin d))
      (fun _ : Fin n => euclideanGaussianLaw (Fin d)) (fun _ => hp)
  exact hp'.integral_comp' H

/-- Actual finite-net ground expectation in the Euclidean source coordinates
used by the uniform empirical-process theorem. -/
def euclideanQuadraticGroundExpectation {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Data2 Unit) (d n : ℕ) (T : κ → SymOp d) : ℝ :=
  ∫ x : Fin (n+1) → BMQuadraticSpectral.Euclid d,
    ground (modelData (κ := κ) P 1 (by norm_num)).toData ((d:ℝ)^2)
      (fun i a => BMQuadraticSpectral.normalizedQuadratic (T a).val (x i))
    ∂gaussianSampleLaw d (n+1)

theorem quadraticGroundExpectation_matrixOf {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (P : Data2 Unit) (d n : ℕ) (T : κ → SymOp d) :
    quadraticGroundExpectation P d n (fun a => matrixOf (T a)) =
      euclideanQuadraticGroundExpectation P d n T := by
  unfold euclideanQuadraticGroundExpectation
  rw [← integral_euclidean_rows]
  unfold quadraticGroundExpectation
  simp only [normalizedQuadratic_coordinate,polynomialFamily,ContinuousMap.coe_mk]

/-- The finite-net expectation universality theorem expressed directly on
symmetric Euclidean operators, matching the actual uniform-moment net layer. -/
theorem finite_symmetric_ground_expectation_universality
    (κ : ℕ → Type*) [∀ d, Fintype (κ d)] [∀ d, DecidableEq (κ d)] [∀ d, Nonempty (κ d)]
    (P : Data2 Unit) (n : ℕ → ℕ) (T : (d : ℕ) → κ d → SymOp d)
    {K α C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hT : ∀ d a, ‖T d a‖ ≤ K)
    (hn : ∀ d, 0 < d → (n d+1 : ℕ) ≤ α*(d:ℝ)^2)
    (hcard : ∀ d, 0 < d → Real.log (Fintype.card (κ d) : ℝ) ≤ C*(d:ℝ)^2) :
    Tendsto (fun d => |euclideanQuadraticGroundExpectation P d (n d) (T d)-
      goeGroundExpectation P d (n d) (fun a => matrixOf (T d a))|) atTop (nhds 0) := by
  have h := finite_ground_expectation_universality κ P n (fun d a => matrixOf (T d a))
    (fun d a => matrixOf_transpose (T d a)) hK hC
    (fun d a => by simpa using hT d a) hn hcard
  simpa only [quadraticGroundExpectation_matrixOf] using h

#print axioms integral_euclidean_rows
#print axioms finite_symmetric_ground_expectation_universality
end BMSymmetricFiniteUniversality
