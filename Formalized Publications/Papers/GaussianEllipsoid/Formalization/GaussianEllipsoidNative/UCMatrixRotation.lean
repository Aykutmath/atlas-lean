import UCNormalizedRows
import UCFrobeniusStein
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Source-matrix orthogonal conjugation and dimension-free Frobenius
perturbation bounds, matching the frame-alignment operator norm exactly. -/
noncomputable section
open BMQuadraticStein
open scoped BigOperators Matrix Matrix.Norms.L2Operator
namespace GaussianEllipsoid.UCMatrixRotation

 theorem matrixOpNorm_transpose {d : ℕ} (A : Square d) : matrixOpNorm A.transpose = matrixOpNorm A := by
  unfold matrixOpNorm
  rw [← real_conjTranspose_eq_transpose]
  exact Matrix.l2_opNorm_conjTranspose A

 theorem frobeniusNorm_mul_le_op_left {d : ℕ} (A B : Square d) :
    frobeniusNorm (A*B) ≤ matrixOpNorm A*frobeniusNorm B := by
  have h := UCFrobeniusStein.frobeniusSq_mul_le_spectral_frobenius A B
  simp only [frobeniusSq] at h
  rw [← frobeniusNorm_sq, ← frobeniusNorm_sq, UCNormalizedRows.spectralNorm_eq_matrixOpNorm] at h
  apply (sq_le_sq₀ (frobeniusNorm_nonneg _) (mul_nonneg (matrixOpNorm_nonneg _) (frobeniusNorm_nonneg _))).mp
  simpa only [mul_pow] using h

 theorem frobeniusNorm_mul_le_op_right {d : ℕ} (A B : Square d) :
    frobeniusNorm (A*B) ≤ frobeniusNorm A*matrixOpNorm B := by
  have h := frobeniusNorm_mul_le_op_left B.transpose A.transpose
  rw [← Matrix.transpose_mul, frobeniusNorm_transpose, matrixOpNorm_transpose,
    frobeniusNorm_transpose] at h
  simpa only [mul_comm] using h

 def rotationMatrix {d : ℕ} (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : Square d :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))

@[simp] theorem toEuclideanCLM_rotation {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (rotationMatrix O) =
      (O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ)).apply_symm_apply _

@[simp] theorem rotation_transpose {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    (rotationMatrix O).transpose = rotationMatrix O.symm := by
  have h := (map_star (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm
    (O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))).symm
  simpa only [rotationMatrix, Matrix.star_eq_conjTranspose, real_conjTranspose_eq_transpose,
    ContinuousLinearMap.star_eq_adjoint, O.adjoint_eq_symm] using h

@[simp] theorem rotation_left_inverse {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    rotationMatrix O.symm*rotationMatrix O = 1 := by
  have hprod : (O.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))*
      (O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    exact O.symm_apply_apply x
  unfold rotationMatrix
  rw [← map_mul, hprod, map_one]

@[simp] theorem rotation_right_inverse {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    rotationMatrix O*rotationMatrix O.symm = 1 := by
  simpa only [LinearIsometryEquiv.symm_symm] using rotation_left_inverse O.symm

 theorem rotation_opNorm_le_one {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) : matrixOpNorm (rotationMatrix O) ≤ 1 := by
  rw [← UCNormalizedRows.spectralNorm_eq_matrixOpNorm]
  unfold spectralNorm
  rw [toEuclideanCLM_rotation]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using O.norm_map x |>.le

 theorem rotation_difference_opNorm {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    matrixOpNorm (rotationMatrix O-1) =
      ‖(O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))-1‖ := by
  rw [← UCNormalizedRows.spectralNorm_eq_matrixOpNorm]
  unfold spectralNorm
  rw [map_sub,map_one,toEuclideanCLM_rotation]

 def conjugate {d : ℕ} (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) : Square d :=
  rotationMatrix O*A*(rotationMatrix O).transpose

@[simp] theorem conjugate_inverse {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    conjugate O.symm (conjugate O A) = A := by
  simp only [conjugate,rotation_transpose,LinearIsometryEquiv.symm_symm]
  calc
    _ = (rotationMatrix O.symm*rotationMatrix O)*A*(rotationMatrix O.symm*rotationMatrix O) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [rotation_left_inverse]; simp

 theorem conjugate_frobenius_le {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    frobeniusNorm (conjugate O A) ≤ frobeniusNorm A := by
  have hO := rotation_opNorm_le_one O
  have hOt : matrixOpNorm (rotationMatrix O).transpose ≤ 1 := by
    rw [matrixOpNorm_transpose]
    exact hO
  calc
    _ ≤ frobeniusNorm (rotationMatrix O*A)*matrixOpNorm (rotationMatrix O).transpose :=
      frobeniusNorm_mul_le_op_right _ _
    _ ≤ frobeniusNorm (rotationMatrix O*A) := by nlinarith [frobeniusNorm_nonneg (rotationMatrix O*A)]
    _ ≤ matrixOpNorm (rotationMatrix O)*frobeniusNorm A := frobeniusNorm_mul_le_op_left _ _
    _ ≤ _ := by nlinarith [frobeniusNorm_nonneg A]

@[simp] theorem conjugate_frobeniusNorm {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    frobeniusNorm (conjugate O A) = frobeniusNorm A := by
  have hb := conjugate_frobenius_le O.symm (conjugate O A)
  rw [conjugate_inverse] at hb
  exact le_antisymm (conjugate_frobenius_le O A) hb

 theorem conjugate_opNorm_le {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    matrixOpNorm (conjugate O A) ≤ matrixOpNorm A := by
  have hO := rotation_opNorm_le_one O
  have hOt : matrixOpNorm (rotationMatrix O).transpose ≤ 1 := by rw [matrixOpNorm_transpose]; exact hO
  calc
    _ ≤ matrixOpNorm (rotationMatrix O*A)*matrixOpNorm (rotationMatrix O).transpose := matrixOpNorm_mul_le _ _
    _ ≤ matrixOpNorm (rotationMatrix O*A) := by nlinarith [matrixOpNorm_nonneg (rotationMatrix O*A)]
    _ ≤ matrixOpNorm (rotationMatrix O)*matrixOpNorm A := matrixOpNorm_mul_le _ _
    _ ≤ _ := by nlinarith [matrixOpNorm_nonneg A]

@[simp] theorem conjugate_matrixOpNorm {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    matrixOpNorm (conjugate O A) = matrixOpNorm A := by
  have hb := conjugate_opNorm_le O.symm (conjugate O A)
  rw [conjugate_inverse] at hb
  exact le_antisymm (conjugate_opNorm_le O A) hb

 theorem conjugate_posSemidef {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {A : Square d} (hA : A.PosSemidef) :
    (conjugate O A).PosSemidef := by
  simpa only [real_conjTranspose_eq_transpose, conjugate] using hA.mul_mul_conjTranspose_same (rotationMatrix O)

@[simp] theorem conjugate_trace {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    Matrix.trace (conjugate O A) = Matrix.trace A := by
  rw [conjugate,Matrix.trace_mul_comm,← Matrix.mul_assoc,rotation_transpose,rotation_left_inverse,Matrix.one_mul]

/-- Dimension-free near-identity Frobenius perturbation, for every matrix. -/
theorem conjugate_sub_frobenius_le {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    frobeniusNorm (conjugate O A-A) ≤
      2*‖(O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))-1‖*frobeniusNorm A := by
  let U := rotationMatrix O
  have he : conjugate O A-A = (U-1)*A*U.transpose+A*(U.transpose-1) := by
    unfold conjugate U
    noncomm_ring
  have hUt : matrixOpNorm U.transpose ≤ 1 := by rw [matrixOpNorm_transpose]; exact rotation_opNorm_le_one O
  have hdiff : matrixOpNorm (U.transpose-1) = matrixOpNorm (U-1) := by
    have he : U.transpose-1 = (U-1).transpose := by simp
    rw [he,matrixOpNorm_transpose]
  rw [he]
  calc
    _ ≤ frobeniusNorm ((U-1)*A*U.transpose)+frobeniusNorm (A*(U.transpose-1)) := frobeniusNorm_add_le _ _
    _ ≤ frobeniusNorm ((U-1)*A)*matrixOpNorm U.transpose+frobeniusNorm A*matrixOpNorm (U.transpose-1) :=
      add_le_add (frobeniusNorm_mul_le_op_right _ _) (frobeniusNorm_mul_le_op_right _ _)
    _ ≤ frobeniusNorm ((U-1)*A)+frobeniusNorm A*matrixOpNorm (U-1) := by
      rw [hdiff]
      nlinarith [frobeniusNorm_nonneg ((U-1)*A)]
    _ ≤ matrixOpNorm (U-1)*frobeniusNorm A+frobeniusNorm A*matrixOpNorm (U-1) :=
      add_le_add (frobeniusNorm_mul_le_op_left _ _) le_rfl
    _ = _ := by rw [show matrixOpNorm (U-1) = _ from rotation_difference_opNorm O]; ring

@[simp] theorem conjugate_add {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A B : Square d) :
    conjugate O (A+B) = conjugate O A+conjugate O B := by
  simp [conjugate, Matrix.mul_add, Matrix.add_mul]

@[simp] theorem conjugate_smul {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (t : ℝ) (A : Square d) :
    conjugate O (t • A) = t • conjugate O A := by
  simp [conjugate]

 theorem conjugate_mul {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A B : Square d) :
    conjugate O A*conjugate O B = conjugate O (A*B) := by
  simp only [conjugate, rotation_transpose]
  calc
    _ = rotationMatrix O*A*(rotationMatrix O.symm*rotationMatrix O)*B*rotationMatrix O.symm := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [rotation_left_inverse]; simp only [Matrix.mul_one,Matrix.mul_assoc]

 theorem conjugate_zero_product {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) {A B : Square d} (h : A*B=0) :
    conjugate O A*conjugate O B=0 := by rw [conjugate_mul,h]; simp [conjugate]

 theorem toEuclideanCLM_conjugate {d : ℕ}
    (O : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (A : Square d) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (conjugate O A) =
      (O : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))*
        Matrix.toEuclideanCLM (𝕜 := ℝ) A*
        (O.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) := by
  simp only [conjugate, rotation_transpose, map_mul, toEuclideanCLM_rotation]

#print axioms conjugate_sub_frobenius_le
#print axioms conjugate_frobeniusNorm
#print axioms conjugate_matrixOpNorm
end GaussianEllipsoid.UCMatrixRotation
