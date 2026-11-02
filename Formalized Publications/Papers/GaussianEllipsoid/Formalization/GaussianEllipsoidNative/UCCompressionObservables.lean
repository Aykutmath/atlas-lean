import UCOrthogonalCompression
import SupportedPolar

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
namespace UCEscape

lemma compress_opNorm_le {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d) (D : Op d) :
    ‖compress V D‖ ≤ ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    ‖compress V D x‖ ≤ ‖D (V x)‖ := adjoint_isometry_norm_le V _
    _ ≤ ‖D‖*‖V x‖ := D.le_opNorm _
    _ = ‖D‖*‖x‖ := by rw [V.norm_map]

lemma matrixTrace_eq_linearTrace {d : ℕ} (D : Op d) :
    Matrix.trace (opMatrix D) = LinearMap.trace ℝ (Euclid d) D.toLinearMap := by
  rw [opMatrix_eq_toMatrix]
  exact (LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis D.toLinearMap).symm

lemma compress_trace {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D)
    (hsupp : ∀ x, D x ∈ LinearMap.range V.toLinearMap) :
    Matrix.trace (opMatrix (compress V D)) = Matrix.trace (opMatrix D) := by
  have hleft : V.toContinuousLinearMap.comp (V.toContinuousLinearMap.adjoint.comp D) = D := by
    apply ContinuousLinearMap.ext
    intro x
    exact projection_fixes_range V (D x) (hsupp x)
  rw [matrixTrace_eq_linearTrace, matrixTrace_eq_linearTrace]
  change LinearMap.trace ℝ (Euclid p)
      ((V.toContinuousLinearMap.adjoint.toLinearMap.comp D.toLinearMap).comp V.toLinearMap) = _
  rw [LinearMap.trace_comp_comm']
  exact congrArg (fun T : Op d => LinearMap.trace ℝ (Euclid d) T.toLinearMap) hleft

lemma compress_quadratic {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D)
    (hsupp : ∀ x, D x ∈ LinearMap.range V.toLinearMap) (x : Euclid d) :
    ⟪D x,x⟫_ℝ =
      ⟪compress V D (V.toContinuousLinearMap.adjoint x),V.toContinuousLinearMap.adjoint x⟫_ℝ := by
  have h := congrArg (fun T : Op d => T x) (compression_reconstruction V D hD hsupp)
  change V (compress V D (V.toContinuousLinearMap.adjoint x)) = D x at h
  rw [← h]
  exact (V.toContinuousLinearMap.adjoint_inner_right
    (compress V D (V.toContinuousLinearMap.adjoint x)) x).symm

/-- Compression preserves the actual centered quadratic observable exactly. -/
theorem compressed_measurement_row {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D)
    (hsupp : ∀ x, D x ∈ LinearMap.range V.toLinearMap) (x : Euclid d) :
    (GaussianEllipsoid.quadratic (opMatrix D) (fun i => x i)-Matrix.trace (opMatrix D))/Real.sqrt 2 =
      (GaussianEllipsoid.quadratic (opMatrix (compress V D))
        (fun i => V.toContinuousLinearMap.adjoint x i)-Matrix.trace (opMatrix (compress V D)))/Real.sqrt 2 := by
  change (dotProduct (fun i => x i) ((opMatrix D).mulVec (fun i => x i)) - _) / _ =
    (dotProduct (fun i => V.toContinuousLinearMap.adjoint x i)
      ((opMatrix (compress V D)).mulVec (fun i => V.toContinuousLinearMap.adjoint x i)) - _) / _
  rw [opMatrix_quadratic, opMatrix_quadratic, compress_trace V D hD hsupp]
  congr 2
  exact compress_quadratic V D hD hsupp x

/-- The exact source-matrix diffuse norm constraints survive compression. -/
theorem compressed_diffuse_constraints {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D)
    (hsupp : ∀ x, D x ∈ LinearMap.range V.toLinearMap)
    (hF : ‖operatorFrobenius D‖ = 1) {τ : ℝ} (hOp : ‖D‖ ≤ τ) :
    (opMatrix (compress V D)).PosSemidef ∧
      frobeniusNorm (opMatrix (compress V D)) = 1 ∧
      matrixOpNorm (opMatrix (compress V D)) ≤ τ := by
  refine ⟨(opMatrix_posSemidef_iff _).mpr (compress_psd V D hD), ?_, ?_⟩
  · rw [frobeniusNorm_opMatrix, compress_frobenius_norm V D hD hsupp, hF]
  · rw [matrixOpNorm_opMatrix]
    exact (compress_opNorm_le V D).trans hOp

#print axioms compressed_measurement_row
#print axioms compressed_diffuse_constraints
end UCEscape
