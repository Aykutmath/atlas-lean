import BMPSDProjection
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open GaussianEllipsoid
namespace BMGeometry

def opMatrix {d : ℕ} (T : Op d) : Matrix (Fin d) (Fin d) ℝ :=
  frobeniusToMatrix (operatorFrobenius T)

theorem opMatrix_eq_toMatrix {d : ℕ} (T : Op d) : opMatrix T =
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis T.toLinearMap := by
  ext i j
  simp [opMatrix, frobeniusToMatrix, LinearMap.toMatrix_apply]

theorem opMatrix_toEuclideanLin {d : ℕ} (T : Op d) :
    Matrix.toEuclideanLin (opMatrix T) = T.toLinearMap := by
  rw [opMatrix_eq_toMatrix, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_toMatrix]

theorem opMatrix_quadratic {d : ℕ} (T : Op d) (x : Fin d → ℝ) :
    dotProduct x (opMatrix T *ᵥ x) =
      ⟪T ((WithLp.equiv 2 _).symm x), (WithLp.equiv 2 _).symm x⟫_ℝ := by
  rw [← ContinuousLinearMap.coe_coe, ← opMatrix_toEuclideanLin,
    Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- The operator PSD predicate is exactly Mathlib's matrix PosSemidef predicate. -/
theorem opMatrix_posSemidef_iff {d : ℕ} (T : Op d) : (opMatrix T).PosSemidef ↔ IsPSD T := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hT
    refine ⟨?_, ?_⟩
    · simpa only [opMatrix_toEuclideanLin] using Matrix.isHermitian_iff_isSymmetric.mp hT.1
    · intro x
      have h := hT.2 (WithLp.equiv 2 _ x)
      simpa only [star_trivial, opMatrix_quadratic, Equiv.symm_apply_apply] using h
  · intro hT
    refine ⟨Matrix.isHermitian_iff_isSymmetric.mpr (by simpa only [opMatrix_toEuclideanLin] using hT.1), ?_⟩
    intro x
    simpa only [star_trivial, opMatrix_quadratic] using hT.2 ((WithLp.equiv 2 _).symm x)

theorem opMatrix_trace {d : ℕ} (T : Op d) : Matrix.trace (opMatrix T) = opTrace T := by
  rw [opTrace, ← sum_inner_operator_basis _ _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  change T (EuclideanSpace.basisFun (Fin d) ℝ i) i =
    ⟪T (EuclideanSpace.basisFun (Fin d) ℝ i), EuclideanSpace.basisFun (Fin d) ℝ i⟫_ℝ
  rw [real_inner_comm, ← (EuclideanSpace.basisFun (Fin d) ℝ).repr_apply_apply]
  rfl

theorem matrix_positivePart_posSemidef {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    (opMatrix (positivePart T hT)).PosSemidef :=
  (opMatrix_posSemidef_iff _).mpr (positivePart_positive T hT)

/-- Positive matrices have nuclear norm equal to their ordinary matrix trace. -/
theorem matrix_nuclear_eq_trace {d : ℕ} (T : Op d) (hT : (opMatrix T).PosSemidef) :
    spectralNuclearNorm (operatorFrobenius T) = Matrix.trace (opMatrix T) := by
  rw [opMatrix_trace]
  exact nuclear_eq_trace_of_psd ((opMatrix_posSemidef_iff T).mp hT)

end BMGeometry
