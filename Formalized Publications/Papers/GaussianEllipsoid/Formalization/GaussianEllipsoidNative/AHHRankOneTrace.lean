import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-! Rank-one trace gluing is algebraic and does not require unit vectors. -/
noncomputable section
open scoped BigOperators Matrix
namespace AHH

variable {n R : Type*} [Fintype n] [CommSemiring R]

theorem rankOne_trace_mul (u v : n → R) (A B : Matrix n n R) :
    Matrix.trace (Matrix.vecMulVec u v * A) * Matrix.trace (Matrix.vecMulVec u v * B) =
      Matrix.trace (Matrix.vecMulVec u v * A * Matrix.vecMulVec u v * B) := by
  rw [Matrix.mul_assoc (Matrix.vecMulVec u v * A) (Matrix.vecMulVec u v) B,
    Matrix.vecMulVec_mul u v A, Matrix.vecMulVec_mul u v B,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec,
    Matrix.trace_vecMulVec, Matrix.trace_vecMulVec]
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_comm]

theorem rankOne_trace_glue (u v : n → R) (U V X Y : Matrix n n R) :
    Matrix.trace (U * Matrix.vecMulVec u v * V) *
        Matrix.trace (X * Matrix.vecMulVec u v * Y) =
      Matrix.trace (U * Matrix.vecMulVec u v * Y * X * Matrix.vecMulVec u v * V) := by
  have hleft : Matrix.trace (U * Matrix.vecMulVec u v * V) =
      Matrix.trace (Matrix.vecMulVec u v * (V * U)) := by
    rw [Matrix.trace_mul_cycle]
    rw [Matrix.trace_mul_comm]
  have hright : Matrix.trace (X * Matrix.vecMulVec u v * Y) =
      Matrix.trace (Matrix.vecMulVec u v * (Y * X)) := by
    rw [Matrix.trace_mul_cycle]
    rw [Matrix.trace_mul_comm]
  rw [hleft, hright, rankOne_trace_mul]
  calc
    _ = Matrix.trace ((V * U * Matrix.vecMulVec u v * (Y * X)) * Matrix.vecMulVec u v) := by
      convert Matrix.trace_mul_comm (Matrix.vecMulVec u v)
        (V * U * Matrix.vecMulVec u v * (Y * X)) using 1 <;>
        simp only [Matrix.mul_assoc]
    _ = _ := by
      convert Matrix.trace_mul_comm V
        (U * Matrix.vecMulVec u v * Y * X * Matrix.vecMulVec u v) using 1 <;>
        simp only [Matrix.mul_assoc]

end AHH
