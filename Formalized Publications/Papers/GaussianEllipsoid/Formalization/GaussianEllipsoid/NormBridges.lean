/-
Matrix norm bridges: Frobenius, operator, and nuclear norms.

The paper works with `‖A‖_F`, `‖A‖_op`, and `‖A‖_*` (defined variationally
as `sup_{‖W‖_op ≤ 1} ⟨W,A⟩`) on real symmetric matrices. This file provides
the three norms with the identities the threshold chains need: trace/inner
forms, rank-one evaluations, submultiplicativity, compression bounds, and
the symmetric quadratic-form characterization of the operator norm.

Spectral facts (PSD square roots, eigenvalue characterizations, and
`‖D‖_* = Tr D` for PSD `D`) are deferred to the Section 5 module, which
will carry the diagonalization machinery.

Mathematical source: paper.tex, Sections 2, 5, and 13.
-/
import GaussianEllipsoid.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section

namespace GaussianEllipsoid

/-! ### Euclidean norm on coordinate vectors -/

/-- Euclidean (`ℓ²`) norm of a real coordinate vector, as an explicit
square root (the ambient `‖·‖` on pi types is the sup norm). -/
def euclidNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- Square of the Euclidean norm. -/
theorem euclidNorm_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (euclidNorm x) ^ 2 = ∑ i, (x i) ^ 2 := by
  unfold euclidNorm
  rw [Real.sq_sqrt]
  apply Finset.sum_nonneg
  intro i _
  exact sq_nonneg _

/-- The Euclidean norm is nonnegative. -/
theorem euclidNorm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ euclidNorm x := by
  unfold euclidNorm
  exact Real.sqrt_nonneg _

/-! ### Frobenius norm -/

section Frobenius

open scoped Matrix Matrix.Norms.Frobenius

/-- The Frobenius norm on square real matrices. -/
def frobeniusNorm {d : Nat} (A : Square d) : ℝ := ‖A‖

/-- Square of the Frobenius norm as a coordinate sum. -/
theorem frobeniusNorm_sq {d : Nat} (A : Square d) :
    (frobeniusNorm A) ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  have hnn : 0 ≤ (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hsq : ((∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2
      = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hnn,
      show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
  unfold frobeniusNorm
  rw [Matrix.frobenius_norm_def, hsq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- The Frobenius norm is nonnegative. -/
theorem frobeniusNorm_nonneg {d : Nat} (A : Square d) :
    0 ≤ frobeniusNorm A := by
  unfold frobeniusNorm
  exact norm_nonneg _

/-- The Frobenius norm vanishes only at zero. -/
theorem frobeniusNorm_eq_zero_iff {d : Nat} (A : Square d) :
    frobeniusNorm A = 0 ↔ A = 0 := by
  unfold frobeniusNorm
  exact norm_eq_zero

/-- Triangle inequality for the Frobenius norm. -/
theorem frobeniusNorm_add_le {d : Nat} (A B : Square d) :
    frobeniusNorm (A + B) ≤ frobeniusNorm A + frobeniusNorm B := by
  unfold frobeniusNorm
  exact norm_add_le _ _

/-- The Frobenius norm is homogeneous. -/
theorem frobeniusNorm_smul {d : Nat} (c : ℝ) (A : Square d) :
    frobeniusNorm (c • A) = ‖c‖ * frobeniusNorm A := by
  unfold frobeniusNorm
  exact norm_smul _ _

/-- Submultiplicativity of the Frobenius norm. -/
theorem frobeniusNorm_mul_le {d : Nat} (A B : Square d) :
    frobeniusNorm (A * B) ≤ frobeniusNorm A * frobeniusNorm B := by
  unfold frobeniusNorm
  exact Matrix.frobenius_norm_mul _ _

/-- The Frobenius norm is transpose-invariant. -/
theorem frobeniusNorm_transpose {d : Nat} (A : Square d) :
    frobeniusNorm Aᵀ = frobeniusNorm A := by
  unfold frobeniusNorm
  exact Matrix.frobenius_norm_transpose _

/-- Squared Frobenius norm as a trace. -/
theorem frobeniusNorm_sq_eq_trace {d : Nat} (A : Square d) :
    (frobeniusNorm A) ^ 2 = Matrix.trace (Aᵀ * A) := by
  rw [frobeniusNorm_sq]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cauchy-Schwarz for the Frobenius inner product. -/
theorem frobenius_inner_le {d : Nat} (A B : Square d) :
    (∑ i, ∑ j, A i j * B i j) ≤ frobeniusNorm A * frobeniusNorm B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d × Fin d))
    (fun ij : Fin d × Fin d => A ij.1 ij.2) (fun ij : Fin d × Fin d => B ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at hcs
  have hsq : (∑ i, ∑ j, A i j * B i j) ^ 2 ≤ (frobeniusNorm A * frobeniusNorm B) ^ 2 := by
    rw [mul_pow, frobeniusNorm_sq, frobeniusNorm_sq]
    exact hcs
  have hnn : 0 ≤ frobeniusNorm A * frobeniusNorm B :=
    mul_nonneg (frobeniusNorm_nonneg _) (frobeniusNorm_nonneg _)
  have habs : |∑ i, ∑ j, A i j * B i j| ≤ frobeniusNorm A * frobeniusNorm B :=
    abs_le_of_sq_le_sq hsq hnn
  exact (le_abs_self _).trans habs

/-- Frobenius norm of a rank-one matrix, squared form. -/
theorem frobeniusNorm_vecMulVec_sq {d : Nat} (u v : Vector d) :
    (frobeniusNorm (Matrix.vecMulVec u v)) ^ 2
      = (∑ i, (u i) ^ 2) * (∑ i, (v i) ^ 2) := by
  rw [frobeniusNorm_sq]
  simp only [Matrix.vecMulVec_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Row-major flattening of a square matrix. -/
def matrixFlatten {d : Nat} (A : Square d) : Fin d × Fin d → ℝ :=
  fun ij => A ij.1 ij.2

/-- Row-vectorization isometry for the Frobenius norm. -/
theorem frobeniusNorm_eq_euclidNorm_flatten {d : Nat} (A : Square d) :
    frobeniusNorm A = euclidNorm (matrixFlatten A) := by
  have hsq : (frobeniusNorm A) ^ 2 = (euclidNorm (matrixFlatten A)) ^ 2 := by
    rw [frobeniusNorm_sq, euclidNorm_sq]
    unfold matrixFlatten
    rw [Fintype.sum_prod_type]
  have ha := frobeniusNorm_nonneg A
  have hb := euclidNorm_nonneg (matrixFlatten A)
  conv_lhs => rw [← Real.sqrt_sq ha]
  conv_rhs => rw [← Real.sqrt_sq hb]
  rw [hsq]

end Frobenius

/-! ### Euclidean homogeneity and Cauchy-Schwarz -/

/-- The Euclidean norm is homogeneous. -/
theorem euclidNorm_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    euclidNorm (c • x) = |c| * euclidNorm x := by
  have hsq : (euclidNorm (c • x)) ^ 2 = (|c| * euclidNorm x) ^ 2 := by
    rw [mul_pow, euclidNorm_sq, euclidNorm_sq, sq_abs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Pi.smul_apply, mul_pow]
  have ha := euclidNorm_nonneg (c • x)
  have hb : 0 ≤ |c| * euclidNorm x :=
    mul_nonneg (abs_nonneg _) (euclidNorm_nonneg _)
  conv_lhs => rw [← Real.sqrt_sq ha]
  conv_rhs => rw [← Real.sqrt_sq hb]
  rw [hsq]

/-- Cauchy-Schwarz for coordinate dot products against Euclidean norms. -/
theorem dotProduct_abs_le_euclidNorm {d : Nat} (x y : Vector d) :
    |x ⬝ᵥ y| ≤ euclidNorm x * euclidNorm y := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) x y
  have hsq : (x ⬝ᵥ y) ^ 2 ≤ (euclidNorm x * euclidNorm y) ^ 2 := by
    rw [mul_pow, euclidNorm_sq, euclidNorm_sq]
    simp only [dotProduct]
    exact hcs
  have hnn : 0 ≤ euclidNorm x * euclidNorm y :=
    mul_nonneg (euclidNorm_nonneg _) (euclidNorm_nonneg _)
  exact abs_le_of_sq_le_sq hsq hnn

/-! ### Operator norm -/

section OpNorm

open scoped Matrix Matrix.Norms.L2Operator

/-- The `ℓ²` operator norm on square real matrices. -/
def matrixOpNorm {d : Nat} (A : Square d) : ℝ := ‖A‖

/-- Bridge: Euclidean norm is the norm of `toLp`. -/
theorem euclidNorm_eq_norm_toLp {d : Nat} (v : Vector d) :
    euclidNorm v = ‖WithLp.toLp 2 v‖ := by
  unfold euclidNorm
  rw [PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  show (v i) ^ 2 = ‖(WithLp.toLp 2 v) i‖ ^ 2
  rw [show (WithLp.toLp 2 v) i = v i from rfl, Real.norm_eq_abs, sq_abs]

/-- Operator-norm bound from a Euclidean pointwise bound (the single
transfer point from `euclidNorm` to the L2-operator norm). -/
theorem matrixOpNorm_le_of_euclid_le {d : Nat} {A : Square d} {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ x : Vector d, euclidNorm (A *ᵥ x) ≤ M * euclidNorm x) :
    matrixOpNorm A ≤ M := by
  unfold matrixOpNorm
  rw [Matrix.l2_opNorm_def]
  apply ContinuousLinearMap.opNorm_le_bound
    (f := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A) hM
  intro y
  show ‖WithLp.toLp 2 (A *ᵥ (WithLp.ofLp y))‖ ≤ M * ‖WithLp.toLp 2 (WithLp.ofLp y)‖
  rw [← euclidNorm_eq_norm_toLp, ← euclidNorm_eq_norm_toLp]
  exact h _

/-- The operator norm is nonnegative. -/
theorem matrixOpNorm_nonneg {d : Nat} (A : Square d) :
    0 ≤ matrixOpNorm A := by
  unfold matrixOpNorm
  exact norm_nonneg _

/-- The operator norm vanishes only at zero. -/
theorem matrixOpNorm_eq_zero_iff {d : Nat} (A : Square d) :
    matrixOpNorm A = 0 ↔ A = 0 := by
  unfold matrixOpNorm
  exact norm_eq_zero

/-- Negation preserves the operator norm. -/
theorem matrixOpNorm_neg {d : Nat} (A : Square d) :
    matrixOpNorm (-A) = matrixOpNorm A := by
  unfold matrixOpNorm
  exact norm_neg _

/-- Triangle inequality for the operator norm. -/
theorem matrixOpNorm_add_le {d : Nat} (A B : Square d) :
    matrixOpNorm (A + B) ≤ matrixOpNorm A + matrixOpNorm B := by
  unfold matrixOpNorm
  exact norm_add_le _ _

/-- The operator norm is homogeneous. -/
theorem matrixOpNorm_smul {d : Nat} (c : ℝ) (A : Square d) :
    matrixOpNorm (c • A) = ‖c‖ * matrixOpNorm A := by
  unfold matrixOpNorm
  exact norm_smul _ _

/-- Submultiplicativity of the operator norm. -/
theorem matrixOpNorm_mul_le {d : Nat} (A B : Square d) :
    matrixOpNorm (A * B) ≤ matrixOpNorm A * matrixOpNorm B := by
  unfold matrixOpNorm
  exact Matrix.l2_opNorm_mul _ _

/-- Over the reals, conjugate transpose is transpose. -/
theorem real_conjTranspose_eq_transpose {d : Nat} (A : Square d) :
    Aᴴ = Aᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]

/-- The C* identity in transpose form. -/
theorem matrixOpNorm_transpose_mul_self {d : Nat} (A : Square d) :
    matrixOpNorm (Aᵀ * A) = matrixOpNorm A * matrixOpNorm A := by
  unfold matrixOpNorm
  rw [← real_conjTranspose_eq_transpose]
  exact Matrix.l2_opNorm_conjTranspose_mul_self _

/-- Operator-norm bound on matrix-vector products (Euclidean norms). -/
theorem matrixOpNorm_mulVec_le {d : Nat} (A : Square d) (x : Vector d) :
    euclidNorm (A *ᵥ x) ≤ matrixOpNorm A * euclidNorm x := by
  have h := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have h' : ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 x‖ := h
  unfold matrixOpNorm
  rw [euclidNorm_eq_norm_toLp, euclidNorm_eq_norm_toLp]
  exact h'

/-- Quadratic forms are bounded by the operator norm. -/
theorem quadratic_abs_le_opNorm_mul_sq {d : Nat} (A : Square d) (x : Vector d) :
    |quadratic A x| ≤ matrixOpNorm A * (euclidNorm x) ^ 2 := by
  have hcs := dotProduct_abs_le_euclidNorm x (A *ᵥ x)
  have hmv := matrixOpNorm_mulVec_le A x
  calc |quadratic A x| = |x ⬝ᵥ (A *ᵥ x)| := rfl
    _ ≤ euclidNorm x * euclidNorm (A *ᵥ x) := hcs
    _ ≤ euclidNorm x * (matrixOpNorm A * euclidNorm x) :=
        mul_le_mul_of_nonneg_left hmv (euclidNorm_nonneg _)
    _ = matrixOpNorm A * (euclidNorm x) ^ 2 := by ring

/-- Operator norm of a rank-one matrix. -/
theorem matrixOpNorm_vecMulVec {d : Nat} (u v : Vector d) :
    matrixOpNorm (Matrix.vecMulVec u v) = euclidNorm u * euclidNorm v := by
  have happly : ∀ x : Vector d,
      (Matrix.vecMulVec u v) *ᵥ x = (v ⬝ᵥ x) • u := by
    intro x
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply le_antisymm
  · apply matrixOpNorm_le_of_euclid_le
      (mul_nonneg (euclidNorm_nonneg _) (euclidNorm_nonneg _))
    intro x
    rw [happly, euclidNorm_smul]
    calc |v ⬝ᵥ x| * euclidNorm u
        ≤ (euclidNorm v * euclidNorm x) * euclidNorm u :=
          mul_le_mul_of_nonneg_right (dotProduct_abs_le_euclidNorm _ _)
            (euclidNorm_nonneg _)
      _ = (euclidNorm u * euclidNorm v) * euclidNorm x := by ring
  · by_cases hv : v = 0
    · subst hv
      have hz : Matrix.vecMulVec u (0 : Vector d) = (0 : Square d) := by
        ext i j
        simp [Matrix.vecMulVec_apply]
      have he : euclidNorm (0 : Vector d) = 0 := by
        unfold euclidNorm
        simp
      rw [hz, he, mul_zero]
      unfold matrixOpNorm
      simp
    · have hpos : 0 < euclidNorm v := by
        obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
          by_contra hall
          push Not at hall
          apply hv
          funext i
          exact hall i
        have hvi : 0 < (v i) ^ 2 := by
          rw [pow_two]
          exact mul_self_pos.mpr hi
        have hsum : 0 < ∑ i, (v i) ^ 2 :=
          Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ i, hvi⟩
        unfold euclidNorm
        exact Real.sqrt_pos.mpr hsum
      by_contra hlt
      push Not at hlt
      have hmv := matrixOpNorm_mulVec_le (Matrix.vecMulVec u v) v
      rw [happly] at hmv
      have hdot : v ⬝ᵥ v = ∑ i, (v i) ^ 2 := by simp [dotProduct, pow_two]
      have hsq : euclidNorm ((v ⬝ᵥ v) • u)
          = (∑ i, (v i) ^ 2) * euclidNorm u := by
        rw [euclidNorm_smul, hdot]
        rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      rw [hsq] at hmv
      have hlt' : (∑ i, (v i) ^ 2) * euclidNorm u
          < (euclidNorm u * euclidNorm v) * euclidNorm v :=
        lt_of_le_of_lt hmv (mul_lt_mul_of_pos_right hlt hpos)
      have hsqv : (∑ i, (v i) ^ 2) = (euclidNorm v) ^ 2 := (euclidNorm_sq v).symm
      have heq' : (euclidNorm u * euclidNorm v) * euclidNorm v
          = (∑ i, (v i) ^ 2) * euclidNorm u := by
        rw [hsqv]; ring
      rw [heq'] at hlt'
      exact lt_irrefl _ hlt'

/-- Compression bound from submultiplicativity. -/
theorem matrixOpNorm_comp_le {d : Nat} (X A Y : Square d) :
    matrixOpNorm (X * A * Y)
      ≤ matrixOpNorm X * matrixOpNorm A * matrixOpNorm Y := by
  calc matrixOpNorm (X * A * Y)
      ≤ matrixOpNorm (X * A) * matrixOpNorm Y :=
        matrixOpNorm_mul_le _ _
    _ ≤ (matrixOpNorm X * matrixOpNorm A) * matrixOpNorm Y :=
        mul_le_mul_of_nonneg_right (matrixOpNorm_mul_le _ _)
          (matrixOpNorm_nonneg _)

/-- The operator norm is bounded by the Frobenius norm. -/
theorem matrixOpNorm_le_frobeniusNorm {d : Nat} (A : Square d) :
    matrixOpNorm A ≤ frobeniusNorm A := by
  apply matrixOpNorm_le_of_euclid_le (frobeniusNorm_nonneg _)
  intro x
  have hrow : ∀ i : Fin d, ((A *ᵥ x) i) ^ 2
      ≤ (∑ j, (A i j) ^ 2) * (∑ k, (x k) ^ 2) := by
    intro i
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun j => A i j) (fun j => x j)
    show ((A *ᵥ x) i) ^ 2 ≤ _
    rw [show (A *ᵥ x) i = ∑ j, A i j * x j from rfl]
    exact hcs
  have hsq : (euclidNorm (A *ᵥ x)) ^ 2 ≤ (frobeniusNorm A * euclidNorm x) ^ 2 := by
    simp only [mul_pow, euclidNorm_sq, frobeniusNorm_sq]
    calc ∑ i, ((A *ᵥ x) i) ^ 2
        ≤ ∑ i, ((∑ j, (A i j) ^ 2) * (∑ k, (x k) ^ 2)) :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ = (∑ i, ∑ j, (A i j) ^ 2) * (∑ k, (x k) ^ 2) :=
          (Finset.sum_mul _ _ _).symm
  have hnn : 0 ≤ frobeniusNorm A * euclidNorm x :=
    mul_nonneg (frobeniusNorm_nonneg _) (euclidNorm_nonneg _)
  have habs := abs_le_of_sq_le_sq hsq hnn
  rwa [abs_of_nonneg (euclidNorm_nonneg _)] at habs

/-- The Frobenius norm is bounded by `√d` times the operator norm. -/
theorem frobeniusNorm_le_sqrt_mul_opNorm {d : Nat} (A : Square d) :
    frobeniusNorm A ≤ Real.sqrt d * matrixOpNorm A := by
  have hbasis : ∀ j : Fin d, euclidNorm (Pi.single j 1 : Vector d) = 1 := by
    intro j
    have h1 : (euclidNorm (Pi.single j 1 : Vector d)) ^ 2 = 1 := by
      rw [euclidNorm_sq]
      simp [Pi.single_apply]
    have hnn := euclidNorm_nonneg (Pi.single j 1 : Vector d)
    conv_lhs => rw [← Real.sqrt_sq hnn]
    rw [h1, Real.sqrt_one]
  have hcol : ∀ j : Fin d, A *ᵥ (Pi.single j 1 : Vector d) = fun i => A i j := by
    intro j
    rw [Matrix.mulVec_single_one]
    ext i
    simp [Matrix.col_apply]
  have hsq : (frobeniusNorm A) ^ 2 ≤ (Real.sqrt d * matrixOpNorm A) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), frobeniusNorm_sq]
    have hper : ∀ j : Fin d, (∑ i, (A i j) ^ 2) ≤ (matrixOpNorm A) ^ 2 := by
      intro j
      have hmv := matrixOpNorm_mulVec_le A (Pi.single j 1)
      rw [hcol j, hbasis j, mul_one] at hmv
      have h2 : (euclidNorm fun i => A i j) ^ 2 ≤ (matrixOpNorm A) ^ 2 :=
        pow_le_pow_left₀ (euclidNorm_nonneg _) hmv 2
      rw [euclidNorm_sq] at h2
      exact h2
    calc ∑ i, ∑ j, (A i j) ^ 2 = ∑ j, ∑ i, (A i j) ^ 2 := Finset.sum_comm
      _ ≤ ∑ j : Fin d, (matrixOpNorm A) ^ 2 := Finset.sum_le_sum (fun j _ => hper j)
      _ = (d : ℝ) * (matrixOpNorm A) ^ 2 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnn : 0 ≤ Real.sqrt d * matrixOpNorm A :=
    mul_nonneg (Real.sqrt_nonneg _) (matrixOpNorm_nonneg _)
  have habs := abs_le_of_sq_le_sq hsq hnn
  rwa [abs_of_nonneg (frobeniusNorm_nonneg _)] at habs

end OpNorm

section Nuclear

open scoped Matrix

/-! ### Nuclear norm, variational definition -/

/-- The operator norm of the zero matrix. -/
theorem matrixOpNorm_zero {d : Nat} : matrixOpNorm (0 : Square d) = 0 :=
  (matrixOpNorm_eq_zero_iff (0 : Square d)).mpr rfl

/-- Trace of `Uᵀ * A` as a Frobenius inner product. -/
theorem trace_transpose_mul_eq_inner {d : Nat} (U A : Square d) :
    Matrix.trace (Uᵀ * A) = ∑ i, ∑ j, U i j * A i j := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- The nuclear (trace) norm, defined variationally as the support function
of the operator-norm unit ball. This is the paper's working definition; no
spectral theory is needed for the Hölder direction or the upper bounds. -/
def nuclearNorm {d : Nat} (A : Square d) : ℝ :=
  sSup { t : ℝ | ∃ U : Square d,
    matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j }

/-- Pointwise bound for dual certificates. -/
theorem dual_inner_le_sqrt_mul_frobenius {d : Nat} (A U : Square d)
    (hU : matrixOpNorm U ≤ 1) :
    (∑ i, ∑ j, U i j * A i j) ≤ Real.sqrt d * frobeniusNorm A := by
  calc ∑ i, ∑ j, U i j * A i j
      ≤ frobeniusNorm U * frobeniusNorm A := frobenius_inner_le U A
    _ ≤ (Real.sqrt d * matrixOpNorm U) * frobeniusNorm A := by
        apply mul_le_mul_of_nonneg_right _ (frobeniusNorm_nonneg _)
        exact frobeniusNorm_le_sqrt_mul_opNorm U
    _ ≤ (Real.sqrt d * 1) * frobeniusNorm A := by
        apply mul_le_mul_of_nonneg_right _ (frobeniusNorm_nonneg _)
        apply mul_le_mul_of_nonneg_left hU (Real.sqrt_nonneg _)
    _ = Real.sqrt d * frobeniusNorm A := by ring

/-- The variational set is bounded above. -/
theorem nuclearNorm_bddAbove {d : Nat} (A : Square d) :
    BddAbove { t : ℝ | ∃ U : Square d,
      matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j } := by
  refine ⟨Real.sqrt d * frobeniusNorm A, ?_⟩
  rintro t ⟨U, hU, rfl⟩
  exact dual_inner_le_sqrt_mul_frobenius A U hU

/-- The variational set is nonempty (witnessed by `U = 0`). -/
theorem nuclearNorm_nonempty {d : Nat} (A : Square d) :
    { t : ℝ | ∃ U : Square d,
      matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j }.Nonempty := by
  refine ⟨0, (0 : Square d), ?_, ?_⟩
  · rw [matrixOpNorm_zero]
    exact zero_le_one
  · simp

/-- Hölder direction: every dual certificate lower-bounds the nuclear norm. -/
theorem nuclearNorm_lower {d : Nat} (A U : Square d) (hU : matrixOpNorm U ≤ 1) :
    (∑ i, ∑ j, U i j * A i j) ≤ nuclearNorm A := by
  have hmem : (∑ i, ∑ j, U i j * A i j) ∈ { t : ℝ | ∃ U : Square d,
      matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j } :=
    ⟨U, hU, rfl⟩
  exact le_csSup (nuclearNorm_bddAbove A) hmem

/-- The nuclear norm is nonnegative. -/
theorem nuclearNorm_nonneg {d : Nat} (A : Square d) : 0 ≤ nuclearNorm A := by
  have hmem : (0 : ℝ) ∈ { t : ℝ | ∃ U : Square d,
      matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j } :=
    ⟨(0 : Square d), by rw [matrixOpNorm_zero]; exact zero_le_one, by simp⟩
  exact le_csSup (nuclearNorm_bddAbove A) hmem

/-- The nuclear norm is bounded by `√d` times the Frobenius norm. -/
theorem nuclearNorm_le_sqrt_mul_frobenius {d : Nat} (A : Square d) :
    nuclearNorm A ≤ Real.sqrt d * frobeniusNorm A := by
  unfold nuclearNorm
  apply csSup_le (nuclearNorm_nonempty A)
  rintro t ⟨U, hU, rfl⟩
  exact dual_inner_le_sqrt_mul_frobenius A U hU

/-- The nuclear norm is bounded by `d` times the operator norm. -/
theorem nuclearNorm_le_card_mul_opNorm {d : Nat} (A : Square d) :
    nuclearNorm A ≤ d * matrixOpNorm A := by
  calc nuclearNorm A
      ≤ Real.sqrt d * frobeniusNorm A := nuclearNorm_le_sqrt_mul_frobenius A
    _ ≤ Real.sqrt d * (Real.sqrt d * matrixOpNorm A) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact frobeniusNorm_le_sqrt_mul_opNorm A
    _ = d * matrixOpNorm A := by
        rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- Triangle inequality for the variational nuclear norm. -/
theorem nuclearNorm_add_le {d : Nat} (A B : Square d) :
    nuclearNorm (A + B) ≤ nuclearNorm A + nuclearNorm B := by
  unfold nuclearNorm
  apply csSup_le (nuclearNorm_nonempty (A + B))
  rintro t ⟨U, hU, rfl⟩
  have hsplit : (∑ i, ∑ j, U i j * (A + B) i j)
      = (∑ i, ∑ j, U i j * A i j) + (∑ i, ∑ j, U i j * B i j) := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsplit]
  exact add_le_add (nuclearNorm_lower A U hU) (nuclearNorm_lower B U hU)

/-- Nonnegative homogeneity of the variational nuclear norm. -/
theorem nuclearNorm_smul_of_nonneg {d : Nat} (c : ℝ) (hc : 0 ≤ c)
    (A : Square d) :
    nuclearNorm (c • A) = c * nuclearNorm A := by
  have hpt : ∀ (U : Square d) (i j : Fin d),
      U i j * (c • A) i j = c * (U i j * A i j) := by
    intro U i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  apply le_antisymm
  · unfold nuclearNorm
    apply csSup_le (nuclearNorm_nonempty (c • A))
    rintro t ⟨U, hU, rfl⟩
    have hsplit : (∑ i, ∑ j, U i j * (c • A) i j)
        = c * (∑ i, ∑ j, U i j * A i j) := by
      simp only [hpt, ← Finset.mul_sum]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left (nuclearNorm_lower A U hU) hc
  · by_cases hc0 : c = 0
    · subst hc0
      rw [zero_mul, zero_smul]
      exact nuclearNorm_nonneg 0
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      have hmem : ∀ t ∈ {t : ℝ | ∃ U : Square d,
            matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j},
          c * t ≤ nuclearNorm (c • A) := by
        rintro t ⟨U, hU, rfl⟩
        have hsplit : c * (∑ i, ∑ j, U i j * A i j)
            = (∑ i, ∑ j, U i j * (c • A) i j) := by
          simp only [hpt, ← Finset.mul_sum]
        rw [hsplit]
        exact nuclearNorm_lower (c • A) U hU
      have hdiv : nuclearNorm A ≤ nuclearNorm (c • A) / c := by
        unfold nuclearNorm
        apply csSup_le (nuclearNorm_nonempty A)
        rintro t ⟨U, hU, rfl⟩
        rw [le_div_iff₀ hcpos, mul_comm]
        exact hmem _ ⟨U, hU, rfl⟩
      calc c * nuclearNorm A ≤ c * (nuclearNorm (c • A) / c) :=
            mul_le_mul_of_nonneg_left hdiv hc
        _ = nuclearNorm (c • A) := by field_simp

/-- Negation preserves the variational nuclear norm (via `U ↦ -U`,
using `matrixOpNorm_neg`). -/
theorem nuclearNorm_neg {d : Nat} (A : Square d) :
    nuclearNorm (-A) = nuclearNorm A := by
  unfold nuclearNorm
  have hset : {t : ℝ | ∃ U : Square d,
        matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * (-A) i j}
      = {t : ℝ | ∃ U : Square d,
        matrixOpNorm U ≤ 1 ∧ t = ∑ i, ∑ j, U i j * A i j} := by
    ext t
    constructor
    · rintro ⟨U, hU, rfl⟩
      refine ⟨-U, by rw [matrixOpNorm_neg]; exact hU, ?_⟩
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.neg_apply]
      ring
    · rintro ⟨U, hU, rfl⟩
      refine ⟨-U, by rw [matrixOpNorm_neg]; exact hU, ?_⟩
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.neg_apply]
      ring
  rw [hset]

end Nuclear

end GaussianEllipsoid
