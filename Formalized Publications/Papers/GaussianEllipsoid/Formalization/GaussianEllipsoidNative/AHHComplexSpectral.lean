import AHHAlgebraBridges
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHAlgebraBridges
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_hermitian_pow_diagonalization (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (m : ℕ) :
    A ^ m = (hA.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) ^ m) *
      star (hA.eigenvectorUnitary : Matrix ι ι ℂ) := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hA.spectral_theorem
  change A^m = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) ^ m) * star U
  induction m with
  | zero => simpa using hUU'.symm
  | succ m ih =>
    rw [pow_succ, ih]
    conv_lhs => arg 2; rw [hspec]
    calc
      _ = U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ) ^ m) * (star U * U) *
          Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * star U := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hUU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
        simp only [pow_succ]

/-- Every trace power of a Hermitian complex matrix is the real eigenvalue sum. -/
theorem complex_trace_pow_eq_eigenvalues (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (m : ℕ) :
    Matrix.trace (A ^ m) = ((∑ i, hA.eigenvalues i ^ m : ℝ) : ℂ) := by
  rw [complex_hermitian_pow_diagonalization A hA m, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp

theorem complex_trace_pow_im_zero (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (m : ℕ) : (Matrix.trace (A ^ m)).im = 0 := by
  rw [complex_trace_pow_eq_eigenvalues A hA m]
  rfl

theorem complex_posSemidef_trace_pow_nonneg (A : Matrix ι ι ℂ)
    (hA : A.PosSemidef) (m : ℕ) : 0 ≤ (Matrix.trace (A ^ m)).re := by
  rw [complex_trace_pow_eq_eigenvalues A hA.1 m]
  exact Finset.sum_nonneg (fun i _ => pow_nonneg (hA.eigenvalues_nonneg i) m)

theorem complex_hermitian_norm_eq_diagonal (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖A‖ = ‖Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))‖ := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hA.eigenvectorUnitary.prop),
    CStarRing.norm_coe_unitary_mul]
  rfl

/-- Exact complex PSD moment domination for the genuine Euclidean operator norm. -/
theorem complex_posSemidef_norm_pow_le_trace [Nonempty ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (m : ℕ) :
    ‖cMatrixCLM A‖ ^ m ≤ (Matrix.trace (A ^ m)).re := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty) hA.1.eigenvalues
  have hbound : ∀ j, hA.1.eigenvalues j ≤ hA.1.eigenvalues i := by
    intro j
    rw [← hmax]
    exact Finset.le_sup' _ (Finset.mem_univ j)
  have hn : ‖A‖ ≤ hA.1.eigenvalues i := by
    rw [complex_hermitian_norm_eq_diagonal A hA.1, Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).mpr
    intro j
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg j)]
      using hbound j
  rw [cMatrixCLM_norm, complex_trace_pow_eq_eigenvalues A hA.1 m]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn m).trans
    (Finset.single_le_sum (fun j _ => pow_nonneg (hA.eigenvalues_nonneg j) m) (Finset.mem_univ i))

/-- Continuity is in the ordinary finite-dimensional coordinate topology. -/
theorem continuous_cMatrixCLM_norm :
    Continuous (fun A : Matrix ι ι ℂ => ‖cMatrixCLM A‖) := by
  simp_rw [cMatrixCLM_norm]
  exact continuous_norm

theorem measurable_cMatrixCLM_norm [MeasurableSpace (Matrix ι ι ℂ)]
    [BorelSpace (Matrix ι ι ℂ)] :
    Measurable (fun A : Matrix ι ι ℂ => ‖cMatrixCLM A‖) :=
  continuous_cMatrixCLM_norm.measurable

end AHHAlgebraBridges
