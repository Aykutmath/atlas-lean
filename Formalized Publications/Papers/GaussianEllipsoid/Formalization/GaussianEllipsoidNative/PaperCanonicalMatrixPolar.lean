import PaperCanonicalPolarFull

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace BigOperators
namespace GaussianEllipsoid.PaperCanonicalPolar

/-- Exact Moore-Penrose half-inverse action on every positive eigenspace. -/
theorem inverseRoot_positive_eigenvector {q : ℕ} (S : Mat q q) (hS : S.IsHermitian)
    (v : Fin q → ℝ) (ev : ℝ) (hev : 0<ev) (hv : S*ᵥv=ev • v) :
    inverseRoot S*ᵥv=ev^(-(1/2:ℝ)) • v := by
  simpa only [inverseRoot,Real.sqrt_eq_rpow,Real.rpow_neg hev.le] using
    cfc_mulVec_eigenvector S hS (fun x => (Real.sqrt x)⁻¹) v ev hv

/-- The half-inverse is zero on the kernel, as prescribed in the source. -/
theorem inverseRoot_kernel {q : ℕ} (S : Mat q q) (hS : S.IsHermitian)
    (v : Fin q → ℝ) (hv : S*ᵥv=0) : inverseRoot S*ᵥv=0 := by
  have h := cfc_mulVec_eigenvector S hS (fun x => (Real.sqrt x)⁻¹) v 0
    (by simpa using hv)
  simpa only [inverseRoot,Real.sqrt_zero,inv_zero,zero_smul] using h

theorem canonicalPolar_source_formula {r q : ℕ} (M : Mat r q) :
    canonicalPolar M=M*inverseRoot (M.transpose*M) := by
  simp only [canonicalPolar,Matrix.conjTranspose_eq_transpose_of_trivial]

def matrixOperator {r q : ℕ} (M : Mat r q) : Euclid q →L[ℝ] Euclid r :=
  (Matrix.toEuclideanLin M).toContinuousLinearMap

@[simp] lemma matrixOperator_apply {r q : ℕ} (M : Mat r q) (x : Euclid q) (i : Fin r) :
    matrixOperator M x i=∑ j,M i j*x j := rfl

lemma matrixOperator_square {q : ℕ} (M : Mat q q) : matrixOperator M=euclideanEquiv q M := by
  ext x i
  rfl

lemma matrixOperator_mul {r q k : ℕ} (M : Mat r q) (N : Mat q k) :
    matrixOperator (M*N)=matrixOperator M ∘L matrixOperator N := by
  ext x i
  change ((M*N)*ᵥ(fun j => x j)) i=(M*ᵥ(N*ᵥ(fun j => x j))) i
  rw [Matrix.mulVec_mulVec]

lemma matrixOperator_adjoint {r q : ℕ} (M : Mat r q) :
    matrixOperator Mᴴ=(matrixOperator M).adjoint := by
  unfold matrixOperator
  rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint,LinearMap.adjoint_toContinuousLinearMap]

/-- Explicit rectangular-matrix bridge for the literal M(MᵀM)^(dagger/2) formula. -/
theorem matrix_canonical_polar_eq_operator {r q : ℕ} (M : Mat r q) :
    matrixOperator (canonicalPolar M)=polarWitness (matrixOperator M) := by
  have hg : euclideanEquiv q (Mᴴ*M)=(matrixOperator M).adjoint ∘L matrixOperator M := by
    rw [← matrixOperator_square,matrixOperator_mul,matrixOperator_adjoint]
  have hs : (euclideanEquiv q).symm ((matrixOperator M).adjoint ∘L matrixOperator M)=Mᴴ*M := by
    rw [← hg,StarAlgEquiv.symm_apply_apply]
  rw [← canonicalOperator_eq_polarWitness]
  unfold canonicalPolar canonicalOperator
  rw [hs,matrixOperator_mul,matrixOperator_square]

lemma matrixOperator_norm {r q : ℕ} (M : Mat r q) : ‖matrixOperator M‖=‖M‖ :=
  (Matrix.l2_opNorm_def M).symm

theorem canonicalPolar_norm_le_one {r q : ℕ} (M : Mat r q) : ‖canonicalPolar M‖≤1 := by
  rw [← matrixOperator_norm,matrix_canonical_polar_eq_operator]
  exact norm_polarWitness_le _

lemma matrixOperator_basis_apply {r q : ℕ} (M : Mat r q) (i : Fin r) (j : Fin q) :
    matrixOperator M (EuclideanSpace.basisFun (Fin q) ℝ j) i=M i j := by
  simp [matrixOperator_apply,EuclideanSpace.basisFun_apply,PiLp.single_apply]

lemma matrix_frobenius_pairing {r q : ℕ} (A B : Mat r q) :
    ⟪operatorFrobenius (matrixOperator A),operatorFrobenius (matrixOperator B)⟫_ℝ=
      ∑ i,∑ j,A i j*B i j := by
  change (∑ j,∑ i, matrixOperator B (EuclideanSpace.basisFun (Fin q) ℝ j) i*
    matrixOperator A (EuclideanSpace.basisFun (Fin q) ℝ j) i)=_
  simp_rw [matrixOperator_basis_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Literal entrywise Frobenius pairing attains the exact nuclear norm. -/
theorem canonicalPolar_pairing {r q : ℕ} (M : Mat r q) :
    (∑ i,∑ j,canonicalPolar M i j*M i j)=spectralNuclearNorm (operatorFrobenius (matrixOperator M)) := by
  rw [← matrix_frobenius_pairing,matrix_canonical_polar_eq_operator]
  exact canonical_polar_pairing _

#print axioms matrix_canonical_polar_eq_operator
#print axioms canonicalPolar_norm_le_one
#print axioms canonicalPolar_pairing
end GaussianEllipsoid.PaperCanonicalPolar
