import FrobeniusFactorCover
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
open Set Metric Module
open scoped BigOperators InnerProductSpace

namespace GaussianEllipsoid

abbrev Euclid (r : ℕ) := EuclideanSpace ℝ (Fin r)

/-- A column matrix regarded as an actual Euclidean continuous linear map. -/
def frobeniusOperator {r q : ℕ} (A : FrobeniusMatrix r q) : Euclid q →L[ℝ] Euclid r :=
  LinearMap.toContinuousLinearMap ((EuclideanSpace.basisFun (Fin q) ℝ).toBasis.constr ℝ (fun j => A j))

/-- An operator's ordinary coordinate columns, with Frobenius norm. -/
def operatorFrobenius {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) : FrobeniusMatrix r q :=
  (WithLp.equiv 2 _).symm (fun j => T (EuclideanSpace.basisFun (Fin q) ℝ j))

@[simp] theorem frobeniusOperator_basis {r q : ℕ} (A : FrobeniusMatrix r q) (j : Fin q) :
    frobeniusOperator A (EuclideanSpace.basisFun (Fin q) ℝ j) = A j := by
  exact (EuclideanSpace.basisFun (Fin q) ℝ).toBasis.constr_basis ℝ _ j

@[simp] theorem operatorFrobenius_apply {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (j : Fin q) :
    operatorFrobenius T j = T (EuclideanSpace.basisFun (Fin q) ℝ j) := rfl

@[simp] theorem operatorFrobenius_frobeniusOperator {r q : ℕ} (A : FrobeniusMatrix r q) :
    operatorFrobenius (frobeniusOperator A) = A := by
  ext j i
  exact congrArg (fun x : Euclid r => x i) (frobeniusOperator_basis A j)

@[simp] theorem frobeniusOperator_operatorFrobenius {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    frobeniusOperator (operatorFrobenius T) = T := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin q) ℝ).toBasis.ext
  intro j
  exact frobeniusOperator_basis (operatorFrobenius T) j

/-- Frobenius energy is independent of the chosen orthonormal domain basis. -/
theorem sum_norm_sq_operator_basis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) :
    ∑ j, ‖T (b j)‖ ^ 2 = ‖operatorFrobenius T‖ ^ 2 := by
  let d := EuclideanSpace.basisFun (Fin r) ℝ
  have key (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) :
      ∑ j, ‖T (b j)‖ ^ 2 = ∑ i, ‖ContinuousLinearMap.adjoint T (d i)‖ ^ 2 := by
    calc
      ∑ j, ‖T (b j)‖ ^ 2 = ∑ j, ∑ i, ‖⟪d i, T (b j)⟫_ℝ‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        exact (d.sum_sq_norm_inner_right _).symm
      _ = ∑ i, ∑ j, ‖⟪b j, ContinuousLinearMap.adjoint T (d i)⟫_ℝ‖ ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
      _ = ∑ i, ‖ContinuousLinearMap.adjoint T (d i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact b.sum_sq_norm_inner_right _
  rw [key, ← key (EuclideanSpace.basisFun (Fin q) ℝ), PiLp.norm_sq_eq_of_L2]
  rfl

/-- The Gram operator `T* T` is self-adjoint. -/
def gramSymmetric {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    (ContinuousLinearMap.adjoint T ∘L T).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪ContinuousLinearMap.adjoint T (T x), y⟫_ℝ =
    ⟪x, ContinuousLinearMap.adjoint T (T y)⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- Right singular vectors, as the actual spectral basis of the Gram operator. -/
def rightSingularBasis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    OrthonormalBasis (Fin q) ℝ (Euclid q) :=
  (gramSymmetric T).eigenvectorBasis finrank_euclideanSpace_fin

/-- Squared singular values are the eigenvalues of `T* T`. -/
def gramEigenvalue {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) : ℝ :=
  (gramSymmetric T).eigenvalues finrank_euclideanSpace_fin i

/-- Singular values have their standard spectral meaning. -/
def singularValue {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) : ℝ :=
  Real.sqrt (gramEigenvalue T i)

/-- The nuclear norm, explicitly the sum of singular values. -/
def spectralNuclearNorm {r q : ℕ} (A : FrobeniusMatrix r q) : ℝ :=
  ∑ i, singularValue (frobeniusOperator A) i

theorem gramEigenvalue_eq_norm_sq {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    gramEigenvalue T i = ‖T (rightSingularBasis T i)‖ ^ 2 := by
  have heig := (gramSymmetric T).apply_eigenvectorBasis finrank_euclideanSpace_fin i
  have h := congrArg (fun x => ⟪x, rightSingularBasis T i⟫_ℝ) heig
  change ⟪ContinuousLinearMap.adjoint T (T (rightSingularBasis T i)), rightSingularBasis T i⟫_ℝ =
    ⟪(gramEigenvalue T i) • rightSingularBasis T i, rightSingularBasis T i⟫_ℝ at h
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
    real_inner_smul_left, real_inner_self_eq_norm_sq,
    (rightSingularBasis T).norm_eq_one i] at h
  simpa using h.symm

@[simp] theorem singularValue_eq_norm {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    singularValue T i = ‖T (rightSingularBasis T i)‖ := by
  rw [singularValue, gramEigenvalue_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Nuclear/Frobenius comparison follows from the actual Gram spectrum. -/
theorem frobenius_le_spectralNuclear {r q : ℕ} (A : FrobeniusMatrix r q) :
    ‖A‖ ≤ spectralNuclearNorm A := by
  have hsq : ‖A‖ ^ 2 = ∑ i, (singularValue (frobeniusOperator A) i) ^ 2 := by
    simp only [singularValue_eq_norm]
    rw [sum_norm_sq_operator_basis, operatorFrobenius_frobeniusOperator]
  have hnonneg : ∀ i : Fin q, 0 ≤ singularValue (frobeniusOperator A) i := by
    intro i; exact Real.sqrt_nonneg _
  have hsum := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (fun i _ => hnonneg i)
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => hnonneg i))).mp
  simpa only [spectralNuclearNorm, hsq] using hsum


/-- Ordering permutation for the singular values, largest first. -/
def singularOrder {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) : Equiv.Perm (Fin q) :=
  Tuple.sort (fun i => -singularValue T i)

def orderedSingularValue {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) : ℝ :=
  singularValue T (singularOrder T i)

def orderedSingularBasis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    OrthonormalBasis (Fin q) ℝ (Euclid q) :=
  (rightSingularBasis T).reindex (singularOrder T).symm

theorem orderedSingularValue_antitone {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    Antitone (orderedSingularValue T) := by
  intro i j hij
  have := Tuple.monotone_sort (fun i => -singularValue T i) hij
  exact neg_le_neg_iff.mp this

@[simp] theorem orderedSingularValue_nonneg {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) : 0 ≤ orderedSingularValue T i :=
  Real.sqrt_nonneg _

@[simp] theorem norm_orderedSingularBasis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    ‖T (orderedSingularBasis T i)‖ = orderedSingularValue T i := by
  simp only [orderedSingularBasis, OrthonormalBasis.reindex_apply, Equiv.symm_symm,
    orderedSingularValue, singularValue_eq_norm]

theorem sum_orderedSingularValue {r q : ℕ} (A : FrobeniusMatrix r q) :
    ∑ i, orderedSingularValue (frobeniusOperator A) i = spectralNuclearNorm A := by
  exact Equiv.sum_comp (singularOrder (frobeniusOperator A)) _

/-- Restrict an operator to a chosen set of orthonormal domain directions. -/
def basisBlock {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) (I : Finset (Fin q)) :
    Euclid q →L[ℝ] Euclid r := ∑ i ∈ I, (innerSL ℝ (b i)).smulRight (T (b i))

theorem basisBlock_apply {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) (I : Finset (Fin q)) (x : Euclid q) :
    basisBlock T b I x = ∑ i ∈ I, ⟪b i, x⟫_ℝ • T (b i) := by
  simp [basisBlock]

@[simp] theorem basisBlock_basis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) (I : Finset (Fin q)) (j : Fin q) :
    basisBlock T b I (b j) = if j ∈ I then T (b j) else 0 := by
  classical
  rw [basisBlock_apply]
  simp only [orthonormal_iff_ite.mp b.orthonormal, ite_smul, one_smul, zero_smul]
  exact Finset.sum_ite_eq' I j (fun i => T (b i))

@[simp] theorem basisBlock_univ {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) : basisBlock T b Finset.univ = T := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro j
  change basisBlock T b Finset.univ (b j) = T (b j)
  simp only [basisBlock_basis, Finset.mem_univ, if_true]

theorem norm_basisBlock_sq {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) (I : Finset (Fin q)) :
    ‖operatorFrobenius (basisBlock T b I)‖ ^ 2 = ∑ i ∈ I, ‖T (b i)‖ ^ 2 := by
  classical
  rw [← sum_norm_sq_operator_basis _ b]
  simp only [basisBlock_basis, apply_ite norm, norm_zero, ite_pow,
    zero_pow (by norm_num : 2 ≠ 0)]
  simp

theorem rank_basisBlock_le {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) (I : Finset (Fin q)) :
    (frobeniusToMatrix (operatorFrobenius (basisBlock T b I))).rank ≤ I.card := by
  classical
  rw [rank_frobeniusToMatrix]
  let S := Submodule.span ℝ (↑(I.image (fun i => T (b i))) : Set (Euclid r))
  have hspan : columnSpan (operatorFrobenius (basisBlock T b I)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change basisBlock T b I (EuclideanSpace.basisFun (Fin q) ℝ j) ∈ S
    rw [basisBlock_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  exact (Submodule.finrank_mono hspan).trans
    ((finrank_span_finset_le_card (I.image (fun i => T (b i)))).trans Finset.card_image_le)

end GaussianEllipsoid

#print axioms GaussianEllipsoid.sum_norm_sq_operator_basis
#print axioms GaussianEllipsoid.gramEigenvalue_eq_norm_sq
#print axioms GaussianEllipsoid.frobenius_le_spectralNuclear

#print axioms GaussianEllipsoid.orderedSingularValue_antitone
#print axioms GaussianEllipsoid.norm_basisBlock_sq
#print axioms GaussianEllipsoid.rank_basisBlock_le
