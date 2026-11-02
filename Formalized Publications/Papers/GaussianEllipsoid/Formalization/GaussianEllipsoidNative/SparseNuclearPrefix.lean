import NuclearLowerMultiplication

noncomputable section
set_option maxHeartbeats 800000
open GaussianEllipsoid.SmallBall GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.SparseSupport

/-- Diagonal coefficient operator in genuine Euclidean coordinates. -/
def coefficientDiagonal {s : ℕ} (u : Fin s → ℝ) : Euclid s →L[ℝ] Euclid s :=
  matrixCLM (Matrix.diagonal u)

@[simp] theorem coefficientDiagonal_apply {s : ℕ} (u : Fin s → ℝ) (v : Euclid s) (i : Fin s) :
    coefficientDiagonal u v i = u i * v i := by
  change (Matrix.diagonal u).mulVec (fun j => v j) i = _
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal]

/-- A diagonal sign operator is a genuine Euclidean contraction. -/
theorem coefficientSign_contraction {s : ℕ} (u : Fin s → ℝ) :
    ‖coefficientDiagonal (fun i => if 0 ≤ u i then 1 else -1)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  simp only [coefficientDiagonal_apply]
  split_ifs <;> simp

/-- Diagonal nuclear norm is at least its coefficient ℓ1 mass, using an
explicit norm-one sign witness, not an assumed singular-value formula. -/
theorem l1_le_coefficientDiagonal_nuclear {s : ℕ} (u : Fin s → ℝ) :
    (∑ i, |u i|) ≤ spectralNuclearNorm (operatorFrobenius (coefficientDiagonal u)) := by
  let W := coefficientDiagonal (fun i => if 0 ≤ u i then 1 else -1)
  have hW : ‖W‖ ≤ 1 := coefficientSign_contraction u
  have hinner : ⟪operatorFrobenius (coefficientDiagonal u), operatorFrobenius W⟫_ℝ =
      ∑ i, |u i| := by
    simp only [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [RCLike.inner_apply, conj_trivial]
    change (∑ i, (W (EuclideanSpace.basisFun (Fin s) ℝ j)) i *
      (coefficientDiagonal u (EuclideanSpace.basisFun (Fin s) ℝ j)) i) = |u j|
    simp only [W, coefficientDiagonal_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply]
    simp only [mul_ite, mul_zero, mul_one, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs with hu
    · simp [abs_of_nonneg hu]
    · simp [abs_of_neg (lt_of_not_ge hu)]
  rw [← hinner]
  exact inner_operator_le_nuclear _ _ hW

/-- Sparse prefix operator in its exact rectangular-diagonal factorization. -/
def sparsePrefixOperator (d n : ℕ) (I : Finset (Fin n))
    (p : ((Fin (2*(d/4)) × Fin n) → ℝ) × ((Fin (2*(d/4)) × Fin n) → ℝ))
    (u : Fin I.card → ℝ) : Euclid (2*(d/4)) →L[ℝ] Euclid (2*(d/4)) :=
  (Real.sqrt (d : ℝ))⁻¹ •
    (supportOperator (2*(d/4)) n I p.1 ∘L coefficientDiagonal u ∘L
      ContinuousLinearMap.adjoint (supportOperator (2*(d/4)) n I p.2))

@[simp] theorem operatorFrobenius_smul_eq {r q : ℕ} (c : ℝ) (T : Euclid q →L[ℝ] Euclid r) :
    operatorFrobenius (c • T) = c • operatorFrobenius T := rfl

/-- Actual sparse nuclear prefix lower bound, simultaneous over all coefficients
and supports on the one concrete Gaussian event. -/
theorem sparseGood_prefix_nuclear_lower {d n m : ℕ} (hd : 24 ≤ d) {p}
    (hp : p ∈ sparseGood (2*(d/4)) n m) (I : Finset (Fin n)) (hI : I.card ≤ m)
    (u : Fin I.card → ℝ) :
    (Real.sqrt (d : ℝ))/12 * (∑ i, |u i|) ≤
      spectralNuclearNorm (operatorFrobenius (sparsePrefixOperator d n I p u)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hspos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hs : Real.sqrt (d : ℝ)^2 = d := Real.sq_sqrt hdR.le
  have hn := sparseGood_nuclear_lower hd hp I hI (coefficientDiagonal u)
  have hl1 := mul_le_mul_of_nonneg_left (l1_le_coefficientDiagonal_nuclear u)
    (show 0 ≤ (d : ℝ)/12 by positivity)
  have hh := mul_le_mul_of_nonneg_left (hl1.trans hn)
    (inv_nonneg.mpr hspos.le)
  simp only [sparsePrefixOperator, operatorFrobenius_smul_eq, spectralNuclear_smul,
    abs_of_nonneg (inv_nonneg.mpr hspos.le)]
  have heq : (Real.sqrt (d : ℝ))⁻¹ * ((d : ℝ)/12) = Real.sqrt (d : ℝ)/12 := by
    field_simp
    nlinarith [hs]
  simpa only [← mul_assoc, heq] using hh

/-- Coordinates of the actual restricted matrix-vector multiplication. -/
theorem supportOperator_apply (h n : ℕ) (I : Finset (Fin n))
    (x : (Fin h × Fin n) → ℝ) (v : Euclid I.card) (i : Fin h) :
    supportOperator h n I x v i =
      ∑ a : Fin I.card, x (i, (I.equivFin.symm a).val) * v a := rfl

/-- An actual submatrix column, with no distributional abstraction. -/
theorem supportOperator_basis_entry (h n : ℕ) (I : Finset (Fin n))
    (x : (Fin h × Fin n) → ℝ) (a : Fin I.card) (i : Fin h) :
    supportOperator h n I x (EuclideanSpace.basisFun (Fin I.card) ℝ a) i =
      x (i, (I.equivFin.symm a).val) := by
  rw [supportOperator_apply]
  simp [EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]

/-- Transpose coordinates of the actual submatrix. -/
theorem supportOperator_adjoint_basis_entry (h n : ℕ) (I : Finset (Fin n))
    (x : (Fin h × Fin n) → ℝ) (j : Fin h) (a : Fin I.card) :
    ContinuousLinearMap.adjoint (supportOperator h n I x)
      (EuclideanSpace.basisFun (Fin h) ℝ j) a = x (j, (I.equivFin.symm a).val) := by
  exact (operatorFrobenius_adjoint_entry (supportOperator h n I x) j a).trans
    (supportOperator_basis_entry h n I x a j)

/-- Exact entrywise identification with the scaled sum of rank-one Gaussian
atoms. `operatorFrobenius` is column-indexed, so j is the column and i the row. -/
theorem sparsePrefixOperator_entry (d n : ℕ) (I : Finset (Fin n))
    (p : ((Fin (2*(d/4)) × Fin n) → ℝ) × ((Fin (2*(d/4)) × Fin n) → ℝ))
    (u : Fin I.card → ℝ) (i j : Fin (2*(d/4))) :
    operatorFrobenius (sparsePrefixOperator d n I p u) j i =
      (Real.sqrt (d : ℝ))⁻¹ * ∑ a : Fin I.card,
        u a * p.1 (i, (I.equivFin.symm a).val) * p.2 (j, (I.equivFin.symm a).val) := by
  change (Real.sqrt (d : ℝ))⁻¹ *
    (supportOperator (2*(d/4)) n I p.1
      (coefficientDiagonal u
        (ContinuousLinearMap.adjoint (supportOperator (2*(d/4)) n I p.2)
          (EuclideanSpace.basisFun (Fin (2*(d/4))) ℝ j)))) i = _
  rw [supportOperator_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [coefficientDiagonal_apply, supportOperator_adjoint_basis_entry]
  ring

end GaussianEllipsoid.SparseSupport
