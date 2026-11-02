import SpectralFrobenius

noncomputable section
open Set Module
open scoped BigOperators InnerProductSpace NNReal
namespace GaussianEllipsoid

@[simp] theorem operatorFrobenius_add {r q : ℕ} (S T : Euclid q →L[ℝ] Euclid r) :
    operatorFrobenius (S + T) = operatorFrobenius S + operatorFrobenius T := by ext j i; rfl

/-- Hilbert-Schmidt pairing is independent of the orthonormal domain basis. -/
theorem sum_inner_operator_basis {r q : ℕ} (S T : Euclid q →L[ℝ] Euclid r)
    (b : OrthonormalBasis (Fin q) ℝ (Euclid q)) :
    ∑ i, ⟪S (b i), T (b i)⟫_ℝ = ⟪operatorFrobenius S, operatorFrobenius T⟫_ℝ := by
  have h := sum_norm_sq_operator_basis (S + T) b
  simp only [ContinuousLinearMap.add_apply, operatorFrobenius_add, norm_add_sq_real,
    Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [sum_norm_sq_operator_basis S b, sum_norm_sq_operator_basis T b] at h
  linarith

/-- Distinct images of right singular vectors are orthogonal, including singular
zero directions. -/
theorem inner_rightSingular_images {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (i j : Fin q) (hij : i ≠ j) :
    ⟪T (rightSingularBasis T i), T (rightSingularBasis T j)⟫_ℝ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have heig := (gramSymmetric T).apply_eigenvectorBasis finrank_euclideanSpace_fin j
  change ContinuousLinearMap.adjoint T (T (rightSingularBasis T j)) =
    (gramEigenvalue T j) • rightSingularBasis T j at heig
  rw [heig, real_inner_smul_right, (rightSingularBasis T).inner_eq_zero hij, mul_zero]

/-- Pythagoras for arbitrary real coefficients and pairwise orthogonal vectors. -/
theorem norm_orthogonal_sum_sq {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ι → E)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) (a : ι → ℝ) :
    ‖∑ i, a i • v i‖ ^ 2 = ∑ i, (a i) ^ 2 * ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]; ring
  · intro j _ hji
    rw [horth j i hji, mul_zero, mul_zero]
  · simp

/-- The polar partial-isometry images, with zero mapped to zero. -/
def polarImage {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) : Euclid r :=
  (singularValue T i)⁻¹ • T (rightSingularBasis T i)

theorem polarImage_norm_le {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    ‖polarImage T i‖ ≤ 1 := by
  rw [polarImage, norm_smul, Real.norm_eq_abs, singularValue_eq_norm,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  by_cases h : ‖T (rightSingularBasis T i)‖ = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem polarImage_orthogonal {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r)
    (i j : Fin q) (hij : i ≠ j) : ⟪polarImage T i, polarImage T j⟫_ℝ = 0 := by
  rw [polarImage, polarImage, real_inner_smul_left, real_inner_smul_right,
    inner_rightSingular_images T i j hij, mul_zero, mul_zero]

def polarWitness {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) : Euclid q →L[ℝ] Euclid r :=
  LinearMap.toContinuousLinearMap ((rightSingularBasis T).toBasis.constr ℝ (polarImage T))

@[simp] theorem polarWitness_basis {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    polarWitness T (rightSingularBasis T i) = polarImage T i :=
  (rightSingularBasis T).toBasis.constr_basis ℝ _ i

/-- The actual polar witness is an operator contraction. -/
theorem norm_polarWitness_le {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    ‖polarWitness T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  have hrepr : polarWitness T x = ∑ i, (rightSingularBasis T).repr x i • polarImage T i := by
    conv_lhs => rw [← (rightSingularBasis T).sum_repr x]
    simp only [map_sum, map_smul, polarWitness_basis]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [hrepr, norm_orthogonal_sum_sq _ (polarImage_orthogonal T)]
  calc
    ∑ i, ((rightSingularBasis T).repr x i) ^ 2 * ‖polarImage T i‖ ^ 2 ≤
        ∑ i, ((rightSingularBasis T).repr x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := pow_le_pow_left₀ (norm_nonneg _) (polarImage_norm_le T i) 2
      simpa using mul_le_mul_of_nonneg_left hi (sq_nonneg _)
    _ = ‖x‖ ^ 2 := by
      have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin q => ℝ) ((rightSingularBasis T).repr x)
      simp only [Real.norm_eq_abs, sq_abs, LinearIsometryEquiv.norm_map] at h
      exact h.symm

theorem inner_polarImage {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) (i : Fin q) :
    ⟪T (rightSingularBasis T i), polarImage T i⟫_ℝ = singularValue T i := by
  rw [polarImage, real_inner_smul_right, real_inner_self_eq_norm_sq, singularValue_eq_norm]
  by_cases h : ‖T (rightSingularBasis T i)‖ = 0
  · simp [h]
  · field_simp

/-- Exact nuclear pairing with an operator-contractive polar witness. -/
theorem inner_polarWitness_eq_nuclear {r q : ℕ} (A : FrobeniusMatrix r q) :
    ⟪A, operatorFrobenius (polarWitness (frobeniusOperator A))⟫_ℝ = spectralNuclearNorm A := by
  rw [← operatorFrobenius_frobeniusOperator A,
    ← sum_inner_operator_basis _ _ (rightSingularBasis (frobeniusOperator A))]
  simp only [frobeniusOperator_operatorFrobenius, polarWitness_basis, inner_polarImage,
    spectralNuclearNorm]

/-- Every operator contraction is dominated by the true singular-value sum. -/
theorem inner_operator_le_nuclear {r q : ℕ} (A : FrobeniusMatrix r q)
    (W : Euclid q →L[ℝ] Euclid r) (hW : ‖W‖ ≤ 1) :
    ⟪A, operatorFrobenius W⟫_ℝ ≤ spectralNuclearNorm A := by
  rw [← operatorFrobenius_frobeniusOperator A,
    ← sum_inner_operator_basis _ _ (rightSingularBasis (frobeniusOperator A))]
  simp only [spectralNuclearNorm, frobeniusOperator_operatorFrobenius, singularValue_eq_norm]
  apply Finset.sum_le_sum
  intro i _
  have hnorm : ‖W (rightSingularBasis (frobeniusOperator A) i)‖ ≤ 1 := by
    calc
      ‖W (rightSingularBasis (frobeniusOperator A) i)‖ ≤
          ‖W‖ * ‖rightSingularBasis (frobeniusOperator A) i‖ := W.le_opNorm _
      _ ≤ 1 := by simpa only [(rightSingularBasis _).norm_eq_one, mul_one] using hW
  exact (real_inner_le_norm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))

/-- Exact operator-dual characterization, proved using the actual polar witness. -/
theorem spectralNuclear_le_iff {r q : ℕ} (A : FrobeniusMatrix r q) (c : ℝ) :
    spectralNuclearNorm A ≤ c ↔
      ∀ W : Euclid q →L[ℝ] Euclid r, ‖W‖ ≤ 1 → ⟪A, operatorFrobenius W⟫_ℝ ≤ c := by
  constructor
  · intro h W hW
    exact (inner_operator_le_nuclear A W hW).trans h
  · intro h
    simpa only [inner_polarWitness_eq_nuclear] using
      h (polarWitness (frobeniusOperator A)) (norm_polarWitness_le _)


@[simp] theorem operatorFrobenius_neg {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    operatorFrobenius (-T) = -operatorFrobenius T := by ext j i; rfl

theorem spectralNuclear_nonneg {r q : ℕ} (A : FrobeniusMatrix r q) :
    0 ≤ spectralNuclearNorm A := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)

@[simp] theorem spectralNuclear_zero (r q : ℕ) : spectralNuclearNorm (0 : FrobeniusMatrix r q) = 0 := by
  apply le_antisymm _ (spectralNuclear_nonneg _)
  apply (spectralNuclear_le_iff _ _).mpr
  intro W hW
  simp

theorem spectralNuclear_add_le {r q : ℕ} (A B : FrobeniusMatrix r q) :
    spectralNuclearNorm (A + B) ≤ spectralNuclearNorm A + spectralNuclearNorm B := by
  apply (spectralNuclear_le_iff _ _).mpr
  intro W hW
  rw [inner_add_left]
  exact add_le_add (inner_operator_le_nuclear A W hW) (inner_operator_le_nuclear B W hW)

theorem abs_inner_operator_le_nuclear {r q : ℕ} (A : FrobeniusMatrix r q)
    (W : Euclid q →L[ℝ] Euclid r) (hW : ‖W‖ ≤ 1) :
    |⟪A, operatorFrobenius W⟫_ℝ| ≤ spectralNuclearNorm A := by
  apply abs_le.mpr
  constructor
  · have h := inner_operator_le_nuclear A (-W) (by simpa only [norm_neg] using hW)
    simpa only [operatorFrobenius_neg, inner_neg_right, neg_le] using h
  · exact inner_operator_le_nuclear A W hW

theorem spectralNuclear_smul_le {r q : ℕ} (c : ℝ) (A : FrobeniusMatrix r q) :
    spectralNuclearNorm (c • A) ≤ |c| * spectralNuclearNorm A := by
  apply (spectralNuclear_le_iff _ _).mpr
  intro W hW
  rw [real_inner_smul_left]
  calc
    c * ⟪A, operatorFrobenius W⟫_ℝ ≤ |c * ⟪A, operatorFrobenius W⟫_ℝ| := le_abs_self _
    _ = |c| * |⟪A, operatorFrobenius W⟫_ℝ| := abs_mul _ _
    _ ≤ |c| * spectralNuclearNorm A :=
      mul_le_mul_of_nonneg_left (abs_inner_operator_le_nuclear A W hW) (abs_nonneg c)

@[simp] theorem spectralNuclear_smul {r q : ℕ} (c : ℝ) (A : FrobeniusMatrix r q) :
    spectralNuclearNorm (c • A) = |c| * spectralNuclearNorm A := by
  apply le_antisymm (spectralNuclear_smul_le c A)
  by_cases hc : c = 0
  · simp [hc]
  have h := spectralNuclear_smul_le c⁻¹ (c • A)
  rw [inv_smul_smul₀ hc, abs_inv] at h
  have h' : spectralNuclearNorm A ≤ spectralNuclearNorm (c • A) / |c| := by
    simpa only [div_eq_mul_inv, mul_comm] using h
  simpa only [mul_comm] using (le_div_iff₀ (abs_pos.mpr hc)).mp h'

@[simp] theorem spectralNuclear_neg {r q : ℕ} (A : FrobeniusMatrix r q) :
    spectralNuclearNorm (-A) = spectralNuclearNorm A := by
  simpa using spectralNuclear_smul (-1) A

@[simp] theorem spectralNuclear_eq_zero_iff {r q : ℕ} (A : FrobeniusMatrix r q) :
    spectralNuclearNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    exact norm_eq_zero.mp (le_antisymm (h ▸ frobenius_le_spectralNuclear A) (norm_nonneg _))
  · rintro rfl; exact spectralNuclear_zero r q

/-- A finite-dimensional Lipschitz bound useful for measurability. -/
theorem spectralNuclear_le_dim_mul_frobenius {r q : ℕ} (A : FrobeniusMatrix r q) :
    spectralNuclearNorm A ≤ q * ‖A‖ := by
  have hsq : ∑ i, (singularValue (frobeniusOperator A) i) ^ 2 = ‖A‖ ^ 2 := by
    simp only [singularValue_eq_norm]
    rw [sum_norm_sq_operator_basis, operatorFrobenius_frobeniusOperator]
  have hpoint (i : Fin q) : singularValue (frobeniusOperator A) i ≤ ‖A‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
    rw [← hsq]
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin q => (singularValue (frobeniusOperator A) j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  calc
    spectralNuclearNorm A ≤ ∑ i : Fin q, ‖A‖ := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = q * ‖A‖ := by simp

/-- The actual singular-value nuclear norm is continuous. -/
theorem continuous_spectralNuclear (r q : ℕ) :
    Continuous (spectralNuclearNorm : FrobeniusMatrix r q → ℝ) := by
  refine (show LipschitzWith (q : ℝ≥0)
    (spectralNuclearNorm : FrobeniusMatrix r q → ℝ) from ?_).continuous
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro A B
  have h1 := spectralNuclear_add_le (A - B) B
  have h2 := spectralNuclear_add_le (B - A) A
  simp only [sub_add_cancel] at h1 h2
  have hn : spectralNuclearNorm (B - A) = spectralNuclearNorm (A - B) := by
    rw [← neg_sub A B, spectralNuclear_neg]
  rw [hn] at h2
  have hab : |spectralNuclearNorm A - spectralNuclearNorm B| ≤ spectralNuclearNorm (A - B) := by
    apply abs_le.mpr; constructor <;> linarith
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_natCast] using
    hab.trans (spectralNuclear_le_dim_mul_frobenius (A - B))

end GaussianEllipsoid
#print axioms GaussianEllipsoid.norm_polarWitness_le
#print axioms GaussianEllipsoid.inner_polarWitness_eq_nuclear
#print axioms GaussianEllipsoid.spectralNuclear_le_iff

#print axioms GaussianEllipsoid.spectralNuclear_add_le
#print axioms GaussianEllipsoid.spectralNuclear_smul
#print axioms GaussianEllipsoid.continuous_spectralNuclear
