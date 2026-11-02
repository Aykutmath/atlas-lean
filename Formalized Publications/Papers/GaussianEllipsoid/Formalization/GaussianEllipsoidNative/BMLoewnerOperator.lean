import BMGaussianFeasibilityTransfer
import BMHighProbabilityBox

noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open BMUniformMoment BMSymmetricFiniteUniversality GaussianEllipsoid BMGeometry

namespace BMBoxRiskAssembly

/-- The genuine Loewner box, realized as symmetric Euclidean operators. -/
def operatorBox (d : ℕ) (lo hi : ℝ) : Set (SymOp d) :=
  {T | matrixOf T ∈ BMRescaling.spectralBox d lo hi}

/-- A Loewner-box matrix is Hermitian, independently of the signs of its endpoints. -/
theorem spectralBox_isHermitian {d : ℕ} {lo hi : ℝ}
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ BMRescaling.spectralBox d lo hi) :
    S.IsHermitian := by
  have hI : (lo • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian := by
    simp [Matrix.IsHermitian]
  simpa only [sub_add_cancel] using hS.1.1.add hI

theorem spectralBox_transpose {d : ℕ} {lo hi : ℝ}
    {S : Matrix (Fin d) (Fin d) ℝ} (hS : S ∈ BMRescaling.spectralBox d lo hi) :
    S.transpose = S := by
  simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
    spectralBox_isHermitian hS

/-- The inverse coordinate realization of any matrix in a genuine Loewner box. -/
def operatorOfBox {d : ℕ} {lo hi : ℝ} (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S ∈ BMRescaling.spectralBox d lo hi) : SymOp d :=
  ⟨(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) S, by
    change ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) S).toLinearMap.IsSymmetric
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    exact Matrix.isHermitian_iff_isSymmetric.mp (spectralBox_isHermitian hS)⟩

@[simp] theorem matrixOf_operatorOfBox {d : ℕ} {lo hi : ℝ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S ∈ BMRescaling.spectralBox d lo hi) :
    matrixOf (operatorOfBox S hS) = S := by
  exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm_apply_apply S

theorem operatorOfBox_mem {d : ℕ} {lo hi : ℝ}
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S ∈ BMRescaling.spectralBox d lo hi) :
    operatorOfBox S hS ∈ operatorBox d lo hi := by
  change matrixOf (operatorOfBox S hS) ∈ BMRescaling.spectralBox d lo hi
  simpa only [matrixOf_operatorOfBox] using hS

/-- The two existing coordinate maps describe exactly the same operator matrix. -/
theorem matrixOf_eq_opMatrix {d : ℕ} (T : SymOp d) : matrixOf T = opMatrix T.val := by
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).injective
  change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (matrixOf T) =
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)) (opMatrix T.val)
  rw [toEuclideanCLM_matrixOf]
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, opMatrix_toEuclideanLin]

/-- The scalar identity matrix belongs to every correctly ordered box. -/
theorem lower_identity_mem_spectralBox (d : ℕ) {lo hi : ℝ} (hlohi : lo ≤ hi) :
    lo • (1 : Matrix (Fin d) (Fin d) ℝ) ∈ BMRescaling.spectralBox d lo hi := by
  letI : StarOrderedRing ℝ := RCLike.toStarOrderedRing
  constructor
  · simpa only [sub_self] using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin d) (Fin d) ℝ).PosSemidef)
  · rw [← sub_smul]
    exact BMRescaling.posSemidef_smul Matrix.PosSemidef.one (sub_nonneg.mpr hlohi)

/-- The lower-endpoint identity witnesses nonemptiness, including in dimension zero. -/
theorem operatorBox_nonempty (d : ℕ) {lo hi : ℝ} (_hlo : 0 < lo) (hlohi : lo ≤ hi) :
    (operatorBox d lo hi).Nonempty :=
  ⟨operatorOfBox _ (lower_identity_mem_spectralBox d hlohi),
    operatorOfBox_mem _ (lower_identity_mem_spectralBox d hlohi)⟩

/-- A genuine positive Loewner box supplies the dimension-free operator-norm bound. -/
theorem operatorBox_norm_le {d : ℕ} {lo hi : ℝ} {T : SymOp d}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hT : T ∈ operatorBox d lo hi) : ‖T‖ ≤ hi := by
  have hbox : opMatrix T.val ∈ BMRescaling.spectralBox d lo hi := by
    simpa only [operatorBox, Set.mem_setOf_eq, matrixOf_eq_opMatrix] using hT
  have hp : IsPSD T.val := (opMatrix_posSemidef_iff _).mp
    (BMRescaling.box_posSemidef hlo hbox)
  have hu : IsPSD (hi • ContinuousLinearMap.id ℝ (Euclid d) - T.val) := by
    apply (opMatrix_posSemidef_iff _).mp
    simpa only [opMatrix_sub, opMatrix_smul, opMatrix_id] using hbox.2
  let b := T.property.eigenvectorBasis finrank_euclideanSpace_fin
  let a := T.property.eigenvalues finrank_euclideanSpace_fin
  have hae (i : Fin d) : T.val (b i) = a i • b i :=
    T.property.apply_eigenvectorBasis finrank_euclideanSpace_fin i
  have ha (i : Fin d) : 0 ≤ a i ∧ a i ≤ hi := by
    constructor
    · exact eigenvalue_nonneg hp i
    · have h := hu.2 (b i)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left, hae,
        real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one] at h
      linarith
  change ‖T.val‖ ≤ hi
  apply ContinuousLinearMap.opNorm_le_bound _ (hlo.trans hlohi)
  intro x
  have hc (i : Fin d) : b.repr (T.val x) i = a i * b.repr x i := by
    rw [b.repr_apply_apply, ← T.property.apply_clm, hae, real_inner_smul_left,
      b.repr_apply_apply]
  have hs : ‖T.val x‖ ^ 2 ≤ (hi * ‖x‖) ^ 2 := by
    rw [mul_pow, ← repr_sq_sum b (T.val x), ← repr_sq_sum b x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [hc, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (ha i).1 (hlo.trans hlohi)).mpr (ha i).2) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hlo.trans hlohi) (norm_nonneg x))).mp hs

end BMBoxRiskAssembly

#print axioms BMBoxRiskAssembly.spectralBox_isHermitian
#print axioms BMBoxRiskAssembly.matrixOf_operatorOfBox
#print axioms BMBoxRiskAssembly.operatorBox_nonempty
#print axioms BMBoxRiskAssembly.operatorBox_norm_le
