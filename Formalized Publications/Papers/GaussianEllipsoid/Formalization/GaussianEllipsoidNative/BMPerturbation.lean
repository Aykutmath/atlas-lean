import BMConditionCone

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

theorem repr_sq_sum {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (x : Euclid d) :
    ∑ i, (b.repr x i)^2 = ‖x‖^2 := by
  have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ) (b.repr x)
  simpa only [Real.norm_eq_abs, sq_abs, LinearIsometryEquiv.norm_map] using! h.symm

theorem spectralOp_rayleigh_bounds {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) {lo hi : ℝ}
    (ha : ∀ i, lo ≤ a i ∧ a i ≤ hi) (x : Euclid d) :
    lo * ‖x‖^2 ≤ ⟪spectralOp b a x, x⟫_ℝ ∧
      ⟪spectralOp b a x, x⟫_ℝ ≤ hi * ‖x‖^2 := by
  rw [spectralOp_inner, ← repr_sq_sum b x, Finset.mul_sum, Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_right (ha i).1 (sq_nonneg (b.repr x i))]
  · apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_right (ha i).2 (sq_nonneg (b.repr x i))]

theorem eigenvalue_abs_le_opNorm {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) (i : Fin d) :
    |hT.eigenvalues finrank_euclideanSpace_fin i| ≤ ‖T‖ := by
  have h := T.le_opNorm (hT.eigenvectorBasis finrank_euclideanSpace_fin i)
  change ‖T.toLinearMap (hT.eigenvectorBasis finrank_euclideanSpace_fin i)‖ ≤
    ‖T‖ * ‖hT.eigenvectorBasis finrank_euclideanSpace_fin i‖ at h
  simpa only [hT.apply_eigenvectorBasis, norm_smul, Real.norm_eq_abs,
    (hT.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one, mul_one] using! h

theorem positivePart_rayleigh_bounds {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    (x : Euclid d) : 0 ≤ ⟪positivePart T hT x, x⟫_ℝ ∧
      ⟪positivePart T hT x, x⟫_ℝ ≤ ‖T‖ * ‖x‖^2 := by
  have h := spectralOp_rayleigh_bounds (hT.eigenvectorBasis finrank_euclideanSpace_fin)
    (fun i => max (hT.eigenvalues finrank_euclideanSpace_fin i) 0)
    (lo := 0) (hi := ‖T‖) (fun i => ⟨le_max_right _ _, max_le
      ((le_abs_self _).trans (eigenvalue_abs_le_opNorm T hT i)) (norm_nonneg T)⟩) x
  simpa only [zero_mul, positivePart] using! h

def perturb {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) (t : ℝ) : Op d :=
  positivePart T hT + t • (ContinuousLinearMap.id ℝ (Euclid d))

theorem isPSD_id (d : ℕ) : IsPSD (ContinuousLinearMap.id ℝ (Euclid d)) :=
  ⟨LinearMap.IsSymmetric.id, fun x => by simpa using (real_inner_self_nonneg (x := x))⟩

theorem perturb_positive {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) {t : ℝ} (ht : 0 ≤ t) :
    IsPSD (perturb T hT t) := (positivePart_positive T hT).add ((isPSD_id d).smul ht)

theorem perturb_rayleigh_bounds {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    (t : ℝ) (x : Euclid d) :
    t * ‖x‖^2 ≤ ⟪perturb T hT t x, x⟫_ℝ ∧
      ⟪perturb T hT t x, x⟫_ℝ ≤ (‖T‖ + t) * ‖x‖^2 := by
  have h := positivePart_rayleigh_bounds T hT x
  simp only [perturb, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  constructor <;> nlinarith

/-- Explicit bounded-condition witness: no limiting spectral law appears. -/
theorem perturb_mem_conditionCone {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    {t κ : ℝ} (ht : 0 ≤ t) (hκ : 0 ≤ κ) (hbound : ‖T‖ + t ≤ κ * t) :
    perturb T hT t ∈ conditionCone d κ := by
  refine ⟨perturb_positive T hT ht, ?_⟩
  intro x y hx hy
  have h1 := (perturb_rayleigh_bounds T hT t x).2
  have h2 := (perturb_rayleigh_bounds T hT t y).1
  rw [hx, one_pow, mul_one] at h1
  rw [hy, one_pow, mul_one] at h2
  exact h1.trans (hbound.trans (mul_le_mul_of_nonneg_left h2 hκ))

theorem frobenius_id_sq (d : ℕ) :
    ‖operatorFrobenius (ContinuousLinearMap.id ℝ (Euclid d))‖^2 = (d : ℝ) := by
  rw [← sum_norm_sq_operator_basis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp

theorem frobenius_id_norm (d : ℕ) :
    ‖operatorFrobenius (ContinuousLinearMap.id ℝ (Euclid d))‖ = Real.sqrt d := by
  rw [← frobenius_id_sq d, Real.sqrt_sq (norm_nonneg _)]

def opTrace {d : ℕ} (T : Op d) : ℝ :=
  ⟪operatorFrobenius T, operatorFrobenius (ContinuousLinearMap.id ℝ (Euclid d))⟫_ℝ

theorem perturb_pairing {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) (t : ℝ) :
    ⟪operatorFrobenius T, operatorFrobenius (perturb T hT t)⟫_ℝ =
      ‖operatorFrobenius (positivePart T hT)‖^2 + t * opTrace T := by
  simp only [perturb, operatorFrobenius_add, operatorFrobenius_smul,
    inner_add_right, real_inner_smul_right, positive_pairing, opTrace]

theorem perturb_norm_upper {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖operatorFrobenius (perturb T hT t)‖ ≤
      ‖operatorFrobenius (positivePart T hT)‖ + t * Real.sqrt d := by
  rw [perturb, operatorFrobenius_add, operatorFrobenius_smul]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    frobenius_id_norm])

theorem perturb_norm_lower {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖operatorFrobenius (positivePart T hT)‖ ≤ ‖operatorFrobenius (perturb T hT t)‖ := by
  have h := psd_pairing_nonneg (positivePart_positive T hT) ((isPSD_id d).smul ht)
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [perturb, operatorFrobenius_add, norm_add_sq_real]
  nlinarith [sq_nonneg ‖operatorFrobenius (t • ContinuousLinearMap.id ℝ (Euclid d))‖]

def normalize {d : ℕ} (S : Op d) : Op d := ‖operatorFrobenius S‖⁻¹ • S

theorem normalize_mem_conditionCone {d : ℕ} {κ : ℝ} {S : Op d}
    (hS : S ∈ conditionCone d κ) : normalize S ∈ conditionCone d κ :=
  conditionCone_smul (inv_nonneg.mpr (norm_nonneg _)) hS

theorem normalize_unit {d : ℕ} {S : Op d} (hS : operatorFrobenius S ≠ 0) :
    ‖operatorFrobenius (normalize S)‖ = 1 := by
  rw [normalize, operatorFrobenius_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hS)]

theorem normalized_perturb_pairing {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) (t : ℝ) :
    ⟪operatorFrobenius T, operatorFrobenius (normalize (perturb T hT t))⟫_ℝ =
      (‖operatorFrobenius (positivePart T hT)‖^2 + t * opTrace T) /
        ‖operatorFrobenius (perturb T hT t)‖ := by
  rw [normalize, operatorFrobenius_smul, real_inner_smul_right, perturb_pairing]
  ring

end BMGeometry
