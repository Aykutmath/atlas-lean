import AdaptiveSpectralPeeling

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

/-- Restrict to the first `j` genuine spectral directions. -/
def spectralHead {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (j : ℕ) : Op d :=
  spectralOp b (fun i => if i.val < j then a i else 0)

/-- The remaining genuine spectral directions. -/
def spectralTail {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (j : ℕ) : Op d :=
  spectralOp b (fun i => if j ≤ i.val then a i else 0)

theorem spectralHead_add_tail {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (j : ℕ) : spectralHead b a j + spectralTail b a j = spectralOp b a := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  change spectralHead b a j (b i) + spectralTail b a j (b i) = spectralOp b a (b i)
  simp only [spectralHead, spectralTail, spectralOp_basis]
  by_cases h : i.val < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.le_of_not_gt h]

theorem spectralHead_psd {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (j : ℕ) : IsPSD (spectralHead b a j) := by
  apply spectralOp_positive
  intro i
  split_ifs <;> simp_all

theorem spectralTail_psd {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (j : ℕ) : IsPSD (spectralTail b a j) := by
  apply spectralOp_positive
  intro i
  split_ifs <;> simp_all

theorem spectralHead_comp_tail {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (j : ℕ) : (spectralHead b a j).comp (spectralTail b a j) = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  change spectralHead b a j (spectralTail b a j (b i)) = 0
  simp only [spectralHead, spectralTail, spectralOp_basis, map_smul]
  by_cases h : i.val < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h]

theorem spectralHead_tail_ranges_orthogonal {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) (j : ℕ)
    (x y : Euclid d) : ⟪spectralHead b a j x, spectralTail b a j y⟫_ℝ = 0 := by
  have hs : (spectralHead b a j).toLinearMap.IsSymmetric :=
    spectralOp_symmetric b (fun i => if i.val < j then a i else 0)
  have hc := congrArg (fun T : Op d => T y) (spectralHead_comp_tail b a j)
  change spectralHead b a j (spectralTail b a j y) = 0 at hc
  rw [hs.apply_clm, hc, inner_zero_right]

theorem spectralHead_tail_frobenius_orthogonal {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) (j : ℕ) :
    ⟪operatorFrobenius (spectralHead b a j), operatorFrobenius (spectralTail b a j)⟫_ℝ = 0 := by
  rw [spectralHead, spectralTail, spectralOp_pairing]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i.val < j
  · simp [h, Nat.not_le.mpr h]
  · simp [h]

theorem spectralHead_eq_basisBlock {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) (j : ℕ) :
    spectralHead b a j = basisBlock (spectralOp b a) b (prefixIndices d j) := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  change spectralHead b a j (b i) = basisBlock (spectralOp b a) b (prefixIndices d j) (b i)
  simp [spectralHead, basisBlock_basis, mem_prefixIndices, ite_smul]

theorem spectralHead_rank_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) (j : ℕ) :
    (frobeniusToMatrix (operatorFrobenius (spectralHead b a j))).rank ≤ j := by
  rw [spectralHead_eq_basisBlock]
  exact (rank_basisBlock_le _ _ _).trans (card_prefixIndices_le d j)

/-- The head range is contained in the span of its j retained spectral images. -/
theorem spectralHead_range_finrank_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) (j : ℕ) :
    Module.finrank ℝ (LinearMap.range (spectralHead b a j).toLinearMap) ≤ j := by
  classical
  rw [spectralHead_eq_basisBlock]
  let I := prefixIndices d j
  let T := spectralOp b a
  let V := Submodule.span ℝ (↑(I.image (fun i => T (b i))) : Set (Euclid d))
  have hv : LinearMap.range (basisBlock T b I).toLinearMap ≤ V := by
    rintro y ⟨x,rfl⟩
    change basisBlock T b I x ∈ V
    rw [basisBlock_apply]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  exact (Submodule.finrank_mono hv).trans
    ((finrank_span_finset_le_card (I.image (fun i => T (b i)))).trans
      (Finset.card_image_le.trans (card_prefixIndices_le d j)))

theorem spectralTail_frobenius_sq {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) (j : ℕ) :
    ‖operatorFrobenius (spectralTail b a j)‖^2 = spectralTailEnergy a j := by
  simp only [spectralTail, spectralOp_frobenius_sq, spectralTailEnergy, ite_pow,
    zero_pow (by omega : 2 ≠ 0)]

/-- The operator norm of an actual diagonal operator is bounded by the coefficient cap. -/
theorem norm_spectralOp_le {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) {c : ℝ} (hc : 0 ≤ c) (ha : ∀ i, |a i| ≤ c) :
    ‖spectralOp b a‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg x))).mp
  rw [spectralOp_apply, norm_orthogonal_sum_sq b (fun i j hij => b.inner_eq_zero hij)]
  simp only [b.norm_eq_one, one_pow, mul_one, mul_pow]
  have hx : ∑ i, (b.repr x i)^2 = ‖x‖^2 := by
    have h := PiLp.norm_sq_eq_of_L2 (fun _ : Fin d => ℝ) (b.repr x)
    simpa only [Real.norm_eq_abs, sq_abs, LinearIsometryEquiv.norm_map] using h.symm
  rw [← hx, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : (a i)^2 ≤ c^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a i)) hc).2 (ha i)
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (b.repr x i))]

theorem paddedEigenvalue_nonneg {d : ℕ} (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) (j : ℕ) :
    0 ≤ paddedEigenvalue a j := by
  unfold paddedEigenvalue
  split_ifs <;> simp_all

theorem spectralTail_norm_le {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hanti : Antitone a) (j : ℕ) :
    ‖spectralTail b a j‖ ≤ paddedEigenvalue a j := by
  apply norm_spectralOp_le b _ (paddedEigenvalue_nonneg a ha j)
  intro i
  by_cases hi : j ≤ i.val
  · have hj : j < d := lt_of_le_of_lt hi i.isLt
    simp only [if_pos hi, paddedEigenvalue, dif_pos hj, abs_of_nonneg (ha i)]
    exact hanti (show (⟨j,hj⟩ : Fin d) ≤ i from hi)
  · simp only [if_neg hi, abs_zero]
    exact paddedEigenvalue_nonneg a ha j

end BMGeometry
