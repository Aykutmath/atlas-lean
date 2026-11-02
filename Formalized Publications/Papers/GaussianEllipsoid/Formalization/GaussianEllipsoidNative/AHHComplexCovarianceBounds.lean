import AHHAlgebraBridges
import AHHRealComplexNorm

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace AHHAlgebraBridges

/-- The literal unnormalized real two-factor covariance. -/
def realCov (n h : ℕ) (a b : Fin n → Fin h → ℝ) :
    Matrix (Fin h × Fin h) (Fin h × Fin h) ℝ :=
  ∑ i, Matrix.vecMulVec (fun p => a i p.1 * b i p.2)
    (fun p => a i p.1 * b i p.2)

theorem realCov_complex_eq (n h : ℕ) (a b : Fin n → Fin h → ℝ) :
    (realCov n h a b).map Complex.ofReal = ∑ i, projector (realTensor (a i) (b i)) := by
  ext p q
  simp [realCov, Matrix.sum_apply, projector, realTensor, Matrix.vecMulVec_apply, Complex.star_def]

theorem realCov_complex_posSemidef (n h : ℕ) (a b : Fin n → Fin h → ℝ) :
    ((realCov n h a b).map Complex.ofReal).PosSemidef := by
  rw [realCov_complex_eq]
  exact Matrix.posSemidef_sum _ (fun i _ => projector_posSemidef _)

/-- Four-sign cancellation after summing over every sample. -/
theorem four_sign_covariance_sum (n h : ℕ) (hh : 0 < h)
    (a a' b b' : Fin n → Fin h → ℝ) :
    (∑ s : Bool, ∑ t : Bool, complexCov n h a a' b b' s t) =
      ((h : ℝ) ^ 2)⁻¹ • ((realCov n h a b).map Complex.ofReal +
        (realCov n h a b').map Complex.ofReal +
        (realCov n h a' b).map Complex.ofReal +
        (realCov n h a' b').map Complex.ofReal) := by
  calc
    _ = ∑ s : Bool, ∑ i, ∑ t : Bool,
        projector (productState (h : ℝ) (a i) (a' i) (b i) (b' i) s t) := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ i, ∑ s : Bool, ∑ t : Bool,
        projector (productState (h : ℝ) (a i) (a' i) (b i) (b' i) s t) := Finset.sum_comm
    _ = _ := by
      simp only [four_sign_projector_sum (h : ℝ) (by exact_mod_cast ne_of_gt hh),
        ← Finset.smul_sum, Finset.sum_add_distrib, realCov_complex_eq]

/-- The paper's PSD domination summed over all samples. -/
theorem realCov_le_four_complexCov (n h : ℕ) (hh : 0 < h)
    (a a' b b' : Fin n → Fin h → ℝ) :
    (realCov n h a b).map Complex.ofReal ≤
      (h : ℝ) ^ 2 • (∑ s : Bool, ∑ t : Bool, complexCov n h a a' b b' s t) := by
  rw [four_sign_covariance_sum n h hh, smul_smul,
    mul_inv_cancel₀ (by positivity : (h : ℝ) ^ 2 ≠ 0), one_smul]
  calc
    _ ≤ (realCov n h a b).map Complex.ofReal + ((realCov n h a b').map Complex.ofReal +
        (realCov n h a' b).map Complex.ofReal + (realCov n h a' b').map Complex.ofReal) :=
      le_add_of_nonneg_right (add_nonneg
        (add_nonneg (realCov_complex_posSemidef n h a b').nonneg
          (realCov_complex_posSemidef n h a' b).nonneg)
        (realCov_complex_posSemidef n h a' b').nonneg)
    _ = _ := by abel

/-- A fixed sign ensemble is PSD-dominated by the sum of all four ensembles. -/
theorem complexCov_le_four_complexCov (n h : ℕ)
    (a a' b b' : Fin n → Fin h → ℝ) (s t : Bool) :
    complexCov n h a a' b b' s t ≤
      ∑ u : Bool, ∑ v : Bool, complexCov n h a a' b b' u v := by
  apply le_trans (Finset.single_le_sum (fun v _ =>
    (complexCov_posSemidef n h a a' b b' s v).nonneg) (Finset.mem_univ t))
  apply Finset.single_le_sum (fun u _ => ?_) (Finset.mem_univ s)
  exact Finset.sum_nonneg (fun v _ => (complexCov_posSemidef n h a a' b b' u v).nonneg)

/-- Exact pathwise norm domination, with real/complexification bridge. -/
theorem realCov_norm_le_four_complexCov_norm (n h : ℕ) (hh : 0 < h)
    (a a' b b' : Fin n → Fin h → ℝ) :
    ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a b)‖ ≤
      (h : ℝ) ^ 2 * ∑ s : Bool, ∑ t : Bool, ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ := by
  simp only [Matrix.l2_opNorm_toEuclideanCLM, cMatrixCLM_norm]
  rw [← real_complex_l2_matrix_norm]
  calc
    _ ≤ ‖(h : ℝ) ^ 2 • (∑ s : Bool, ∑ t : Bool, complexCov n h a a' b b' s t)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg (realCov_le_four_complexCov n h hh a a' b b')
        (realCov_complex_posSemidef n h a b).nonneg
    _ = (h : ℝ) ^ 2 * ‖∑ s : Bool, ∑ t : Bool, complexCov n h a a' b b' s t‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ _ := mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun s _ => norm_sum_le _ _))) (sq_nonneg _)

/-- One fixed-sign covariance is bounded by h⁻² times the four real covariance
norms. This supports the real-Gaussian replacement proof of the paper's tail. -/
theorem complexCov_norm_le_four_realCov_norm (n h : ℕ) (hh : 0 < h)
    (a a' b b' : Fin n → Fin h → ℝ) (s t : Bool) :
    ‖cMatrixCLM (complexCov n h a a' b b' s t)‖ ≤
      ((h : ℝ) ^ 2)⁻¹ *
        (‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a b)‖ +
         ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a b')‖ +
         ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a' b)‖ +
         ‖(Matrix.toEuclideanCLM (𝕜 := ℝ)) (realCov n h a' b')‖) := by
  simp only [cMatrixCLM_norm, Matrix.l2_opNorm_toEuclideanCLM]
  calc
    _ ≤ ‖∑ u : Bool, ∑ v : Bool, complexCov n h a a' b b' u v‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg (complexCov_le_four_complexCov n h a a' b b' s t)
        (complexCov_posSemidef n h a a' b b' s t).nonneg
    _ = ((h : ℝ) ^ 2)⁻¹ * ‖(realCov n h a b).map Complex.ofReal +
        (realCov n h a b').map Complex.ofReal + (realCov n h a' b).map Complex.ofReal +
        (realCov n h a' b').map Complex.ofReal‖ := by
      rw [four_sign_covariance_sum n h hh, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ ((h : ℝ) ^ 2)⁻¹)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      calc
        _ ≤ ‖(realCov n h a b).map Complex.ofReal‖ +
            ‖(realCov n h a b').map Complex.ofReal‖ +
            ‖(realCov n h a' b).map Complex.ofReal‖ +
            ‖(realCov n h a' b').map Complex.ofReal‖ :=
          (norm_add_le _ _).trans (add_le_add
            ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
        _ = _ := by simp only [real_complex_l2_matrix_norm]) (by positivity)

end AHHAlgebraBridges
