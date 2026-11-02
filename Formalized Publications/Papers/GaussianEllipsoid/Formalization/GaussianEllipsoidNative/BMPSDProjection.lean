import BMPerturbation

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

theorem symmetric_neg {d : ℕ} {T : Op d} (hT : T.toLinearMap.IsSymmetric) :
    (-T).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪(-T) x, y⟫_ℝ = ⟪x, (-T) y⟫_ℝ
  simp only [ContinuousLinearMap.neg_apply, inner_neg_left, inner_neg_right, hT.apply_clm]

/-- Support inequality for the PSD unit ball. -/
theorem psd_unitBall_support_le {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    {S : Op d} (hS : IsPSD S) (hn : ‖operatorFrobenius S‖ ≤ 1) :
    ⟪operatorFrobenius T, operatorFrobenius S⟫_ℝ ≤
      ‖operatorFrobenius (positivePart T hT)‖ := by
  exact (pairing_le_positive T hT hS).trans ((real_inner_le_norm _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left hn (norm_nonneg (operatorFrobenius (positivePart T hT)))))

theorem normalized_positive_pairing {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ⟪operatorFrobenius T, operatorFrobenius (normalize (positivePart T hT))⟫_ℝ =
      ‖operatorFrobenius (positivePart T hT)‖ := by
  rw [normalize, operatorFrobenius_smul, real_inner_smul_right, positive_pairing]
  by_cases hp : ‖operatorFrobenius (positivePart T hT)‖ = 0
  · simp [hp]
  · field_simp

theorem normalized_positive_psd {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    IsPSD (normalize (positivePart T hT)) :=
  (positivePart_positive T hT).smul (inv_nonneg.mpr (norm_nonneg _))

theorem normalize_norm_le_one {d : ℕ} (S : Op d) : ‖operatorFrobenius (normalize S)‖ ≤ 1 := by
  by_cases h : operatorFrobenius S = 0
  · simp [normalize, operatorFrobenius_smul, h]
  · rw [normalize_unit h]

/-- Exact support maximum, including the negative-definite case where the witness is zero. -/
theorem psd_unitBall_support_max {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    IsGreatest {z : ℝ | ∃ S : Op d, IsPSD S ∧ ‖operatorFrobenius S‖ ≤ 1 ∧
      z = ⟪operatorFrobenius T, operatorFrobenius S⟫_ℝ}
      ‖operatorFrobenius (positivePart T hT)‖ := by
  refine ⟨⟨normalize (positivePart T hT), normalized_positive_psd T hT,
    normalize_norm_le_one _, (normalized_positive_pairing T hT).symm⟩, ?_⟩
  rintro z ⟨S, hS, hn, rfl⟩
  exact psd_unitBall_support_le T hT hS hn

theorem norm_le_of_sq_le_mul {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p^2 ≤ q*p) : p ≤ q := by
  nlinarith

/-- Sign reversal swaps the positive/negative energies without choosing matching eigenbases. -/
theorem negative_norm_eq_positive_neg {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ‖operatorFrobenius (negativePart T hT)‖ =
      ‖operatorFrobenius (positivePart (-T) (symmetric_neg hT))‖ := by
  let P := operatorFrobenius (positivePart T hT)
  let N := operatorFrobenius (negativePart T hT)
  let Q := operatorFrobenius (positivePart (-T) (symmetric_neg hT))
  have hdecomp : operatorFrobenius (-T) = N-P := by
    rw [operatorFrobenius_neg]
    have h := congrArg operatorFrobenius (positive_sub_negative T hT)
    rw [operatorFrobenius_sub] at h
    change P-N = operatorFrobenius T at h
    rw [← h]
    abel
  have hPN : ⟪P,N⟫_ℝ = 0 := positive_negative_orthogonal T hT
  apply le_antisymm
  · apply norm_le_of_sq_le_mul (norm_nonneg N) (norm_nonneg Q)
    have h1 := pairing_le_positive (-T) (symmetric_neg hT) (negativePart_positive T hT)
    change ⟪operatorFrobenius (-T), N⟫_ℝ ≤ ⟪Q,N⟫_ℝ at h1
    rw [hdecomp, inner_sub_left, hPN, real_inner_self_eq_norm_sq, sub_zero] at h1
    exact h1.trans (real_inner_le_norm Q N)
  · apply norm_le_of_sq_le_mul (norm_nonneg Q) (norm_nonneg N)
    have h1 := positive_pairing (-T) (symmetric_neg hT)
    change ⟪operatorFrobenius (-T), Q⟫_ℝ = ‖Q‖^2 at h1
    rw [hdecomp, inner_sub_left] at h1
    have h2 := psd_pairing_nonneg (positivePart_positive T hT)
      (positivePart_positive (-T) (symmetric_neg hT))
    change 0 ≤ ⟪P,Q⟫_ℝ at h2
    have h3 := real_inner_le_norm N Q
    linarith

/-- The exact pointwise identity needed for E||G+||² = (dim Sym_d)/2. -/
theorem positive_energy_sign_split {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ‖operatorFrobenius (positivePart T hT)‖^2 +
      ‖operatorFrobenius (positivePart (-T) (symmetric_neg hT))‖^2 =
        ‖operatorFrobenius T‖^2 := by
  rw [← negative_norm_eq_positive_neg]
  exact positive_negative_energy T hT

theorem opTrace_spectral {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    opTrace T = ∑ i, hT.eigenvalues finrank_euclideanSpace_fin i := by
  unfold opTrace
  nth_rw 1 [← spectral_reconstruction T hT]
  rw [spectral_pairing_general]
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq,
    (hT.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one, one_pow, mul_one]

/-- On the PSD cone, the genuine singular-value nuclear norm equals the trace. -/
theorem nuclear_eq_trace_of_psd {d : ℕ} {T : Op d} (hT : IsPSD T) :
    spectralNuclearNorm (operatorFrobenius T) = opTrace T := by
  apply le_antisymm
  · apply (spectralNuclear_le_iff _ _).mpr
    intro W hW
    rw [opTrace_spectral T hT.1]
    nth_rw 1 [← spectral_reconstruction T hT.1]
    rw [spectral_pairing_general]
    apply Finset.sum_le_sum
    intro i _
    have hw : ⟪W (hT.1.eigenvectorBasis finrank_euclideanSpace_fin i),
        hT.1.eigenvectorBasis finrank_euclideanSpace_fin i⟫_ℝ ≤ 1 := by
      calc
        _ ≤ ‖W (hT.1.eigenvectorBasis finrank_euclideanSpace_fin i)‖ *
          ‖hT.1.eigenvectorBasis finrank_euclideanSpace_fin i‖ := real_inner_le_norm _ _
        _ ≤ 1 := by
          have hn := W.le_opNorm (hT.1.eigenvectorBasis finrank_euclideanSpace_fin i)
          rw [(hT.1.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one, mul_one] at hn ⊢
          exact hn.trans hW
    simpa using mul_le_mul_of_nonneg_left hw (eigenvalue_nonneg hT i)
  · exact inner_operator_le_nuclear (operatorFrobenius T)
      (ContinuousLinearMap.id ℝ (Euclid d)) ContinuousLinearMap.norm_id_le

end BMGeometry
