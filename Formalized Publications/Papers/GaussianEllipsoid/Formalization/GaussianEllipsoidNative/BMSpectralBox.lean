import BMConditionEigen
import BMRescaling

noncomputable section
open scoped BigOperators InnerProductSpace Matrix
open GaussianEllipsoid
namespace BMGeometry

@[simp] theorem opMatrix_sub {d : ℕ} (T S : Op d) : opMatrix (T-S) = opMatrix T - opMatrix S := by
  ext i j
  rfl

@[simp] theorem opMatrix_smul {d : ℕ} (a : ℝ) (T : Op d) : opMatrix (a • T) = a • opMatrix T := by
  ext i j
  rfl

@[simp] theorem opMatrix_id (d : ℕ) : opMatrix (ContinuousLinearMap.id ℝ (Euclid d)) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
  ext i j
  simp [opMatrix, frobeniusToMatrix, EuclideanSpace.basisFun_apply]
  split_ifs <;> aesop

theorem spectralBox_of_eigenvalue_bounds {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    {lo hi : ℝ}
    (hlohi : ∀ i, lo ≤ hT.eigenvalues finrank_euclideanSpace_fin i ∧
      hT.eigenvalues finrank_euclideanSpace_fin i ≤ hi) :
    opMatrix T ∈ BMRescaling.spectralBox d lo hi := by
  have hb (x : Euclid d) : lo*‖x‖^2 ≤ ⟪T x,x⟫_ℝ ∧ ⟪T x,x⟫_ℝ ≤ hi*‖x‖^2 := by
    have h := spectralOp_rayleigh_bounds (hT.eigenvectorBasis finrank_euclideanSpace_fin)
      (hT.eigenvalues finrank_euclideanSpace_fin) hlohi x
    rw [spectral_reconstruction] at h
    exact h
  have hlow : IsPSD (T-lo • ContinuousLinearMap.id ℝ (Euclid d)) := by
    refine ⟨hT.sub ((isPSD_id d).1.smul (by simp)), ?_⟩
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [(hb x).1]
  have hupp : IsPSD (hi • ContinuousLinearMap.id ℝ (Euclid d)-T) := by
    refine ⟨((isPSD_id d).1.smul (by simp)).sub hT, ?_⟩
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith [(hb x).2]
  constructor
  · simpa only [opMatrix_sub, opMatrix_smul, opMatrix_id] using (opMatrix_posSemidef_iff _).mpr hlow
  · simpa only [opMatrix_sub, opMatrix_smul, opMatrix_id] using (opMatrix_posSemidef_iff _).mpr hupp

/-- Exact endpoint extraction used in BM §3.1.4, now in the actual Loewner box consumed by
BMRescaling. The endpoints are dimension-independent and explicit: B/κ and κ√A. -/
theorem conditioned_trace_energy_spectralBox {d : ℕ} (hd : 0 < d) {T : Op d} {κ A B : ℝ}
    (hT : T ∈ conditionCone d κ) (hκ : 0 < κ) (hA : 0 ≤ A)
    (henergy : ‖operatorFrobenius T‖^2 ≤ A*d) (htrace : B*d ≤ opTrace T) :
    opMatrix T ∈ BMRescaling.spectralBox d (B/κ) (κ*Real.sqrt A) := by
  exact spectralBox_of_eigenvalue_bounds T hT.1.1 fun i =>
    ⟨eigenvalue_lower_of_trace hd hT hκ htrace i,
      eigenvalue_upper_of_energy hd hT hκ.le hA henergy i⟩

/-- The trace lower bound from a bounded-norm dual witness, as used in BM §3.1.4. -/
theorem trace_lower_of_dual_pairing {d : ℕ} {T H : Op d} {B C : ℝ}
    (hT : IsPSD T) (hC : 0 < C) (hH : ‖H‖ ≤ C)
    (hpair : B*d ≤ |⟪operatorFrobenius T,operatorFrobenius H⟫_ℝ|) :
    (B/C)*d ≤ opTrace T := by
  have hcontr : ‖C⁻¹ • H‖ ≤ 1 := by
    rw [norm_smul C⁻¹ H, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    exact (mul_le_mul_of_nonneg_left hH (inv_nonneg.mpr hC.le)).trans_eq (inv_mul_cancel₀ hC.ne')
  have h := abs_inner_operator_le_nuclear (operatorFrobenius T) (C⁻¹ • H) hcontr
  rw [operatorFrobenius_smul, real_inner_smul_right, abs_mul,
    abs_of_pos (inv_pos.mpr hC), nuclear_eq_trace_of_psd hT] at h
  calc
    (B/C)*d = C⁻¹*(B*d) := by ring
    _ ≤ C⁻¹*|⟪operatorFrobenius T,operatorFrobenius H⟫_ℝ| :=
      mul_le_mul_of_nonneg_left hpair (inv_nonneg.mpr hC.le)
    _ ≤ opTrace T := h

end BMGeometry
