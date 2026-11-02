import GaussianSparseSupportEvent
import NuclearCompression

noncomputable section
open GaussianTensorMoments
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.SparseSupport

/-- A lower norm bound produces a scaled left inverse which is a contraction.
The construction uses the genuine range and its orthogonal projection. -/
theorem exists_scaled_left_inverse {s h : ℕ} (A : Euclid s →L[ℝ] Euclid h)
    {c : ℝ} (hc : 0 < c) (hA : ∀ v, c*‖v‖^2 ≤ ‖A v‖^2) :
    ∃ R : Euclid h →L[ℝ] Euclid s,
      ‖R‖ ≤ 1 ∧ R ∘L A = Real.sqrt c • ContinuousLinearMap.id ℝ _ := by
  have hAi : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have hh := hA v
    rw [hv, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hh
    have hsq : ‖v‖^2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by simpa using hh)
    have hnorm : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hnorm
  let W : Submodule ℝ (Euclid h) := LinearMap.range A.toLinearMap
  let e : Euclid s ≃L[ℝ] W := (LinearEquiv.ofInjective A.toLinearMap hAi).toContinuousLinearEquiv
  let R : Euclid h →L[ℝ] Euclid s :=
    Real.sqrt c • (e.symm.toContinuousLinearMap ∘L W.orthogonalProjection)
  have hAsym (y : W) : A (e.symm y) = y := LinearEquiv.ofInjective_symm_apply _ (h := hAi) y
  have hRnorm : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro x
    change ‖Real.sqrt c • e.symm (W.orthogonalProjection x)‖ ≤ 1*‖x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
    have hquad := hA (e.symm (W.orthogonalProjection x))
    rw [hAsym] at hquad
    have hp : ‖W.orthogonalProjection x‖ ≤ ‖x‖ := by
      have hb := W.orthogonalProjection.le_opNorm x
      exact hb.trans (by simpa using mul_le_mul_of_nonneg_right W.orthogonalProjection_norm_le (norm_nonneg x))
    apply (sq_le_sq₀ (by positivity) (norm_nonneg x)).mp
    rw [mul_pow, Real.sq_sqrt hc.le]
    exact hquad.trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg x)).mpr hp)
  refine ⟨R, hRnorm, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  change Real.sqrt c • e.symm (W.orthogonalProjection (A v)) = Real.sqrt c • v
  have hv : A v = (e v : Euclid h) := rfl
  rw [hv, Submodule.orthogonalProjection_mem_subspace_eq_self, e.symm_apply_apply]

/-- Genuine rectangular nuclear multiplication lower bound. The hypotheses
are all-vector norm inequalities, never assumed singular values or pseudoinverses. -/
theorem spectralNuclear_multiplication_lower {s t h k : ℕ}
    (A : Euclid s →L[ℝ] Euclid h) (B : Euclid t →L[ℝ] Euclid k)
    (D : Euclid t →L[ℝ] Euclid s) {c : ℝ} (hc : 0 < c)
    (hA : ∀ v, c*‖v‖^2 ≤ ‖A v‖^2) (hB : ∀ v, c*‖v‖^2 ≤ ‖B v‖^2) :
    c * spectralNuclearNorm (operatorFrobenius D) ≤
      spectralNuclearNorm (operatorFrobenius (A ∘L D ∘L ContinuousLinearMap.adjoint B)) := by
  obtain ⟨R, hR, hRA⟩ := exists_scaled_left_inverse A hc hA
  obtain ⟨S, hS, hSB⟩ := exists_scaled_left_inverse B hc hB
  have hBSt : ContinuousLinearMap.adjoint B ∘L ContinuousLinearMap.adjoint S =
      Real.sqrt c • ContinuousLinearMap.id ℝ (Euclid t) := by
    rw [← ContinuousLinearMap.adjoint_comp, hSB]
    simp [ContinuousLinearMap.adjoint_id]
  have hident : R ∘L (A ∘L D ∘L ContinuousLinearMap.adjoint B) ∘L
      ContinuousLinearMap.adjoint S = c • D := by
    apply ContinuousLinearMap.ext
    intro v
    have hRAv (w : Euclid s) : R (A w) = Real.sqrt c • w :=
      congrArg (fun T : Euclid s →L[ℝ] Euclid s => T w) hRA
    have hBStv : ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint S v) =
        Real.sqrt c • v := congrArg (fun T : Euclid t →L[ℝ] Euclid t => T v) hBSt
    change R (A (D (ContinuousLinearMap.adjoint B (ContinuousLinearMap.adjoint S v)))) = c • D v
    rw [hRAv, hBStv, map_smul, smul_smul, ← pow_two, Real.sq_sqrt hc.le]
  have hh := spectralNuclear_compression_le R
    (A ∘L D ∘L ContinuousLinearMap.adjoint B) (ContinuousLinearMap.adjoint S) hR
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hS)
  rw [hident] at hh
  change spectralNuclearNorm (c • operatorFrobenius D) ≤ _ at hh
  simpa only [spectralNuclear_smul, abs_of_pos hc] using hh

/-- The sparse Gaussian event gives the nuclear lower bound for every
middle operator on every small support, simultaneously and samplewise. -/
theorem sparseGood_nuclear_lower {d n m : ℕ} (hd : 24 ≤ d) {p}
    (hp : p ∈ sparseGood (2*(d/4)) n m) (I : Finset (Fin n)) (hI : I.card ≤ m)
    (D : Euclid I.card →L[ℝ] Euclid I.card) :
    (d : ℝ)/12 * spectralNuclearNorm (operatorFrobenius D) ≤
      spectralNuclearNorm (operatorFrobenius
        (supportOperator (2*(d/4)) n I p.1 ∘L D ∘L
          ContinuousLinearMap.adjoint (supportOperator (2*(d/4)) n I p.2))) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  apply spectralNuclear_multiplication_lower _ _ D (by positivity)
  · intro v
    exact (sparseGood_dimension_lower hd hp I hI v).1
  · intro v
    exact (sparseGood_dimension_lower hd hp I hI v).2

end GaussianEllipsoid.SparseSupport
