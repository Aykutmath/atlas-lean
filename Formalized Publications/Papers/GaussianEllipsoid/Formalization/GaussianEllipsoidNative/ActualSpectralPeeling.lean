import OperatorSpectralPeeling

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

/-- Actual adaptive spectral peeling, with a supplied dimension-independent budget.
The stopping index is at most K; a fixed K-tail is never asserted to be diffuse. -/
theorem spectral_peeling_of_budget {d : ℕ} (S : Op d) (hS : IsPSD S)
    (hunit : ‖operatorFrobenius S‖ = 1) {τ δ : ℝ} {K : ℕ}
    (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hδ : 0 ≤ δ)
    (hK : (1-τ^2)^K ≤ δ^2) :
    ∃ j ≤ K, ∃ H R : Op d,
      IsPSD H ∧ IsPSD R ∧ S = H+R ∧ H.comp R = 0 ∧
      (∀ x y, ⟪H x, R y⟫_ℝ = 0) ∧
      ⟪operatorFrobenius H, operatorFrobenius R⟫_ℝ = 0 ∧
      Module.finrank ℝ (LinearMap.range H.toLinearMap) ≤ j ∧
      (frobeniusToMatrix (operatorFrobenius H)).rank ≤ j ∧
      (‖operatorFrobenius R‖ ≤ δ ∨ ‖R‖ ≤ τ * ‖operatorFrobenius R‖) := by
  let b := hS.1.eigenvectorBasis finrank_euclideanSpace_fin
  let a := hS.1.eigenvalues finrank_euclideanSpace_fin
  have ha : ∀ i, 0 ≤ a i := eigenvalue_nonneg hS
  have hanti : Antitone a := hS.1.eigenvalues_antitone _
  have hrecon : spectralOp b a = S := spectral_reconstruction S hS.1
  have henergy : ∑ i, (a i)^2 ≤ 1 := by
    rw [← spectralOp_frobenius_sq b a, hrecon, hunit]
    norm_num
  obtain ⟨j,hj,hstop⟩ := spectral_sequence_stopping a hτ hτ1 henergy hK
  refine ⟨j,hj,spectralHead b a j,spectralTail b a j,
    spectralHead_psd b a ha j,spectralTail_psd b a ha j,?_,
    spectralHead_comp_tail b a j,spectralHead_tail_ranges_orthogonal b a j,
    spectralHead_tail_frobenius_orthogonal b a j,spectralHead_range_finrank_le b a j,
    spectralHead_rank_le b a j,?_⟩
  · rw [spectralHead_add_tail, hrecon]
  · rcases hstop with hsmall | hdiff
    · left
      have he := spectralTail_frobenius_sq b a j
      nlinarith [norm_nonneg (operatorFrobenius (spectralTail b a j))]
    · right
      apply (spectralTail_norm_le b a ha hanti j).trans
      have hm := paddedEigenvalue_nonneg a ha j
      have he := spectralTail_frobenius_sq b a j
      have hn := norm_nonneg (operatorFrobenius (spectralTail b a j))
      have hp := mul_nonneg hτ hn
      nlinarith

/-- Every genuine diagonal operator has operator norm at most its Frobenius norm. -/
theorem norm_spectralOp_le_frobenius {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) :
    ‖spectralOp b a‖ ≤ ‖operatorFrobenius (spectralOp b a)‖ := by
  apply norm_spectralOp_le b a (norm_nonneg _)
  intro i
  have hi : (a i)^2 ≤ ∑ k, (a k)^2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ i)
  rw [← spectralOp_frobenius_sq b a] at hi
  nlinarith [norm_nonneg (operatorFrobenius (spectralOp b a)), abs_nonneg (a i), sq_abs (a i)]

theorem norm_psd_le_frobenius {d : ℕ} {S : Op d} (hS : IsPSD S) :
    ‖S‖ ≤ ‖operatorFrobenius S‖ := by
  nth_rw 1 [← spectral_reconstruction S hS.1]
  have h := norm_spectralOp_le_frobenius
    (hS.1.eigenvectorBasis finrank_euclideanSpace_fin)
    (hS.1.eigenvalues finrank_euclideanSpace_fin)
  simpa only [spectral_reconstruction] using h

/-- One budget works in every dimension, including caps at least one. -/
theorem exists_uniform_spectral_peeling {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ K : ℕ, (1-τ^2)^K ≤ δ^2 ∧
      ∀ (d : ℕ) (S : Op d), IsPSD S → ‖operatorFrobenius S‖ = 1 →
        ∃ j ≤ K, ∃ H R : Op d,
          IsPSD H ∧ IsPSD R ∧ S = H+R ∧ H.comp R = 0 ∧
          (∀ x y, ⟪H x, R y⟫_ℝ = 0) ∧
          ⟪operatorFrobenius H, operatorFrobenius R⟫_ℝ = 0 ∧
          Module.finrank ℝ (LinearMap.range H.toLinearMap) ≤ j ∧
      (frobeniusToMatrix (operatorFrobenius H)).rank ≤ j ∧
          (‖operatorFrobenius R‖ ≤ δ ∨ ‖R‖ ≤ τ * ‖operatorFrobenius R‖) := by
  by_cases ht : τ < 1
  · obtain ⟨K,hK⟩ := exists_peeling_budget hτ ht hδ
    refine ⟨K,hK,?_⟩
    intro d S hS hunit
    exact spectral_peeling_of_budget S hS hunit hτ.le ht.le hδ.le hK
  · have ht : 1 ≤ τ := le_of_not_gt ht
    refine ⟨1,?_,?_⟩
    · simpa only [pow_one] using (show 1-τ^2 ≤ δ^2 by nlinarith [sq_nonneg δ])
    · intro d S hS hunit
      have hz : operatorFrobenius (0 : Op d) = 0 := by ext j i; rfl
      have hmz : frobeniusToMatrix (0 : FrobeniusMatrix d d) = 0 := by ext i j; rfl
      refine ⟨0,by omega,0,S,isPSD_zero d,hS,by simp,by simp,?_,?_,?_,?_,Or.inr ?_⟩
      · intro x y; simp
      · rw [hz, inner_zero_left]
      · simp
      · rw [hz, hmz]; simp
      · exact (norm_psd_le_frobenius hS).trans
          (by nlinarith [norm_nonneg (operatorFrobenius S)])

/-- The tail in the non-small branch is genuinely normalized and diffuse. -/
theorem normalize_diffuse_tail {d : ℕ} {H R : Op d} {τ δ : ℝ}
    (hR : IsPSD R) (horth : H.comp R = 0) (hδ : 0 ≤ δ)
    (hsmall : δ < ‖operatorFrobenius R‖)
    (hdiff : ‖R‖ ≤ τ * ‖operatorFrobenius R‖) :
    ∃ ρ : ℝ, ∃ D : Op d, δ < ρ ∧ R = ρ • D ∧ IsPSD D ∧
      H.comp D = 0 ∧ ‖operatorFrobenius D‖ = 1 ∧ ‖D‖ ≤ τ := by
  let ρ := ‖operatorFrobenius R‖
  have hρ : 0 < ρ := lt_of_le_of_lt hδ hsmall
  let D : Op d := ρ⁻¹ • R
  refine ⟨ρ,D,hsmall,?_,hR.smul (inv_nonneg.mpr hρ.le),?_,?_,?_⟩
  · dsimp [D]
    rw [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  · apply ContinuousLinearMap.ext
    intro x
    change H (ρ⁻¹ • R x) = 0
    rw [map_smul]
    have hc := congrArg (fun T : Op d => T x) horth
    change H (R x) = 0 at hc
    rw [hc, smul_zero]
  · change ‖operatorFrobenius (ρ⁻¹ • R)‖ = 1
    rw [operatorFrobenius_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hρ.le)]
    exact inv_mul_cancel₀ hρ.ne'
  · change ‖ρ⁻¹ • R‖ ≤ τ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hρ.le)]
    calc
      ρ⁻¹ * ‖R‖ ≤ ρ⁻¹ * (τ * ρ) := mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hρ.le)
      _ = τ := by field_simp

/-- Orthogonal peeling preserves the actual Frobenius energy exactly. -/
theorem spectral_peeling_energy {d : ℕ} {S H R : Op d}
    (hunit : ‖operatorFrobenius S‖ = 1) (hdecomp : S = H+R)
    (horth : ⟪operatorFrobenius H,operatorFrobenius R⟫_ℝ = 0) :
    ‖operatorFrobenius H‖^2 + ‖operatorFrobenius R‖^2 = 1 := by
  have he : ‖operatorFrobenius S‖^2 = 1 := by rw [hunit]; norm_num
  rw [hdecomp, GaussianEllipsoid.operatorFrobenius_add, norm_add_sq_real, horth] at he
  nlinarith

/-- The complete finite large-eigenvalue/diffuse remainder decomposition.
All operators and norms are genuine. K is selected before dimension and S. -/
theorem exists_uniform_normalized_spectral_peeling {τ δ : ℝ}
    (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ K : ℕ, (1-τ^2)^K ≤ δ^2 ∧
      ∀ (d : ℕ) (S : Op d), IsPSD S → ‖operatorFrobenius S‖ = 1 →
        ∃ H R : Op d,
          IsPSD H ∧ IsPSD R ∧ S = H+R ∧ H.comp R = 0 ∧
          (∀ x y, ⟪H x,R y⟫_ℝ = 0) ∧
          ⟪operatorFrobenius H,operatorFrobenius R⟫_ℝ = 0 ∧
          Module.finrank ℝ (LinearMap.range H.toLinearMap) ≤ K ∧
          (frobeniusToMatrix (operatorFrobenius H)).rank ≤ K ∧
          ‖operatorFrobenius H‖^2 + ‖operatorFrobenius R‖^2 = 1 ∧
          (‖operatorFrobenius R‖ ≤ δ ∨
            ∃ ρ : ℝ, ∃ D : Op d, δ < ρ ∧ R = ρ • D ∧ IsPSD D ∧
              H.comp D = 0 ∧ ‖operatorFrobenius D‖ = 1 ∧ ‖D‖ ≤ τ) := by
  obtain ⟨K,hK,hpeel⟩ := exists_uniform_spectral_peeling hτ hδ
  refine ⟨K,hK,?_⟩
  intro d S hS hunit
  obtain ⟨j,hj,H,R,hH,hR,hdecomp,hcomp,hrangeorth,hfroborth,hrank,hmrank,hstop⟩ :=
    hpeel d S hS hunit
  refine ⟨H,R,hH,hR,hdecomp,hcomp,hrangeorth,hfroborth,hrank.trans hj,hmrank.trans hj,
    spectral_peeling_energy hunit hdecomp hfroborth,?_⟩
  by_cases hsmall : ‖operatorFrobenius R‖ ≤ δ
  · exact Or.inl hsmall
  · exact Or.inr (normalize_diffuse_tail hR hcomp hδ.le (lt_of_not_ge hsmall)
      (hstop.resolve_left hsmall))

end BMGeometry
#print axioms BMGeometry.spectral_peeling_of_budget
#print axioms BMGeometry.exists_uniform_spectral_peeling
#print axioms BMGeometry.normalize_diffuse_tail

#print axioms BMGeometry.exists_uniform_normalized_spectral_peeling
