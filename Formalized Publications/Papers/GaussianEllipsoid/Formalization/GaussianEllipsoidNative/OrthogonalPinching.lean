import SupportedPolar

noncomputable section
open Set Module
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid

/-- Pairing may be moved through a rectangular compression. -/
theorem inner_compression_eq {r q h k : ℕ}
    (D : Euclid r →L[ℝ] Euclid h) (T : Euclid q →L[ℝ] Euclid r)
    (E : Euclid k →L[ℝ] Euclid q) (W : Euclid k →L[ℝ] Euclid h) :
    ⟪operatorFrobenius (D ∘L T ∘L E), operatorFrobenius W⟫_ℝ =
      ⟪operatorFrobenius T,
        operatorFrobenius (ContinuousLinearMap.adjoint D ∘L W ∘L ContinuousLinearMap.adjoint E)⟫_ℝ := by
  have h₀ := inner_operator_comp_left D (T ∘L E) W
  have h₁ := inner_operator_comp_right T E (ContinuousLinearMap.adjoint D ∘L W)
  simpa only [ContinuousLinearMap.comp_assoc] using h₀.trans h₁

theorem left_support_of_two_sided {r q : ℕ} (D : Euclid r →L[ℝ] Euclid r)
    (E : Euclid q →L[ℝ] Euclid q) (W : Euclid q →L[ℝ] Euclid r)
    (hD : D ∘L D = D) (hW : D ∘L W ∘L E = W) : D ∘L W = W := by
  calc
    D ∘L W = D ∘L (D ∘L W ∘L E) := congrArg (fun U => D ∘L U) hW.symm
    _ = D ∘L W ∘L E := by rw [← ContinuousLinearMap.comp_assoc, hD]
    _ = W := hW

theorem right_support_of_two_sided {r q : ℕ} (D : Euclid r →L[ℝ] Euclid r)
    (E : Euclid q →L[ℝ] Euclid q) (W : Euclid q →L[ℝ] Euclid r)
    (hE : E ∘L E = E) (hW : D ∘L W ∘L E = W) : W ∘L E = W := by
  calc
    W ∘L E = (D ∘L W ∘L E) ∘L E := congrArg (fun U => U ∘L E) hW.symm
    _ = D ∘L W ∘L E := by simp only [ContinuousLinearMap.comp_assoc, hE]
    _ = W := hW

theorem inner_supported_eq_compressed {r q : ℕ}
    (D : Euclid r →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q)
    (T W : Euclid q →L[ℝ] Euclid r)
    (hD : ContinuousLinearMap.adjoint D = D) (hE : ContinuousLinearMap.adjoint E = E)
    (hW : D ∘L W ∘L E = W) :
    ⟪operatorFrobenius T, operatorFrobenius W⟫_ℝ =
      ⟪operatorFrobenius (D ∘L T ∘L E), operatorFrobenius W⟫_ℝ := by
  rw [inner_compression_eq, hD, hE, hW]

@[simp] theorem operatorFrobenius_zero (r q : ℕ) :
    operatorFrobenius (0 : Euclid q →L[ℝ] Euclid r) = 0 := by ext j i; rfl

/-- Exact cancellation of a backward block against a supported witness. -/
theorem inner_supported_eq_zero_of_compression_zero {r q : ℕ}
    (D : Euclid r →L[ℝ] Euclid r) (E : Euclid q →L[ℝ] Euclid q)
    (T W : Euclid q →L[ℝ] Euclid r)
    (hD : ContinuousLinearMap.adjoint D = D) (hE : ContinuousLinearMap.adjoint E = E)
    (hW : D ∘L W ∘L E = W) (hT : D ∘L T ∘L E = 0) :
    ⟪operatorFrobenius T, operatorFrobenius W⟫_ℝ = 0 := by
  rw [inner_supported_eq_compressed D E T W hD hE hW, hT, operatorFrobenius_zero, inner_zero_left]

theorem inner_projection_images_eq_zero {q : ℕ} (D E : Euclid q →L[ℝ] Euclid q)
    (hD : ContinuousLinearMap.adjoint D = D) (hDE : D ∘L E = 0) (x y : Euclid q) :
    ⟪D x, E y⟫_ℝ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right, hD]
  have h := congrArg (fun U : Euclid q →L[ℝ] Euclid q => U y) hDE
  change D (E y) = 0 at h
  rw [h, inner_zero_right]

/-- Bessel inequality for any finite family of orthogonal orthogonal projections. -/
theorem sum_projection_norm_sq_le {ι : Type*} [Fintype ι] {q : ℕ}
    (E : ι → Euclid q →L[ℝ] Euclid q)
    (hSelf : ∀ i, ContinuousLinearMap.adjoint (E i) = E i)
    (hSq : ∀ i, E i ∘L E i = E i)
    (hOrtho : ∀ i j, i ≠ j → E i ∘L E j = 0) (x : Euclid q) :
    ∑ i, ‖E i x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have horth : ∀ i j, i ≠ j → ⟪E i x, E j x⟫_ℝ = 0 :=
    fun i j hij => inner_projection_images_eq_zero (E i) (E j) (hSelf i) (hOrtho i j hij) x x
  have hnorm : ‖∑ i, E i x‖ ^ 2 = ∑ i, ‖E i x‖ ^ 2 := by
    simpa using norm_orthogonal_sum_sq (fun i => E i x) horth (fun _ => (1 : ℝ))
  have hinner : ⟪x, ∑ i, E i x⟫_ℝ = ∑ i, ‖E i x‖ ^ 2 := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := ContinuousLinearMap.adjoint_inner_right (E i) x (E i x)
    rw [hSelf i, real_inner_self_eq_norm_sq] at h
    have hx := congrArg (fun U : Euclid q →L[ℝ] Euclid q => U x) (hSq i)
    change E i (E i x) = E i x at hx
    rwa [hx] at h
  have hi := real_inner_le_norm x (∑ i, E i x)
  have hn : ‖∑ i, E i x‖ ≤ ‖x‖ := by
    rw [hinner, ← hnorm] at hi
    nlinarith [norm_nonneg x, norm_nonneg (∑ i, E i x)]
  rw [← hnorm]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- Sum of pairwise orthogonally supported rectangular contractions is a
contraction, with no loss in the number of blocks. -/
theorem norm_sum_supported_le_one {ι : Type*} [Fintype ι] {r q : ℕ}
    (D : ι → Euclid r →L[ℝ] Euclid r) (E : ι → Euclid q →L[ℝ] Euclid q)
    (W : ι → Euclid q →L[ℝ] Euclid r)
    (hDself : ∀ i, ContinuousLinearMap.adjoint (D i) = D i)
    (hEself : ∀ i, ContinuousLinearMap.adjoint (E i) = E i)
    (hDsq : ∀ i, D i ∘L D i = D i) (hEsq : ∀ i, E i ∘L E i = E i)
    (hDortho : ∀ i j, i ≠ j → D i ∘L D j = 0)
    (hEortho : ∀ i j, i ≠ j → E i ∘L E j = 0)
    (hNorm : ∀ i, ‖W i‖ ≤ 1) (hSupport : ∀ i, D i ∘L W i ∘L E i = W i) :
    ‖∑ i, W i‖ ≤ 1 := by
  have hLeft (i : ι) : D i ∘L W i = W i := left_support_of_two_sided _ _ _ (hDsq i) (hSupport i)
  have hRight (i : ι) : W i ∘L E i = W i := right_support_of_two_sided _ _ _ (hEsq i) (hSupport i)
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, ContinuousLinearMap.sum_apply]
  have horth : ∀ i j, i ≠ j → ⟪W i x, W j x⟫_ℝ = 0 := by
    intro i j hij
    have hi := congrArg (fun U : Euclid q →L[ℝ] Euclid r => U x) (hLeft i)
    have hj := congrArg (fun U : Euclid q →L[ℝ] Euclid r => U x) (hLeft j)
    change D i (W i x) = W i x at hi
    change D j (W j x) = W j x at hj
    rw [← hi, ← hj]
    exact inner_projection_images_eq_zero _ _ (hDself i) (hDortho i j hij) _ _
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hnorm : ‖∑ i, W i x‖ ^ 2 = ∑ i, ‖W i x‖ ^ 2 := by
    simpa using norm_orthogonal_sum_sq (fun i => W i x) horth (fun _ => (1 : ℝ))
  rw [hnorm]
  calc
    ∑ i, ‖W i x‖ ^ 2 ≤ ∑ i, ‖E i x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply pow_le_pow_left₀ (norm_nonneg _)
      have hi := congrArg (fun U : Euclid q →L[ℝ] Euclid r => U x) (hRight i)
      change W i (E i x) = W i x at hi
      rw [← hi]
      exact ((W i).le_opNorm (E i x)).trans
        (by simpa using mul_le_mul_of_nonneg_right (hNorm i) (norm_nonneg _))
    _ ≤ ‖x‖ ^ 2 := sum_projection_norm_sq_le E hEself hEsq hEortho x


@[simp] theorem operatorFrobenius_sum {ι : Type*} [Fintype ι] {r q : ℕ}
    (W : ι → Euclid q →L[ℝ] Euclid r) :
    operatorFrobenius (∑ i, W i) = ∑ i, operatorFrobenius (W i) := by
  let F : (Euclid q →L[ℝ] Euclid r) →+ FrobeniusMatrix r q :=
    { toFun := operatorFrobenius
      map_zero' := operatorFrobenius_zero r q
      map_add' := operatorFrobenius_add }
  exact map_sum F W Finset.univ

/-- Rectangular orthogonal pinching is nuclear-norm contractive, including a
sum over all diagonal rectangular blocks. -/
theorem sum_spectralNuclear_compressions_le {ι : Type*} [Fintype ι] {r q : ℕ}
    (T : Euclid q →L[ℝ] Euclid r)
    (D : ι → Euclid r →L[ℝ] Euclid r) (E : ι → Euclid q →L[ℝ] Euclid q)
    (hDself : ∀ i, ContinuousLinearMap.adjoint (D i) = D i)
    (hEself : ∀ i, ContinuousLinearMap.adjoint (E i) = E i)
    (hDsq : ∀ i, D i ∘L D i = D i) (hEsq : ∀ i, E i ∘L E i = E i)
    (hDortho : ∀ i j, i ≠ j → D i ∘L D j = 0)
    (hEortho : ∀ i j, i ≠ j → E i ∘L E j = 0) :
    ∑ i, spectralNuclearNorm (operatorFrobenius (D i ∘L T ∘L E i)) ≤
      spectralNuclearNorm (operatorFrobenius T) := by
  have hBlock (i : ι) : D i ∘L (D i ∘L T ∘L E i) ∘L E i = D i ∘L T ∘L E i := by
    apply ContinuousLinearMap.ext
    intro x
    change D i (D i (T (E i (E i x)))) = D i (T (E i x))
    have he := congrArg (fun U : Euclid q →L[ℝ] Euclid q => U x) (hEsq i)
    change E i (E i x) = E i x at he
    rw [he]
    exact congrArg (fun U : Euclid r →L[ℝ] Euclid r => U (T (E i x))) (hDsq i)
  choose W hNorm hSupport hPair hEnergy using fun i =>
    exists_supported_polar (D i ∘L T ∘L E i) (D i) (E i)
      (hDself i) (hEself i) (hDsq i) (hEsq i) (hBlock i)
  have hSum := norm_sum_supported_le_one D E W hDself hEself hDsq hEsq hDortho hEortho hNorm hSupport
  calc
    ∑ i, spectralNuclearNorm (operatorFrobenius (D i ∘L T ∘L E i)) =
        ∑ i, ⟪operatorFrobenius T, operatorFrobenius (W i)⟫_ℝ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_supported_eq_compressed (D i) (E i) T (W i) (hDself i) (hEself i) (hSupport i)]
      exact (hPair i).symm
    _ = ⟪operatorFrobenius T, operatorFrobenius (∑ i, W i)⟫_ℝ := by
      rw [operatorFrobenius_sum, inner_sum]
    _ ≤ spectralNuclearNorm (operatorFrobenius T) := inner_operator_le_nuclear _ _ hSum

end GaussianEllipsoid
#print axioms GaussianEllipsoid.inner_supported_eq_zero_of_compression_zero
#print axioms GaussianEllipsoid.norm_sum_supported_le_one

#print axioms GaussianEllipsoid.sum_spectralNuclear_compressions_le
