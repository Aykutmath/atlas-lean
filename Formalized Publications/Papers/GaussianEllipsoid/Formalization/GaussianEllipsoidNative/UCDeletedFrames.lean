import UCRetainedFrames
import UCDeletedCoordinateEntropy
import UCEscapeStatistic
import ClippedL1Bridge

noncomputable section
open scoped InnerProductSpace
open GaussianEllipsoid BMGeometry BMSaddle
namespace UCEscape

/-- The retained coordinates associated to a deleted-coordinate set. -/
def retainedOfDeleted {n k : ℕ} (D : deletedCoordinateSets n k) : Finset (Fin n) :=
  Finset.univ \ D.val

/-- A uniform frame family exists after deleting any set of at most k coordinates. -/
theorem exists_deleted_frame_family {n r k : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : r + Module.finrank ℝ L + k ≤ n) :
    ∃ U : deletedCoordinateSets n k →
        EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ D x, U D x ∈ Lᗮ) ∧
      (∀ D x i, i ∉ retainedOfDeleted D → U D x i = 0) := by
  apply exists_retained_orthogonal_frame_family (fun D => retainedOfDeleted D) L
  intro D
  have hD := (mem_deletedCoordinateSets n k D.val).mp D.prop
  have hcard : (retainedOfDeleted D).card = n - D.val.card := by
    rw [retainedOfDeleted, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [hcard]
  omega

/-- Coordinates at or above the residual threshold. -/
def largeResidualCoordinates {n : ℕ} (w v : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    Finset (Fin n) := Finset.univ.filter (fun i => a ≤ |w i - v i|)

/-- Uniform projected escape over all small deletions forces many large residuals,
uniformly over every deterministic shift in L. -/
theorem many_large_residual_coordinates_of_frame_lower {n r k : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : deletedCoordinateSets n k →
      EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (horth : ∀ D x, U D x ∈ Lᗮ)
    (hsupp : ∀ D x i, i ∉ retainedOfDeleted D → U D x i = 0)
    (w v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ L)
    (a ell : ℝ) (ha : 0 ≤ a) (hgap : a * Real.sqrt n < ell)
    (hlower : ∀ D, ell ≤ ‖(U D).toContinuousLinearMap.adjoint w‖) :
    k < (largeResidualCoordinates w v a).card := by
  classical
  by_contra hb
  have hb' : (largeResidualCoordinates w v a).card ≤ k := Nat.le_of_not_gt hb
  let D : deletedCoordinateSets n k :=
    ⟨largeResidualCoordinates w v a, (mem_deletedCoordinateSets _ _ _).mpr hb'⟩
  have hsmall : ∀ i ∈ retainedOfDeleted D, (w i - v i)^2 ≤ a^2 := by
    intro i hi
    have hnot : i ∉ largeResidualCoordinates w v a := (Finset.mem_sdiff.mp hi).2
    have habs : |w i - v i| < a := by
      by_contra hn
      apply hnot
      simp [largeResidualCoordinates, le_of_not_gt hn]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (w i - v i)) ha).2 habs.le
  have hcard : ((retainedOfDeleted D).card : ℝ) ≤ n := by
    exact_mod_cast (show (retainedOfDeleted D).card ≤ n by
      simpa using Finset.card_le_univ (retainedOfDeleted D))
  have hs : ‖(U D).toContinuousLinearMap.adjoint w‖ ^ 2 ≤ (n : ℝ) * a ^ 2 := by
    calc
      _ ≤ ∑ i ∈ retainedOfDeleted D, (w i - v i)^2 :=
        frame_adjoint_norm_sq_le_shifted_retained _ (U D) L (horth D) (hsupp D) w v hv
      _ ≤ ∑ _i ∈ retainedOfDeleted D, a^2 := Finset.sum_le_sum hsmall
      _ = ((retainedOfDeleted D).card : ℝ) * a^2 := by simp
      _ ≤ (n : ℝ) * a^2 := mul_le_mul_of_nonneg_right hcard (sq_nonneg a)
  have hn : ‖(U D).toContinuousLinearMap.adjoint w‖ ≤ a * Real.sqrt n := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    nlinarith [hs]
  linarith [hlower D]

/-- The actual compact PSD escape statistic forces the residual-coordinate count. -/
theorem many_large_residual_coordinates_of_projectedEscape {n d r k : ℕ}
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : deletedCoordinateSets n k →
      EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (horth : ∀ D x, U D x ∈ Lᗮ)
    (hsupp : ∀ D x i, i ∉ retainedOfDeleted D → U D x i = 0)
    (X : BMSaddle.Sample n d) (S : HMat d) (hS : S ∈ psdUnit d)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ L)
    (a : ℝ) (ha : 0 ≤ a) (hgap : a * Real.sqrt n < projectedEscape U X) :
    k < (largeResidualCoordinates (measurement X S) v a).card := by
  apply many_large_residual_coordinates_of_frame_lower L U horth hsupp
    (measurement X S) v hv a (projectedEscape U X) ha hgap
  intro D
  exact csInf_le (projectedEscape_bddBelow U X) ⟨(D, ⟨S, hS⟩), rfl⟩

/-- Many large coordinates give a positive empirical rational-loss floor. -/
theorem smoothLoss_average_lower_of_many_large {n k : ℕ} (hn : 0 < n)
    (w v : EuclideanSpace ℝ (Fin n)) (a θ : ℝ) (ha : 0 ≤ a)
    (hcount : k < (largeResidualCoordinates w v a).card)
    (hθ : θ * (n : ℝ) ≤ (k : ℝ) + 1) :
    θ * BMClippedL1Bridge.smoothLoss a ≤
      (∑ i, BMClippedL1Bridge.smoothLoss (w i - v i)) / n := by
  let B := largeResidualCoordinates w v a
  have hcard : θ * (n : ℝ) ≤ (B.card : ℝ) := by
    have hnat : k + 1 ≤ B.card := hcount
    have hreal : (k : ℝ) + 1 ≤ (B.card : ℝ) := by exact_mod_cast hnat
    exact hθ.trans hreal
  have hsum : (B.card : ℝ) * BMClippedL1Bridge.smoothLoss a ≤
      ∑ i ∈ B, BMClippedL1Bridge.smoothLoss (w i - v i) := by
    calc
      _ = ∑ _i ∈ B, BMClippedL1Bridge.smoothLoss a := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact BMClippedL1Bridge.smoothLoss_gap ha (Finset.mem_filter.mp hi).2
  have hall : (∑ i ∈ B, BMClippedL1Bridge.smoothLoss (w i - v i)) ≤
      ∑ i, BMClippedL1Bridge.smoothLoss (w i - v i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => BMClippedL1Bridge.smoothLoss_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hcard (BMClippedL1Bridge.smoothLoss_nonneg a)
  apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mpr
  nlinarith

/-- The actual compact PSD escape statistic gives a uniform rational-loss floor
for all unit PSD matrices and every deterministic shift in L. -/
theorem smoothLoss_average_lower_of_projectedEscape {n d r k : ℕ} (hn : 0 < n)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (U : deletedCoordinateSets n k →
      EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (horth : ∀ D x, U D x ∈ Lᗮ)
    (hsupp : ∀ D x i, i ∉ retainedOfDeleted D → U D x i = 0)
    (X : BMSaddle.Sample n d) (S : HMat d) (hS : S ∈ psdUnit d)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ L)
    (a θ : ℝ) (ha : 0 ≤ a) (hgap : a * Real.sqrt n < projectedEscape U X)
    (hθ : θ * (n : ℝ) ≤ (k : ℝ) + 1) :
    θ * BMClippedL1Bridge.smoothLoss a ≤
      (∑ i, BMClippedL1Bridge.smoothLoss (measurement X S i - v i)) / n := by
  apply smoothLoss_average_lower_of_many_large hn (measurement X S) v a θ ha
    (many_large_residual_coordinates_of_projectedEscape L U horth hsupp X S hS v hv a ha hgap) hθ

#print axioms exists_deleted_frame_family
#print axioms smoothLoss_average_lower_of_projectedEscape
#print axioms many_large_residual_coordinates_of_frame_lower
#print axioms many_large_residual_coordinates_of_projectedEscape
end UCEscape
