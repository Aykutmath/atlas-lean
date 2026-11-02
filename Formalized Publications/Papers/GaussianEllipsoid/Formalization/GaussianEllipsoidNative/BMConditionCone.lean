import BMSpectralPositive

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

/-- Bounded condition number, stated without arbitrary eigenvalue ordering.
For PSD operators this says every Rayleigh quotient is at most κ times any other. -/
def conditionCone (d : ℕ) (κ : ℝ) : Set (Op d) :=
  {T | IsPSD T ∧ ∀ x y : Euclid d, ‖x‖ = 1 → ‖y‖ = 1 →
    ⟪T x, x⟫_ℝ ≤ κ * ⟪T y, y⟫_ℝ}

theorem isPSD_zero (d : ℕ) : IsPSD (0 : Op d) := by
  refine ⟨LinearMap.IsSymmetric.zero, ?_⟩
  intro x
  simp

theorem IsPSD.add {d : ℕ} {S T : Op d} (hS : IsPSD S) (hT : IsPSD T) : IsPSD (S+T) := by
  refine ⟨hS.1.add hT.1, ?_⟩
  intro x
  simpa only [ContinuousLinearMap.add_apply, inner_add_left] using add_nonneg (hS.2 x) (hT.2 x)

theorem IsPSD.smul {d : ℕ} {T : Op d} (hT : IsPSD T) {a : ℝ} (ha : 0 ≤ a) : IsPSD (a • T) := by
  refine ⟨hT.1.smul (by simp), ?_⟩
  intro x
  simpa only [ContinuousLinearMap.smul_apply, real_inner_smul_left] using mul_nonneg ha (hT.2 x)

theorem zero_mem_conditionCone (d : ℕ) (κ : ℝ) : (0 : Op d) ∈ conditionCone d κ := by
  refine ⟨isPSD_zero d, ?_⟩
  intro x y hx hy
  simp

theorem conditionCone_add {d : ℕ} {κ : ℝ} {S T : Op d}
    (hS : S ∈ conditionCone d κ) (hT : T ∈ conditionCone d κ) : S+T ∈ conditionCone d κ := by
  refine ⟨hS.1.add hT.1, ?_⟩
  intro x y hx hy
  simpa only [ContinuousLinearMap.add_apply, inner_add_left, mul_add] using
    add_le_add (hS.2 x y hx hy) (hT.2 x y hx hy)

theorem conditionCone_smul {d : ℕ} {κ a : ℝ} {T : Op d}
    (ha : 0 ≤ a) (hT : T ∈ conditionCone d κ) : a • T ∈ conditionCone d κ := by
  refine ⟨hT.1.smul ha, ?_⟩
  intro x y hx hy
  simpa only [ContinuousLinearMap.smul_apply, real_inner_smul_left, mul_left_comm κ a] using
    mul_le_mul_of_nonneg_left (hT.2 x y hx hy) ha

theorem convex_conditionCone (d : ℕ) (κ : ℝ) : Convex ℝ (conditionCone d κ) := by
  intro S hS T hT a b ha hb hab
  exact conditionCone_add (conditionCone_smul ha hS) (conditionCone_smul hb hT)

theorem conditionCone_mono {d : ℕ} {κ κ' : ℝ} (hκ : κ ≤ κ') :
    conditionCone d κ ⊆ conditionCone d κ' := by
  intro T hT
  refine ⟨hT.1, ?_⟩
  intro x y hx hy
  exact (hT.2 x y hx hy).trans (mul_le_mul_of_nonneg_right hκ (hT.1.2 y))

theorem continuous_operator_inner {d : ℕ} (x y : Euclid d) :
    Continuous (fun T : Op d => ⟪T x, y⟫_ℝ) :=
  ((ContinuousLinearMap.apply ℝ (Euclid d) x).continuous).inner continuous_const

theorem isClosed_isPSD (d : ℕ) : IsClosed {T : Op d | IsPSD T} := by
  have hs : IsClosed {T : Op d | T.toLinearMap.IsSymmetric} := by
    change IsClosed {T : Op d | ∀ x y, ⟪T x, y⟫_ℝ = ⟪x, T y⟫_ℝ}
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    exact isClosed_eq (continuous_operator_inner x y)
      (continuous_const.inner (ContinuousLinearMap.apply ℝ (Euclid d) y).continuous)
  have hp : IsClosed {T : Op d | ∀ x, 0 ≤ ⟪T x, x⟫_ℝ} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_operator_inner x x)
  exact hs.inter hp

theorem isClosed_conditionCone (d : ℕ) (κ : ℝ) : IsClosed (conditionCone d κ) := by
  apply (isClosed_isPSD d).inter
  change IsClosed {T : Op d | ∀ x y : Euclid d, ‖x‖ = 1 → ‖y‖ = 1 →
    ⟪T x, x⟫_ℝ ≤ κ * ⟪T y, y⟫_ℝ}
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun _hx =>
    isClosed_iInter fun _hy => isClosed_le (continuous_operator_inner x x)
      (continuous_const.mul (continuous_operator_inner y y))

/-- The Rayleigh definition entails every pairwise eigenvalue inequality. -/
theorem conditionCone_eigenvalues {d : ℕ} {κ : ℝ} {T : Op d}
    (hT : T ∈ conditionCone d κ) (i j : Fin d) :
    hT.1.1.eigenvalues finrank_euclideanSpace_fin i ≤
      κ * hT.1.1.eigenvalues finrank_euclideanSpace_fin j := by
  have h := hT.2 (hT.1.1.eigenvectorBasis finrank_euclideanSpace_fin i)
    (hT.1.1.eigenvectorBasis finrank_euclideanSpace_fin j)
    ((hT.1.1.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one i)
    ((hT.1.1.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one j)
  simpa only [← ContinuousLinearMap.coe_coe, hT.1.1.apply_eigenvectorBasis,
    real_inner_smul_left, real_inner_self_eq_norm_sq,
    (hT.1.1.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one,
    one_pow, mul_one] using! h

end BMGeometry
