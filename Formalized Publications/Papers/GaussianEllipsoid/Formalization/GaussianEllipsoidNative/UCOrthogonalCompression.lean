import NuclearCompression
import UCProjectSpectralPeeling

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
namespace UCEscape

lemma operatorFrobenius_norm_sq_columns {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    ‖operatorFrobenius T‖^2 = ∑ j : Fin q, ‖T (EuclideanSpace.basisFun (Fin q) ℝ j)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

lemma frobenius_norm_adjoint {r q : ℕ} (T : Euclid q →L[ℝ] Euclid r) :
    ‖operatorFrobenius T.adjoint‖ = ‖operatorFrobenius T‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [real_inner_self_eq_norm_sq] using inner_operatorFrobenius_adjoint T T

lemma frobenius_norm_isometry_comp {r q p : ℕ}
    (U : Euclid r →ₗᵢ[ℝ] Euclid p) (T : Euclid q →L[ℝ] Euclid r) :
    ‖operatorFrobenius (U.toContinuousLinearMap.comp T)‖ = ‖operatorFrobenius T‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [operatorFrobenius_norm_sq_columns, operatorFrobenius_norm_sq_columns]
  apply Finset.sum_congr rfl
  intro j _
  change ‖U (T (EuclideanSpace.basisFun (Fin q) ℝ j))‖^2 = _
  rw [U.norm_map]

lemma frobenius_norm_comp_isometry_adjoint {r q p : ℕ}
    (U : Euclid q →ₗᵢ[ℝ] Euclid p) (T : Euclid q →L[ℝ] Euclid r) :
    ‖operatorFrobenius (T.comp U.toContinuousLinearMap.adjoint)‖ = ‖operatorFrobenius T‖ := by
  rw [← frobenius_norm_adjoint (T.comp U.toContinuousLinearMap.adjoint),
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    frobenius_norm_isometry_comp, frobenius_norm_adjoint]

def compress {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d) (D : Op d) : Op p :=
  V.toContinuousLinearMap.adjoint.comp (D.comp V.toContinuousLinearMap)

lemma projection_fixes_range {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (y : Euclid d) (hy : y ∈ LinearMap.range V.toLinearMap) :
    V (V.toContinuousLinearMap.adjoint y) = y := by
  obtain ⟨x,rfl⟩ := hy
  have h := congrArg (fun T : Euclid p →L[ℝ] Euclid p => T x) V.adjoint_comp_self
  change V.toContinuousLinearMap.adjoint (V x) = x at h
  change V (V.toContinuousLinearMap.adjoint (V x)) = V x
  rw [h]

lemma compress_psd {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D) : IsPSD (compress V D) := by
  have hpair (x y : Euclid p) :
      ⟪compress V D x,y⟫_ℝ = ⟪D (V x),V y⟫_ℝ := by
    exact V.toContinuousLinearMap.adjoint_inner_left y (D (V x))
  constructor
  · intro x y
    change ⟪compress V D x,y⟫_ℝ = ⟪x,compress V D y⟫_ℝ
    calc
      ⟪compress V D x,y⟫_ℝ = ⟪D (V x),V y⟫_ℝ := hpair x y
      _ = ⟪V x,D (V y)⟫_ℝ := hD.1 (V x) (V y)
      _ = ⟪D (V y),V x⟫_ℝ := real_inner_comm _ _
      _ = ⟪compress V D y,x⟫_ℝ := (hpair y x).symm
      _ = ⟪x,compress V D y⟫_ℝ := real_inner_comm _ _
  · intro x
    rw [hpair]
    exact hD.2 (V x)

lemma compression_reconstruction {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D)
    (hsupp : ∀ x, D x ∈ LinearMap.range V.toLinearMap) :
    V.toContinuousLinearMap.comp ((compress V D).comp V.toContinuousLinearMap.adjoint) = D := by
  have hleft : V.toContinuousLinearMap.comp (V.toContinuousLinearMap.adjoint.comp D) = D := by
    apply ContinuousLinearMap.ext
    intro x
    exact projection_fixes_range V (D x) (hsupp x)
  have hself : D.adjoint = D :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hD.1).adjoint_eq
  have hright := congrArg ContinuousLinearMap.adjoint hleft
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hself] at hright
  apply ContinuousLinearMap.ext
  intro x
  change V (V.toContinuousLinearMap.adjoint (D (V (V.toContinuousLinearMap.adjoint x)))) = D x
  rw [projection_fixes_range V _ (hsupp _)]
  exact congrArg (fun T : Op d => T x) hright

lemma compress_frobenius_norm {d p : ℕ} (V : Euclid p →ₗᵢ[ℝ] Euclid d)
    (D : Op d) (hD : IsPSD D)
    (hsupp : ∀ x, D x ∈ LinearMap.range V.toLinearMap) :
    ‖operatorFrobenius (compress V D)‖ = ‖operatorFrobenius D‖ := by
  conv_rhs => rw [← compression_reconstruction V D hD hsupp]
  rw [frobenius_norm_isometry_comp, frobenius_norm_comp_isometry_adjoint]

#print axioms compression_reconstruction
#print axioms compress_frobenius_norm
end UCEscape
