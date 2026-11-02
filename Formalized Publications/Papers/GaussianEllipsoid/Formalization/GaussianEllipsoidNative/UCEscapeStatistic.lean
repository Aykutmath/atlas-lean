import BMSaddleCoordinates
import UCPSDUnitGeometry

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry BMSaddle
namespace UCEscape

lemma measurement_norm_le {n d : ℕ} (X : BMSaddle.Sample n d) (S : HMat d) :
    ‖measurement X S‖ ≤ ‖X‖*‖S‖ := by
  apply norm_le_of_sq_le_mul (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h := real_inner_le_norm X (tensor (measurement X S) S)
  rw [← combine_pairing, ← measurement_pairing, real_inner_self_eq_norm_sq, tensor_norm] at h
  nlinarith

lemma measurement_sub_left {n d : ℕ} (X Y : BMSaddle.Sample n d) (S : HMat d) :
    measurement (X-Y) S = measurement X S - measurement Y S := by
  ext k
  simp [measurement_apply, sub_mul, Finset.sum_sub_distrib]

lemma adjoint_isometry_norm_le {n r : ℕ}
    (U : Euclid r →ₗᵢ[ℝ] Euclid n) (v : Euclid n) :
    ‖U.toContinuousLinearMap.adjoint v‖ ≤ ‖v‖ := by
  apply norm_le_of_sq_le_mul (norm_nonneg _) (norm_nonneg _)
  have h := real_inner_le_norm (U (U.toContinuousLinearMap.adjoint v)) v
  have he := U.toContinuousLinearMap.adjoint_inner_right
    (U.toContinuousLinearMap.adjoint v) v
  change ⟪U.toContinuousLinearMap.adjoint v,U.toContinuousLinearMap.adjoint v⟫_ℝ =
    ⟪U (U.toContinuousLinearMap.adjoint v),v⟫_ℝ at he
  rw [← he, real_inner_self_eq_norm_sq, U.norm_map] at h
  nlinarith

variable {J : Type*} [Nonempty J] {n d r : ℕ}

def projectedEscape (U : J → Euclid r →ₗᵢ[ℝ] Euclid n)
    (X : BMSaddle.Sample n d) : ℝ :=
  sInf (Set.range (fun p : J × ↥(psdUnit d) =>
    ‖(U p.1).toContinuousLinearMap.adjoint (measurement X p.2)‖))

lemma projectedEscape_bddBelow (U : J → Euclid r →ₗᵢ[ℝ] Euclid n)
    (X : BMSaddle.Sample n d) :
    BddBelow (Set.range (fun p : J × ↥(psdUnit d) =>
      ‖(U p.1).toContinuousLinearMap.adjoint (measurement X p.2)‖)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨p,rfl⟩
  exact norm_nonneg _

lemma projectedEscape_sub_le (hd : 0 < d)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) (X Y : BMSaddle.Sample n d) :
    projectedEscape U X - ‖X-Y‖ ≤ projectedEscape U Y := by
  letI : Nonempty ↥(psdUnit d) := (psdUnit_nonempty hd).to_subtype
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨p,rfl⟩
  have hi : projectedEscape U X ≤ ‖(U p.1).toContinuousLinearMap.adjoint (measurement X p.2)‖ :=
    csInf_le (projectedEscape_bddBelow U X) ⟨p,rfl⟩
  have hn : ‖(p.2 : HMat d)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property.2
  have he := norm_sub_norm_le
    ((U p.1).toContinuousLinearMap.adjoint (measurement X p.2))
    ((U p.1).toContinuousLinearMap.adjoint (measurement Y p.2))
  rw [← map_sub, ← measurement_sub_left] at he
  have hb := (adjoint_isometry_norm_le (U p.1) (measurement (X-Y) p.2)).trans
    (measurement_norm_le (X-Y) p.2)
  rw [hn, mul_one] at hb
  linarith

theorem projectedEscape_lipschitz (hd : 0 < d)
    (U : J → Euclid r →ₗᵢ[ℝ] Euclid n) : LipschitzWith 1 (projectedEscape (d := d) U) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs]
  have h1 := projectedEscape_sub_le hd U X Y
  have h2 := projectedEscape_sub_le hd U Y X
  rw [norm_sub_rev Y X] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms projectedEscape_lipschitz
end UCEscape
