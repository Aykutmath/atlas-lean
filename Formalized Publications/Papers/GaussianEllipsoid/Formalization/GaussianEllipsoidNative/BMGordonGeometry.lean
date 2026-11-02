import BMSaddleProbability
import GaussianLinearMoments

noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory GaussianEllipsoid GaussianMixedNormHelpers BMGeometry BMSaddle
namespace BMGordon

abbrev UnitSample (n : ℕ) := ↥(Metric.sphere (0 : Euclid n) 1)
abbrev UnitCone (d : ℕ) (κ : ℝ) := ↥(conditionedUnitFrobenius d κ)

instance unitSample_compactSpace (n : ℕ) : CompactSpace (UnitSample n) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Euclid n) 1)
instance unitCone_compactSpace (d : ℕ) (κ : ℝ) : CompactSpace (UnitCone d κ) :=
  isCompact_iff_compactSpace.mp (conditionedUnitFrobenius_compact d κ)

theorem unitSample_nonempty {n : ℕ} (hn : 0 < n) : Nonempty (UnitSample n) :=
  (unitSphere_nonempty hn).to_subtype

theorem unitCone_nonempty {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    Nonempty (UnitCone d κ) := by
  obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd hκ
  refine ⟨⟨operatorFrobenius S, ?_⟩⟩
  refine ⟨?_,?_⟩
  · change frobeniusOperator (operatorFrobenius S) ∈ conditionCone d κ
    simpa only [frobeniusOperator_operatorFrobenius] using hS.1
  · simpa only [Metric.mem_sphere,dist_zero_right] using hS.2

@[simp] theorem unitSample_norm {n : ℕ} (u : UnitSample n) : ‖(u : Euclid n)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using u.property
@[simp] theorem unitCone_norm {d : ℕ} {κ : ℝ} (S : UnitCone d κ) : ‖(S : HMat d)‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using S.property.2

/-- All four independent Gaussian blocks live on this one finite coordinate space. -/
abbrev Index (n d : ℕ) := (EntryIndex n d ⊕ Unit) ⊕ ((Fin d × Fin d) ⊕ Fin n)
abbrev Space (n d : ℕ) := EuclideanSpace ℝ (Index n d)
abbrev law (n d : ℕ) := euclideanGaussianLaw (Index n d)

def primaryCoefficient {n d : ℕ} (u : Euclid n) (S : HMat d) : Space n d :=
  (WithLp.equiv 2 _).symm (Sum.elim (Sum.elim (tensor u S) (fun _ => 1)) (fun _ => 0))
def auxiliaryCoefficient {n d : ℕ} (u : Euclid n) (S : HMat d) : Space n d :=
  (WithLp.equiv 2 _).symm (Sum.elim (fun _ => 0)
    (Sum.elim (frobeniusEquivEuclidean d d S) u))

def primary {n d : ℕ} {κ : ℝ} (p : UnitSample n × UnitCone d κ) (ω : Space n d) : ℝ :=
  ⟪primaryCoefficient p.1 p.2,ω⟫_ℝ
def auxiliary {n d : ℕ} {κ : ℝ} (p : UnitSample n × UnitCone d κ) (ω : Space n d) : ℝ :=
  ⟪auxiliaryCoefficient p.1 p.2,ω⟫_ℝ

theorem tensor_inner {n d : ℕ} (u v : Euclid n) (S T : HMat d) :
    ⟪tensor u S,tensor v T⟫_ℝ = ⟪u,v⟫_ℝ * ⟪S,T⟫_ℝ := by
  change (∑ p : EntryIndex n d, (v p.1*T p.2.2 p.2.1)*(u p.1*S p.2.2 p.2.1)) =
    (∑ k, v k*u k)*(∑ j,∑ i,T j i*S j i)
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ k, (v k*u k)*(∑ j,∑ i,T j i*S j i) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem primaryCoefficient_inner {n d : ℕ} (u v : Euclid n) (S T : HMat d) :
    ⟪primaryCoefficient u S,primaryCoefficient v T⟫_ℝ =
      ⟪u,v⟫_ℝ*⟪S,T⟫_ℝ+1 := by
  change (∑ i : Index n d, primaryCoefficient v T i * primaryCoefficient u S i) = _
  simp only [Fintype.sum_sum_type, primaryCoefficient,
    Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
  change (∑ i : EntryIndex n d, tensor v T i*tensor u S i) + (∑ _ : Unit, (1:ℝ)*1) +
    ((∑ _ : Fin d × Fin d, (0:ℝ)*0)+(∑ _ : Fin n, (0:ℝ)*0)) = _
  simp only [one_mul,zero_mul,Fintype.sum_unique,Finset.sum_const_zero,add_zero]
  change ⟪tensor u S,tensor v T⟫_ℝ + 1 = _
  rw [tensor_inner]

theorem auxiliaryCoefficient_inner {n d : ℕ} (u v : Euclid n) (S T : HMat d) :
    ⟪auxiliaryCoefficient u S,auxiliaryCoefficient v T⟫_ℝ = ⟪S,T⟫_ℝ+⟪u,v⟫_ℝ := by
  change (∑ i : Index n d, auxiliaryCoefficient v T i * auxiliaryCoefficient u S i) = _
  simp only [Fintype.sum_sum_type, auxiliaryCoefficient,
    Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add]
  change ((∑ _ : EntryIndex n d, (0:ℝ)*0)+(∑ _ : Unit,(0:ℝ)*0))+
    ((∑ i : Fin d × Fin d, frobeniusEquivEuclidean d d T i*frobeniusEquivEuclidean d d S i)+
    ∑ i : Fin n, v i*u i) = _
  simp only [zero_mul,Finset.sum_const_zero,zero_add]
  change ⟪frobeniusEquivEuclidean d d S,frobeniusEquivEuclidean d d T⟫_ℝ + ⟪u,v⟫_ℝ = _
  rw [LinearIsometryEquiv.inner_map_map]

@[simp] theorem primaryCoefficient_norm_sq {n d : ℕ} {κ : ℝ}
    (u : UnitSample n) (S : UnitCone d κ) : ‖primaryCoefficient (u : Euclid n) (S : HMat d)‖^2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, primaryCoefficient_inner,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,unitSample_norm,unitCone_norm]
  norm_num
@[simp] theorem auxiliaryCoefficient_norm_sq {n d : ℕ} {κ : ℝ}
    (u : UnitSample n) (S : UnitCone d κ) : ‖auxiliaryCoefficient (u : Euclid n) (S : HMat d)‖^2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, auxiliaryCoefficient_inner,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,unitSample_norm,unitCone_norm]
  norm_num

theorem coefficient_increment_gap {n d : ℕ} {κ : ℝ}
    (u v : UnitSample n) (S T : UnitCone d κ) :
    ‖auxiliaryCoefficient (u : Euclid n) (S : HMat d)-auxiliaryCoefficient (v : Euclid n) (T : HMat d)‖^2 -
      ‖primaryCoefficient (u : Euclid n) (S : HMat d)-primaryCoefficient (v : Euclid n) (T : HMat d)‖^2 =
      2*(1-⟪(u : Euclid n),(v : Euclid n)⟫_ℝ)*(1-⟪(S : HMat d),(T : HMat d)⟫_ℝ) := by
  rw [norm_sub_sq_real,norm_sub_sq_real,auxiliaryCoefficient_norm_sq,
    auxiliaryCoefficient_norm_sq,primaryCoefficient_norm_sq,primaryCoefficient_norm_sq,
    primaryCoefficient_inner,auxiliaryCoefficient_inner]
  ring

theorem coefficient_increment_same_row {n d : ℕ} {κ : ℝ}
    (u : UnitSample n) (S T : UnitCone d κ) :
    ‖auxiliaryCoefficient (u : Euclid n) (S : HMat d)-auxiliaryCoefficient (u : Euclid n) (T : HMat d)‖^2 =
      ‖primaryCoefficient (u : Euclid n) (S : HMat d)-primaryCoefficient (u : Euclid n) (T : HMat d)‖^2 := by
  have h := coefficient_increment_gap u u S T
  rw [real_inner_self_eq_norm_sq,unitSample_norm] at h
  nlinarith

theorem coefficient_increment_comparison {n d : ℕ} {κ : ℝ}
    (u v : UnitSample n) (S T : UnitCone d κ) :
    ‖primaryCoefficient (u : Euclid n) (S : HMat d)-primaryCoefficient (v : Euclid n) (T : HMat d)‖^2 ≤
      ‖auxiliaryCoefficient (u : Euclid n) (S : HMat d)-auxiliaryCoefficient (v : Euclid n) (T : HMat d)‖^2 := by
  have hu := real_inner_le_norm (u : Euclid n) (v : Euclid n)
  have hS := real_inner_le_norm (S : HMat d) (T : HMat d)
  simp only [unitSample_norm,unitCone_norm,mul_one] at hu hS
  have hp := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hS)
  have h := coefficient_increment_gap u v S T
  nlinarith

end BMGordon

namespace BMGordon
open scoped InnerProductSpace
open GaussianEllipsoid BMGeometry BMSaddle

theorem coefficient_covariance_gap {n d : ℕ} {κ : ℝ}
    (u v : UnitSample n) (S T : UnitCone d κ) :
    ⟪primaryCoefficient (u : Euclid n) (S : HMat d),primaryCoefficient (v : Euclid n) (T : HMat d)⟫_ℝ -
      ⟪auxiliaryCoefficient (u : Euclid n) (S : HMat d),auxiliaryCoefficient (v : Euclid n) (T : HMat d)⟫_ℝ =
      (1-⟪(u : Euclid n),(v : Euclid n)⟫_ℝ)*(1-⟪(S : HMat d),(T : HMat d)⟫_ℝ) := by
  rw [primaryCoefficient_inner,auxiliaryCoefficient_inner]
  ring

theorem coefficient_covariance_same_row {n d : ℕ} {κ : ℝ}
    (u : UnitSample n) (S T : UnitCone d κ) :
    ⟪primaryCoefficient (u : Euclid n) (S : HMat d),primaryCoefficient (u : Euclid n) (T : HMat d)⟫_ℝ =
      ⟪auxiliaryCoefficient (u : Euclid n) (S : HMat d),auxiliaryCoefficient (u : Euclid n) (T : HMat d)⟫_ℝ := by
  rw [primaryCoefficient_inner,auxiliaryCoefficient_inner,real_inner_self_eq_norm_sq,unitSample_norm]
  ring

theorem coefficient_covariance_comparison {n d : ℕ} {κ : ℝ}
    (u v : UnitSample n) (S T : UnitCone d κ) :
    ⟪auxiliaryCoefficient (u : Euclid n) (S : HMat d),auxiliaryCoefficient (v : Euclid n) (T : HMat d)⟫_ℝ ≤
      ⟪primaryCoefficient (u : Euclid n) (S : HMat d),primaryCoefficient (v : Euclid n) (T : HMat d)⟫_ℝ := by
  have hu := real_inner_le_norm (u : Euclid n) (v : Euclid n)
  have hS := real_inner_le_norm (S : HMat d) (T : HMat d)
  simp only [unitSample_norm,unitCone_norm,mul_one] at hu hS
  have hp := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hS)
  have h := coefficient_covariance_gap u v S T
  linarith

end BMGordon
