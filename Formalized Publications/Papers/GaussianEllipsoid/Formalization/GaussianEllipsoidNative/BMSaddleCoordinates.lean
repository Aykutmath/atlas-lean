import BMThresholdMargin
import BMFullEntryWidth
import BMConeCompact
import GaussianVarianceBound

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid BMGeometry
namespace BMSaddle

abbrev EntryIndex (n d : ℕ) := Fin n × (Fin d × Fin d)
abbrev Sample (n d : ℕ) := EuclideanSpace ℝ (EntryIndex n d)

def tensor {n d : ℕ} (u : Euclid n) (S : HMat d) : Sample n d :=
  (WithLp.equiv 2 _).symm (fun p => u p.1 * S p.2.2 p.2.1)

def combine {n d : ℕ} (X : Sample n d) (u : Euclid n) : HMat d :=
  (WithLp.equiv 2 _).symm (fun j => (WithLp.equiv 2 _).symm (fun i =>
    ∑ k : Fin n, u k * X (k,(i,j))))

@[simp] theorem combine_apply {n d : ℕ} (X : Sample n d) (u : Euclid n) (j i : Fin d) :
    combine X u j i = ∑ k : Fin n, u k * X (k,(i,j)) := rfl

theorem tensor_norm {n d : ℕ} (u : Euclid n) (S : HMat d) : ‖tensor u S‖ = ‖u‖*‖S‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, frobenius_norm_sq]
  simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
  change (∑ k, ∑ i, ∑ j, (u k * S j i)^2) = (∑ k, (u k)^2) * ∑ j, ∑ i, (S j i)^2
  simp_rw [mul_pow]
  calc
    _ = ∑ k, (u k)^2 * (∑ i, ∑ j, (S j i)^2) := by simp only [Finset.mul_sum]
    _ = (∑ k, (u k)^2) * (∑ i, ∑ j, (S j i)^2) := (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [Finset.sum_comm (f := fun i j => (S j i)^2)]

theorem combine_pairing {n d : ℕ} (X : Sample n d) (u : Euclid n) (S : HMat d) :
    ⟪combine X u,S⟫_ℝ = ⟪X,tensor u S⟫_ℝ := by
  change (∑ j, ∑ i, S j i * (∑ k, u k * X (k,(i,j)))) =
    ∑ p : EntryIndex n d, (u p.1 * S p.2.2 p.2.1) * X p
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  calc
    _ = ∑ j, ∑ k, ∑ i, S j i * (u k * X (k,(i,j))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ j, ∑ i, S j i * (u k * X (k,(i,j))) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem combine_norm_le {n d : ℕ} (X : Sample n d) (u : Euclid n) :
    ‖combine X u‖ ≤ ‖X‖*‖u‖ := by
  apply norm_le_of_sq_le_mul (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h := real_inner_le_norm X (tensor u (combine X u))
  rw [← combine_pairing, real_inner_self_eq_norm_sq, tensor_norm] at h
  nlinarith

@[simp] theorem combine_sub_left {n d : ℕ} (X Y : Sample n d) (u : Euclid n) :
    combine (X-Y) u = combine X u - combine Y u := by
  ext j i
  simp [combine_apply, mul_sub, Finset.sum_sub_distrib]

def combineRightLM {n d : ℕ} (X : Sample n d) : Euclid n →ₗ[ℝ] HMat d where
  toFun := combine X
  map_add' u v := by ext j i; simp [combine_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c u := by ext j i; simp [combine_apply, Finset.mul_sum, mul_assoc]

def measurementLM {n d : ℕ} (X : Sample n d) : HMat d →ₗ[ℝ] Euclid n where
  toFun S := (WithLp.equiv 2 _).symm (fun k => ∑ j, ∑ i, X (k,(i,j))*S j i)
  map_add' S T := by ext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c S := by ext k; simp [Finset.mul_sum, mul_left_comm]

def measurement {n d : ℕ} (X : Sample n d) : HMat d →L[ℝ] Euclid n :=
  (measurementLM X).toContinuousLinearMap

@[simp] theorem measurement_apply {n d : ℕ} (X : Sample n d) (S : HMat d) (k : Fin n) :
    measurement X S k = ∑ j, ∑ i, X (k,(i,j))*S j i := rfl

theorem measurement_pairing {n d : ℕ} (X : Sample n d) (u : Euclid n) (S : HMat d) :
    ⟪u,measurement X S⟫_ℝ = ⟪combine X u,S⟫_ℝ := by
  rw [combine_pairing]
  change (∑ k, (∑ j, ∑ i, X (k,(i,j))*S j i)*u k) =
    ∑ p : EntryIndex n d, (u p.1*S p.2.2 p.2.1)*X p
  simp only [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def ones (n : ℕ) : Euclid n := (WithLp.equiv 2 _).symm (fun _ => 1)

@[simp] theorem ones_apply (n : ℕ) (i : Fin n) : ones n i = 1 := rfl

theorem ones_norm (n : ℕ) : ‖ones n‖ = Real.sqrt n := by
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp [ones]

end BMSaddle
