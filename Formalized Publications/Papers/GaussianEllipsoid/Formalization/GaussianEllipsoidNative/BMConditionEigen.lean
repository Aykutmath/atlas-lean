import BMSupportLoss
import BMMatrixBridge

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

theorem conditionCone_of_eigenvalues {d : ℕ} {κ : ℝ} {T : Op d}
    (hT : IsPSD T)
    (hspec : ∀ i j, hT.1.eigenvalues finrank_euclideanSpace_fin i ≤
      κ * hT.1.eigenvalues finrank_euclideanSpace_fin j) : T ∈ conditionCone d κ := by
  refine ⟨hT, ?_⟩
  intro x y hx hy
  let b := hT.1.eigenvectorBasis finrank_euclideanSpace_fin
  let a := hT.1.eigenvalues finrank_euclideanSpace_fin
  have hTx : ⟪T x,x⟫_ℝ = ∑ i, a i * (b.repr x i)^2 := by
    nth_rw 1 [← spectral_reconstruction T hT.1]
    rw [spectralOp_inner]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hTy : ⟪T y,y⟫_ℝ = ∑ i, a i * (b.repr y i)^2 := by
    nth_rw 1 [← spectral_reconstruction T hT.1]
    rw [spectralOp_inner]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsumx : ∑ i, (b.repr x i)^2 = 1 := by rw [repr_sq_sum, hx, one_pow]
  have hsumy : ∑ i, (b.repr y i)^2 = 1 := by rw [repr_sq_sum, hy, one_pow]
  have hpoint (j : Fin d) : ⟪T x,x⟫_ℝ ≤ κ*a j := by
    rw [hTx]
    calc
      _ ≤ ∑ i, (κ*a j) * (b.repr x i)^2 := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hspec i j) (sq_nonneg _)
      _ = κ*a j := by rw [← Finset.mul_sum, hsumx, mul_one]
  calc
    ⟪T x,x⟫_ℝ = ∑ j, ⟪T x,x⟫_ℝ * (b.repr y j)^2 := by rw [← Finset.mul_sum, hsumy, mul_one]
    _ ≤ ∑ j, (κ*a j) * (b.repr y j)^2 := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hpoint j) (sq_nonneg _)
    _ = κ*⟪T y,y⟫_ℝ := by rw [hTy, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring

theorem conditionCone_iff_eigenvalues {d : ℕ} {κ : ℝ} {T : Op d} (hT : IsPSD T) :
    T ∈ conditionCone d κ ↔ ∀ i j, hT.1.eigenvalues finrank_euclideanSpace_fin i ≤
      κ * hT.1.eigenvalues finrank_euclideanSpace_fin j := by
  exact ⟨fun h i j => conditionCone_eigenvalues h i j, conditionCone_of_eigenvalues hT⟩

/-- Spectral energy is the genuine Frobenius norm squared. -/
theorem eigenvalues_sq_sum {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ∑ i, (hT.eigenvalues finrank_euclideanSpace_fin i)^2 = ‖operatorFrobenius T‖^2 := by
  rw [← spectralOp_frobenius_sq, spectral_reconstruction]

/-- §3.1.4 lower spectral endpoint from trace and condition number. -/
theorem eigenvalue_lower_of_trace {d : ℕ} (hd : 0 < d) {T : Op d} {κ B : ℝ}
    (hT : T ∈ conditionCone d κ) (hκ : 0 < κ) (htrace : B*d ≤ opTrace T) (j : Fin d) :
    B/κ ≤ hT.1.1.eigenvalues finrank_euclideanSpace_fin j := by
  have hsum : opTrace T ≤ (d : ℝ) * (κ*hT.1.1.eigenvalues finrank_euclideanSpace_fin j) := by
    rw [opTrace_spectral T hT.1.1]
    calc
      _ ≤ ∑ _i : Fin d, κ*hT.1.1.eigenvalues finrank_euclideanSpace_fin j :=
        Finset.sum_le_sum fun i _ => conditionCone_eigenvalues hT i j
      _ = _ := by simp
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  apply (div_le_iff₀ hκ).mpr
  nlinarith

/-- §3.1.4 upper spectral endpoint from Frobenius energy and condition number. -/
theorem eigenvalue_upper_of_energy {d : ℕ} (hd : 0 < d) {T : Op d} {κ A : ℝ}
    (hT : T ∈ conditionCone d κ) (hκ : 0 ≤ κ) (hA : 0 ≤ A)
    (henergy : ‖operatorFrobenius T‖^2 ≤ A*d) (i : Fin d) :
    hT.1.1.eigenvalues finrank_euclideanSpace_fin i ≤ κ*Real.sqrt A := by
  let a := hT.1.1.eigenvalues finrank_euclideanSpace_fin
  have hsum : (d : ℝ) * (a i)^2 ≤ κ^2 * ‖operatorFrobenius T‖^2 := by
    rw [← eigenvalues_sq_sum T hT.1.1, Finset.mul_sum]
    calc
      _ = ∑ _j : Fin d, (a i)^2 := by simp
      _ ≤ ∑ j, κ^2 * (a j)^2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := conditionCone_eigenvalues hT i j
        change a i ≤ κ*a j at h
        have hi := eigenvalue_nonneg hT.1 i
        have hj := eigenvalue_nonneg hT.1 j
        change 0 ≤ a i at hi
        change 0 ≤ a j at hj
        nlinarith [sq_le_sq₀ hi (mul_nonneg hκ hj) |>.mpr h]
  have hmul := mul_le_mul_of_nonneg_left henergy (sq_nonneg κ)
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hs : (a i)^2 ≤ κ^2*A := by nlinarith
  have hi := eigenvalue_nonneg hT.1 i
  have hsqrt := Real.sq_sqrt hA
  have hnonneg : 0 ≤ κ*Real.sqrt A := mul_nonneg hκ (Real.sqrt_nonneg _)
  change a i ≤ κ*Real.sqrt A
  nlinarith

end BMGeometry
