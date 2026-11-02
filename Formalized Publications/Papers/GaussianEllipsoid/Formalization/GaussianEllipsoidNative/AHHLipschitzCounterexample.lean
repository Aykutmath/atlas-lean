import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A kernel-checkable counterexample to the AHH scalar 1-Lipschitz assertion

This file uses complex Euclidean spaces and the Euclidean operator norm, not an
entrywise or Frobenius norm. The input distance is precisely the sum over the
factor positions of the Euclidean product distance over the samples.

Reference: Ambainis--Harrow--Hastings, arXiv:0910.0472v2, printed pp. 7--8.
The statement refuted is a proof step, not the concentration inequality itself.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open WithLp

namespace AHHLipschitzCounterexample

abbrev LocalSpace := EuclideanSpace ℂ (Fin 2)
abbrev TensorSpace := EuclideanSpace ℂ (Fin 2 × Fin 2)
abbrev Configuration (ι : Type*) := Fin 2 → ι → LocalSpace

/-- A rank-one complex outer product, in orthonormal coordinates. -/
def projector {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => v i * star (v j)

/-- The coordinate outer product is the standard rank-one continuous linear operator. -/
theorem projector_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : EuclideanSpace ℂ ι) :
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (projector v) = InnerProductSpace.rankOne ℂ v v := by
  apply ContinuousLinearMap.coe_injective
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  apply (Matrix.toEuclideanLin (𝕜 := ℂ) (m := ι) (n := ι)).symm.injective
  rw [LinearEquiv.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne]
  rfl

/-- The canonical coordinate realization of a two-factor pure tensor. -/
def pureTensor (u v : LocalSpace) : TensorSpace :=
  toLp 2 (fun i => u i.1 * v i.2)

/-- The tensor product of rank-one projectors is the projector of the pure tensor. -/
theorem projector_pureTensor (u v : LocalSpace) :
    projector (pureTensor u v) = Matrix.kronecker (projector u) (projector v) := by
  ext i j
  simp [projector, pureTensor, Matrix.kronecker_apply, mul_comm, mul_left_comm, mul_assoc]

/-- The exact matrix whose norm appears in the AHH normalized ensemble, for k=2. -/
def ahhMatrix {ι : Type*} [Fintype ι] (X : Configuration ι) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ s, Matrix.kronecker (projector (X 0 s)) (projector (X 1 s))

/-- The same matrix is a sum of rank-one tensor projectors. -/
theorem ahhMatrix_eq_sum_projectors {ι : Type*} [Fintype ι] (X : Configuration ι) :
    ahhMatrix X = ∑ s, projector (pureTensor (X 0 s) (X 1 s)) := by
  simp only [ahhMatrix, projector_pureTensor]

/-- The scalar function is the genuine Euclidean operator norm. -/
def ahhFunction {ι : Type*} [Fintype ι] (X : Configuration ι) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin 2 × Fin 2) (𝕜 := ℂ)) (ahhMatrix X)‖

/-- The norm instance used in subsequent calculations is exactly that operator norm. -/
theorem ahhFunction_eq_l2_matrix_norm {ι : Type*} [Fintype ι] (X : Configuration ι) :
    ahhFunction X = ‖ahhMatrix X‖ := by
  exact Matrix.l2_opNorm_toEuclideanCLM (ahhMatrix X)

/-- AHH's outer ℓ1 and inner ℓ2 product metric, with Euclidean chord distance. -/
def ahhDistance {ι : Type*} [Fintype ι] (X Y : Configuration ι) : ℝ :=
  ∑ a : Fin 2, Real.sqrt (∑ s : ι, ‖X a s - Y a s‖ ^ 2)

/-- Exact bridge to Mathlib's standard nested ℓ1/ℓ2 metric. -/
theorem ahhDistance_eq_nested_distance {ι : Type*} [Fintype ι]
    (X Y : Configuration ι) :
    ahhDistance X Y =
      dist (toLp 1 (fun a => toLp 2 (X a))) (toLp 1 (fun a => toLp 2 (Y a))) := by
  unfold ahhDistance
  rw [PiLp.dist_eq_of_L1]
  apply Finset.sum_congr rfl
  intro a _
  change _ = dist (toLp 2 (X a)) (toLp 2 (Y a))
  rw [PiLp.dist_eq_of_L2]
  simp only [PiLp.toLp_apply, dist_eq_norm]

/-- Every individual factor lies on the complex unit sphere. -/
def UnitConfiguration {ι : Type*} (X : Configuration ι) : Prop :=
  ∀ a s, ‖X a s‖ = 1

/-- The two standard coordinate unit vectors of ℂ². -/
def basisVector (i : Fin 2) : LocalSpace := toLp 2 (Pi.single i 1)

@[simp] theorem basisVector_apply (i j : Fin 2) :
    basisVector i j = if j = i then 1 else 0 := by
  simp [basisVector, Pi.single_apply]

@[simp] theorem basisVector_norm (i : Fin 2) : ‖basisVector i‖ = 1 := by
  simp [basisVector]

@[simp] theorem basisVector_sub_sq (i j : Fin 2) :
    ‖basisVector i - basisVector j‖ ^ 2 = if i = j then 0 else 2 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, basisVector_apply]

@[simp] theorem basisVector_sub_norm (i j : Fin 2) :
    ‖basisVector i - basisVector j‖ = if i = j then 0 else Real.sqrt 2 := by
  calc
    _ = Real.sqrt (‖basisVector i - basisVector j‖ ^ 2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [basisVector_sub_sq]; split_ifs <;> simp

/-- There are m copies of each of the two orthogonal first-factor states. -/
def configA (m : ℕ) : Configuration (Fin 2 × Fin m) :=
  fun a s => if a = 0 then basisVector s.1 else basisVector 0

/-- All 2m first-factor states coincide, as do the second-factor states. -/
def configB (m : ℕ) : Configuration (Fin 2 × Fin m) :=
  fun _ _ => basisVector 0

theorem configA_unit (m : ℕ) : UnitConfiguration (configA m) := by
  intro a s
  dsimp [configA]
  split_ifs <;> exact basisVector_norm _

theorem configB_unit (m : ℕ) : UnitConfiguration (configB m) := by
  intro a s
  simp [configB]

/-- The sample count is p=2m. -/
theorem sample_card (m : ℕ) : Fintype.card (Fin 2 × Fin m) = 2 * m := by simp

/-- Exact diagonalization of the first configuration. -/
theorem matrixA (m : ℕ) : ahhMatrix (configA m) =
    Matrix.diagonal (fun i : Fin 2 × Fin 2 => if i.2 = 0 then (m : ℂ) else 0) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [ahhMatrix, Matrix.sum_apply]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [ahhMatrix, configA, projector, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply]

/-- Exact diagonalization of the second configuration. -/
theorem matrixB (m : ℕ) : ahhMatrix (configB m) =
    Matrix.diagonal (fun i : Fin 2 × Fin 2 => if i = (0, 0) then (2 * m : ℂ) else 0) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [ahhMatrix, Matrix.sum_apply]
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [ahhMatrix, configB, projector, Matrix.kronecker_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.diagonal_apply, two_mul]

/-- A nonempty diagonal indicator with nonnegative real value has that operator norm. -/
theorem diagonal_indicator_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Prop) [DecidablePred P] (i₀ : ι) (hi₀ : P i₀)
    (c : ℝ) (hc : 0 ≤ c) :
    ‖Matrix.diagonal (fun i : ι => if P i then (c : ℂ) else 0)‖ = c := by
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hc).mpr
    intro i
    split_ifs <;> simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, hc]
  · simpa [hi₀, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc] using
      (norm_le_pi_norm (fun i : ι => if P i then (c : ℂ) else 0) i₀)

theorem functionA (m : ℕ) : ahhFunction (configA m) = m := by
  rw [ahhFunction_eq_l2_matrix_norm, matrixA]
  convert diagonal_indicator_norm (fun i : Fin 2 × Fin 2 => i.2 = 0) (0, 0)
    rfl (m : ℝ) (Nat.cast_nonneg m) using 1 <;> simp

theorem functionB (m : ℕ) : ahhFunction (configB m) = 2 * m := by
  rw [ahhFunction_eq_l2_matrix_norm, matrixB]
  convert diagonal_indicator_norm (fun i : Fin 2 × Fin 2 => i = (0, 0)) (0, 0)
    rfl (2 * m : ℝ) (by positivity) using 1 <;> simp

/-- The exact AHH input distance for the replicated family. -/
theorem distanceAB (m : ℕ) :
    ahhDistance (configA m) (configB m) = Real.sqrt (2 * m) := by
  simp [ahhDistance, configA, configB, Fin.sum_univ_two, Fintype.sum_prod_type,
    basisVector_sub_sq, mul_comm]

/-- Every global Lipschitz bound has a sample-count-dependent necessary lower bound. -/
theorem lipschitz_constant_necessary (m : ℕ) (L : ℝ)
    (hL : ∀ X Y : Configuration (Fin 2 × Fin m),
      UnitConfiguration X → UnitConfiguration Y →
      |ahhFunction X - ahhFunction Y| ≤ L * ahhDistance X Y) :
    (m : ℝ) ≤ L * Real.sqrt (2 * m) := by
  have h := hL (configA m) (configB m) (configA_unit m) (configB_unit m)
  rw [functionA, functionB, distanceAB] at h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simpa [show (m : ℝ) - 2 * m = -m by ring, abs_of_nonneg hm] using h

/-- For p=2m>0, the replicated family forces L≥√p/2. -/
theorem lipschitz_constant_lower_bound (m : ℕ) (hm : 0 < m) (L : ℝ)
    (hL : ∀ X Y : Configuration (Fin 2 × Fin m),
      UnitConfiguration X → UnitConfiguration Y →
      |ahhFunction X - ahhFunction Y| ≤ L * ahhDistance X Y) :
    Real.sqrt (2 * m) / 2 ≤ L := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hs : 0 < Real.sqrt (2 * m) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * m by positivity)
  have h := lipschitz_constant_necessary m L hL
  apply (mul_le_mul_iff_left₀ hs).mp
  nlinarith

/-- Even with k=d=2 fixed, no finite Lipschitz constant works for every sample count. -/
theorem no_sample_independent_constant :
    ¬ (∃ L : ℝ, ∀ m : ℕ, ∀ X Y : Configuration (Fin 2 × Fin m),
      UnitConfiguration X → UnitConfiguration Y →
      |ahhFunction X - ahhFunction Y| ≤ L * ahhDistance X Y) := by
  rintro ⟨L, hL⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * L ^ 2 + 1)
  have hm' : (0 : ℝ) < m := by nlinarith [sq_nonneg L]
  have hb := lipschitz_constant_lower_bound m (Nat.cast_pos.mp hm') L (hL m)
  have hs := Real.sqrt_nonneg (2 * (m : ℝ))
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * m by positivity)
  have hL0 : 0 ≤ L := by linarith
  have hsq : (Real.sqrt (2 * (m : ℝ))) ^ 2 ≤ (2 * L) ^ 2 := by
    apply pow_le_pow_left₀ hs
    linarith
  nlinarith

/-- Concrete k=2, d=2, p=8 violation of the asserted scalar 1-Lipschitz inequality. -/
theorem counterexample_p8 :
    UnitConfiguration (configA 4) ∧ UnitConfiguration (configB 4) ∧
    Fintype.card (Fin 2 × Fin 4) = 8 ∧
    ahhFunction (configA 4) = 4 ∧ ahhFunction (configB 4) = 8 ∧
    ahhDistance (configA 4) (configB 4) = Real.sqrt 8 ∧
    ahhDistance (configA 4) (configB 4) <
      |ahhFunction (configA 4) - ahhFunction (configB 4)| := by
  refine ⟨configA_unit 4, configB_unit 4, by simp, ?_, ?_, ?_, ?_⟩
  · simpa using functionA 4
  · convert functionB 4 using 1 <;> norm_num
  · simpa only [Nat.cast_ofNat, show (2 : ℝ) * 4 = 8 by norm_num] using distanceAB 4
  · rw [functionA, functionB, distanceAB]
    norm_num
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)

/-- The universal scalar 1-Lipschitz assertion on the stated input space is false. -/
theorem not_one_lipschitz_p8 :
    ¬ (∀ X Y : Configuration (Fin 2 × Fin 4),
      UnitConfiguration X → UnitConfiguration Y →
      |ahhFunction X - ahhFunction Y| ≤ ahhDistance X Y) := by
  intro h
  exact (not_le_of_gt counterexample_p8.2.2.2.2.2.2)
    (h _ _ (configA_unit 4) (configB_unit 4))

end AHHLipschitzCounterexample
