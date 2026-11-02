import OperatorFrobeniusEquiv
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

abbrev Op (d : ℕ) := Euclid d →L[ℝ] Euclid d
abbrev HMat (d : ℕ) := FrobeniusMatrix d d

/-- Positive semidefiniteness of an actual Euclidean operator. -/
def IsPSD {d : ℕ} (T : Op d) : Prop :=
  T.toLinearMap.IsSymmetric ∧ ∀ x, 0 ≤ ⟪T x, x⟫_ℝ

/-- Diagonal operator in an actual orthonormal basis. -/
def spectralOp {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d)) (a : Fin d → ℝ) : Op d :=
  LinearMap.toContinuousLinearMap (b.toBasis.constr ℝ (fun i => a i • b i))

@[simp] theorem spectralOp_basis {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (i : Fin d) : spectralOp b a (b i) = a i • b i :=
  b.toBasis.constr_basis ℝ _ i

theorem spectralOp_apply {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (x : Euclid d) :
    spectralOp b a x = ∑ i, (b.repr x i * a i) • b i := by
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, spectralOp_basis, smul_smul]

theorem spectralOp_inner {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (x y : Euclid d) :
    ⟪spectralOp b a x, y⟫_ℝ = ∑ i, a i * (b.repr x i) * (b.repr y i) := by
  rw [spectralOp_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left, ← b.repr_apply_apply]
  ring

theorem spectralOp_symmetric {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) : (spectralOp b a).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪spectralOp b a x, y⟫_ℝ = ⟪x, spectralOp b a y⟫_ℝ
  rw [← real_inner_comm x (spectralOp b a y), spectralOp_inner, spectralOp_inner]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectralOp_positive {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (ha : ∀ i, 0 ≤ a i) : IsPSD (spectralOp b a) := by
  refine ⟨spectralOp_symmetric b a, ?_⟩
  intro x
  change 0 ≤ ⟪spectralOp b a x, x⟫_ℝ
  rw [spectralOp_inner]
  exact Finset.sum_nonneg fun i _ => by nlinarith [mul_nonneg (ha i) (sq_nonneg (b.repr x i))]

theorem spectralOp_frobenius_sq {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) : ‖operatorFrobenius (spectralOp b a)‖ ^ 2 = ∑ i, (a i)^2 := by
  rw [← sum_norm_sq_operator_basis _ b]
  simp only [spectralOp_basis, norm_smul, Real.norm_eq_abs, b.norm_eq_one, mul_one, sq_abs]

theorem spectralOp_pairing {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a c : Fin d → ℝ) :
    ⟪operatorFrobenius (spectralOp b a), operatorFrobenius (spectralOp b c)⟫_ℝ =
      ∑ i, a i * c i := by
  rw [← sum_inner_operator_basis _ _ b]
  simp only [spectralOp_basis, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, b.norm_eq_one, one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Actual positive spectral part of a self-adjoint operator. -/
def positivePart {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) : Op d :=
  spectralOp (hT.eigenvectorBasis finrank_euclideanSpace_fin)
    (fun i => max (hT.eigenvalues finrank_euclideanSpace_fin i) 0)

def negativePart {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) : Op d :=
  spectralOp (hT.eigenvectorBasis finrank_euclideanSpace_fin)
    (fun i => max (-hT.eigenvalues finrank_euclideanSpace_fin i) 0)

theorem spectral_reconstruction {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    spectralOp (hT.eigenvectorBasis finrank_euclideanSpace_fin)
      (hT.eigenvalues finrank_euclideanSpace_fin) = T := by
  apply ContinuousLinearMap.coe_injective
  apply (hT.eigenvectorBasis finrank_euclideanSpace_fin).toBasis.ext
  intro i
  exact (spectralOp_basis _ _ i).trans (hT.apply_eigenvectorBasis _ i).symm

theorem positivePart_positive {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    IsPSD (positivePart T hT) := spectralOp_positive _ _ (fun _ => le_max_right _ _)

theorem negativePart_positive {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    IsPSD (negativePart T hT) := spectralOp_positive _ _ (fun _ => le_max_right _ _)

theorem spectralOp_sub {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a c : Fin d → ℝ) : spectralOp b a - spectralOp b c = spectralOp b (fun i => a i-c i) := by
  apply ContinuousLinearMap.coe_injective
  apply b.toBasis.ext
  intro i
  simp [sub_smul]

theorem positive_sub_negative {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    positivePart T hT - negativePart T hT = T := by
  rw [positivePart, negativePart, spectralOp_sub]
  convert spectral_reconstruction T hT using 2
  funext i
  simp only [max_def]
  split_ifs <;> linarith

theorem positive_negative_orthogonal {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ⟪operatorFrobenius (positivePart T hT), operatorFrobenius (negativePart T hT)⟫_ℝ = 0 := by
  rw [positivePart, negativePart, spectralOp_pairing]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : 0 ≤ hT.eigenvalues finrank_euclideanSpace_fin i
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · simp [max_eq_right (le_of_not_ge h)]

theorem positive_pairing {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ⟪operatorFrobenius T, operatorFrobenius (positivePart T hT)⟫_ℝ =
      ‖operatorFrobenius (positivePart T hT)‖^2 := by
  nth_rw 1 [← spectral_reconstruction T hT]
  rw [positivePart, spectralOp_pairing, spectralOp_frobenius_sq]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ hT.eigenvalues finrank_euclideanSpace_fin i
  · simp [max_eq_left h, pow_two]
  · simp [max_eq_right (le_of_not_ge h)]

@[simp] theorem operatorFrobenius_smul {d : ℕ} (a : ℝ) (T : Op d) :
    operatorFrobenius (a • T) = a • operatorFrobenius T := by ext j i; rfl

@[simp] theorem operatorFrobenius_sub {d : ℕ} (T U : Op d) :
    operatorFrobenius (T-U) = operatorFrobenius T - operatorFrobenius U := by ext j i; rfl

theorem eigenvalue_nonneg {d : ℕ} {T : Op d} (hT : IsPSD T) (i : Fin d) :
    0 ≤ hT.1.eigenvalues finrank_euclideanSpace_fin i := by
  have h := hT.2 (hT.1.eigenvectorBasis finrank_euclideanSpace_fin i)
  change 0 ≤ ⟪T.toLinearMap (hT.1.eigenvectorBasis finrank_euclideanSpace_fin i),
    hT.1.eigenvectorBasis finrank_euclideanSpace_fin i⟫_ℝ at h
  simpa only [hT.1.apply_eigenvectorBasis, real_inner_smul_left,
    real_inner_self_eq_norm_sq, (hT.1.eigenvectorBasis finrank_euclideanSpace_fin).norm_eq_one,
    one_pow, mul_one] using! h

theorem spectral_pairing_general {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ (Euclid d))
    (a : Fin d → ℝ) (S : Op d) :
    ⟪operatorFrobenius (spectralOp b a), operatorFrobenius S⟫_ℝ =
      ∑ i, a i * ⟪S (b i), b i⟫_ℝ := by
  rw [← sum_inner_operator_basis _ _ b]
  apply Finset.sum_congr rfl
  intro i _
  rw [spectralOp_basis, real_inner_smul_left, real_inner_comm]

/-- Self-duality direction for the actual PSD cone. -/
theorem psd_pairing_nonneg {d : ℕ} {T S : Op d} (hT : IsPSD T) (hS : IsPSD S) :
    0 ≤ ⟪operatorFrobenius T, operatorFrobenius S⟫_ℝ := by
  nth_rw 1 [← spectral_reconstruction T hT.1]
  rw [spectral_pairing_general]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (eigenvalue_nonneg hT i) (hS.2 _)

theorem pairing_le_positive {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric)
    {S : Op d} (hS : IsPSD S) :
    ⟪operatorFrobenius T, operatorFrobenius S⟫_ℝ ≤
      ⟪operatorFrobenius (positivePart T hT), operatorFrobenius S⟫_ℝ := by
  have h := psd_pairing_nonneg (negativePart_positive T hT) hS
  have heq := congrArg operatorFrobenius (positive_sub_negative T hT)
  rw [operatorFrobenius_sub] at heq
  rw [← heq, inner_sub_left]
  linarith

theorem positive_norm_le_add {d : ℕ} (T U : Op d)
    (hT : T.toLinearMap.IsSymmetric) (hU : U.toLinearMap.IsSymmetric) :
    ‖operatorFrobenius (positivePart T hT)‖ ≤
      ‖operatorFrobenius (positivePart U hU)‖ + ‖operatorFrobenius (T-U)‖ := by
  let P := operatorFrobenius (positivePart T hT)
  let Q := operatorFrobenius (positivePart U hU)
  have h1 := pairing_le_positive U hU (positivePart_positive T hT)
  have h2 := real_inner_le_norm Q P
  have h3 := real_inner_le_norm (operatorFrobenius (T-U)) P
  have heq : ⟪operatorFrobenius T, P⟫_ℝ =
      ⟪operatorFrobenius (T-U), P⟫_ℝ + ⟪operatorFrobenius U, P⟫_ℝ := by
    rw [operatorFrobenius_sub, inner_sub_left]
    ring
  have hsq : ‖P‖^2 ≤ (‖Q‖ + ‖operatorFrobenius (T-U)‖) * ‖P‖ := by
    have hp := positive_pairing T hT
    change ⟪operatorFrobenius T, P⟫_ℝ = ‖P‖^2 at hp
    change ⟪operatorFrobenius U, P⟫_ℝ ≤ ⟪Q, P⟫_ℝ at h1
    nlinarith
  by_cases hp : ‖P‖ = 0
  · change ‖P‖ ≤ ‖Q‖ + _
    rw [hp]
    positivity
  · have hp' : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
    nlinarith

/-- The support norm of the PSD unit ball is genuinely 1-Lipschitz in Frobenius norm. -/
theorem positive_norm_lipschitz {d : ℕ} (T U : Op d)
    (hT : T.toLinearMap.IsSymmetric) (hU : U.toLinearMap.IsSymmetric) :
    |‖operatorFrobenius (positivePart T hT)‖ - ‖operatorFrobenius (positivePart U hU)‖| ≤
      ‖operatorFrobenius T - operatorFrobenius U‖ := by
  apply abs_le.mpr
  have h1 := positive_norm_le_add T U hT hU
  have h2 := positive_norm_le_add U T hU hT
  rw [operatorFrobenius_sub] at h1 h2
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- Pythagorean positive/negative energy split, independent of semicircle limits. -/
theorem positive_negative_energy {d : ℕ} (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    ‖operatorFrobenius (positivePart T hT)‖^2 +
      ‖operatorFrobenius (negativePart T hT)‖^2 = ‖operatorFrobenius T‖^2 := by
  have heq := congrArg operatorFrobenius (positive_sub_negative T hT)
  rw [operatorFrobenius_sub] at heq
  rw [← heq, norm_sub_sq_real, positive_negative_orthogonal]
  ring

end BMGeometry
