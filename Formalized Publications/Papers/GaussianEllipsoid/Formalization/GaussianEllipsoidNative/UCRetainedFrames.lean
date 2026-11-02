import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
set_option maxHeartbeats 1200000
open scoped InnerProductSpace
namespace UCEscape

/-- The coordinate subspace supported on the retained set. -/
def retainedCoordinateSubspace {n : ℕ} (A : Finset (Fin n)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range (fun i : A => (EuclideanSpace.single i.val (1 : ℝ) : EuclideanSpace ℝ (Fin n))))

theorem retainedCoordinateSubspace_finrank {n : ℕ} (A : Finset (Fin n)) :
    Module.finrank ℝ (retainedCoordinateSubspace A) = A.card := by
  have hli : LinearIndependent ℝ
      (fun i : A => (EuclideanSpace.single i.val (1 : ℝ) : EuclideanSpace ℝ (Fin n))) :=
    (EuclideanSpace.orthonormal_single.comp (fun i : A => i.val) Subtype.val_injective).linearIndependent
  rw [retainedCoordinateSubspace, finrank_span_eq_card hli]
  simp

theorem retainedCoordinateSubspace_supported {n : ℕ} (A : Finset (Fin n))
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ retainedCoordinateSubspace A)
    (i : Fin n) (hi : i ∉ A) : v i = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    have hne : i ≠ j.val := by intro h; exact hi (h ▸ j.prop)
    simp [hne]
  | zero => simp
  | add x y hx hy hx0 hy0 => simpa using congrArg₂ (· + ·) hx0 hy0
  | smul a x hx hx0 => simp [hx0]

/-- Intersecting with L-perp loses at most dim L retained coordinates. -/
theorem retained_orthogonal_finrank_lower {n r : ℕ}
    (A : Finset (Fin n)) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : r + Module.finrank ℝ L ≤ A.card) :
    r ≤ Module.finrank ℝ (retainedCoordinateSubspace A ⊓ Lᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq (retainedCoordinateSubspace A) Lᗮ
  have hle := (retainedCoordinateSubspace A ⊔ Lᗮ).finrank_le
  have horth := L.finrank_add_finrank_orthogonal
  rw [retainedCoordinateSubspace_finrank A] at hadd
  omega

/-- Every finite-dimensional subspace containing at least r independent directions
contains a genuine orthonormal frame of rank r. -/
theorem exists_frame_in_subspace {n r : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : r ≤ Module.finrank ℝ K) :
    ∃ U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x, U x ∈ K := by
  classical
  let b := stdOrthonormalBasis ℝ K
  let f : EuclideanSpace ℝ (Fin r) →ₗ[ℝ] K :=
    { toFun := fun x => ∑ i, x i • b (Fin.castLE h i)
      map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [mul_smul, Finset.smul_sum] }
  have hb : Orthonormal ℝ (fun i : Fin r => b (Fin.castLE h i)) :=
    b.orthonormal.comp (Fin.castLE h) (Fin.castLE_injective h)
  have hf : ∀ x y, ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ := by
    intro x y
    change ⟪∑ i, x i • b (Fin.castLE h i), ∑ i, y i • b (Fin.castLE h i)⟫_ℝ = _
    rw [hb.inner_sum]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    congr 1
    funext i
    ring
  let V := f.isometryOfInner hf
  exact ⟨K.subtypeₗᵢ.comp V, fun x => (V x).prop⟩

/-- Actual retained-coordinate frame existence; the sole dimension premise is
r + dim L ≤ number of retained coordinates. -/
theorem exists_retained_orthogonal_frame {n r : ℕ}
    (A : Finset (Fin n)) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : r + Module.finrank ℝ L ≤ A.card) :
    ∃ U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, U x ∈ Lᗮ) ∧ (∀ x i, i ∉ A → U x i = 0) := by
  obtain ⟨U, hU⟩ := exists_frame_in_subspace (retainedCoordinateSubspace A ⊓ Lᗮ)
    (retained_orthogonal_finrank_lower A L h)
  exact ⟨U, fun x => (hU x).2, fun x i hi =>
    retainedCoordinateSubspace_supported A (hU x).1 i hi⟩

/-- The adjoint of an isometric frame is a contraction, including rank zero. -/
theorem frame_adjoint_norm_le {n r : ℕ}
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) : ‖U.toContinuousLinearMap.adjoint w‖ ≤ ‖w‖ := by
  have hi : ‖U.toContinuousLinearMap.adjoint w‖ ^ 2 ≤
      ‖w‖ * ‖U.toContinuousLinearMap.adjoint w‖ := by
    calc
      _ = ⟪w, U (U.toContinuousLinearMap.adjoint w)⟫_ℝ := by
        change _ = ⟪w, U.toContinuousLinearMap (U.toContinuousLinearMap.adjoint w)⟫_ℝ
        rw [← U.toContinuousLinearMap.adjoint_inner_left]
        exact (real_inner_self_eq_norm_sq _).symm
      _ ≤ ‖w‖ * ‖U (U.toContinuousLinearMap.adjoint w)‖ := real_inner_le_norm _ _
      _ = _ := by rw [U.norm_map]
  nlinarith [norm_nonneg w, norm_nonneg (U.toContinuousLinearMap.adjoint w)]

/-- Frames contained in L-perp annihilate every deterministic shift in L. -/
theorem frame_adjoint_eq_zero_of_mem {n r : ℕ}
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hU : ∀ x, U x ∈ Lᗮ)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ L) : U.toContinuousLinearMap.adjoint v = 0 := by
  apply ext_inner_right ℝ
  intro x
  rw [U.toContinuousLinearMap.adjoint_inner_left, inner_zero_left]
  exact Submodule.inner_right_of_mem_orthogonal hv (hU x)

theorem frame_adjoint_sub_mem {n r : ℕ}
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hU : ∀ x, U x ∈ Lᗮ)
    (w v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ L) :
    U.toContinuousLinearMap.adjoint (w - v) = U.toContinuousLinearMap.adjoint w := by
  rw [map_sub, frame_adjoint_eq_zero_of_mem U L hU hv, sub_zero]

/-- The adjoint of a supported frame depends only on retained coordinates. -/
theorem frame_adjoint_eq_of_eq_on_retained {n r : ℕ}
    (A : Finset (Fin n))
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x i, i ∉ A → U x i = 0)
    (v w : EuclideanSpace ℝ (Fin n)) (hvw : ∀ i ∈ A, v i = w i) :
    U.toContinuousLinearMap.adjoint v = U.toContinuousLinearMap.adjoint w := by
  apply ext_inner_right ℝ
  intro x
  simp only [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · rw [hvw i hi]
  · simp [hU x i hi]

/-- Retain the A coordinates and set all other coordinates to zero. -/
def retainedCoordinates {n : ℕ} (A : Finset (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => if i ∈ A then w i else 0)

theorem retainedCoordinates_norm_sq {n : ℕ} (A : Finset (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) : ‖retainedCoordinates A w‖ ^ 2 = ∑ i ∈ A, (w i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [retainedCoordinates]

/-- Supported orthonormal frames contract the retained-coordinate norm. -/
theorem frame_adjoint_norm_le_retained {n r : ℕ}
    (A : Finset (Fin n))
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x i, i ∉ A → U x i = 0) (w : EuclideanSpace ℝ (Fin n)) :
    ‖U.toContinuousLinearMap.adjoint w‖ ≤ ‖retainedCoordinates A w‖ := by
  rw [frame_adjoint_eq_of_eq_on_retained A U hU w (retainedCoordinates A w)
    (fun i hi => by simp [retainedCoordinates, hi])]
  exact frame_adjoint_norm_le U _

/-- Squared form suitable for deterministic retained residual-coordinate bounds. -/
theorem frame_adjoint_norm_sq_le_sum_retained {n r : ℕ}
    (A : Finset (Fin n))
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (hU : ∀ x i, i ∉ A → U x i = 0) (w : EuclideanSpace ℝ (Fin n)) :
    ‖U.toContinuousLinearMap.adjoint w‖ ^ 2 ≤ ∑ i ∈ A, (w i) ^ 2 := by
  rw [← retainedCoordinates_norm_sq]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (frame_adjoint_norm_le_retained A U hU w)

/-- Projected measurement energy is bounded by any shifted retained residual energy. -/
theorem frame_adjoint_norm_sq_le_shifted_retained {n r : ℕ}
    (A : Finset (Fin n))
    (U : EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (horth : ∀ x, U x ∈ Lᗮ) (hsupp : ∀ x i, i ∉ A → U x i = 0)
    (w v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ L) :
    ‖U.toContinuousLinearMap.adjoint w‖ ^ 2 ≤ ∑ i ∈ A, (w i - v i) ^ 2 := by
  rw [← frame_adjoint_sub_mem U L horth w v hv]
  exact frame_adjoint_norm_sq_le_sum_retained A U hsupp (w - v)

/-- Frames can be selected simultaneously for an arbitrary deterministic family of
retained sets, without any extra dimension premise. -/
theorem exists_retained_orthogonal_frame_family {J : Type*} {n r : ℕ}
    (A : J → Finset (Fin n)) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ j, r + Module.finrank ℝ L ≤ (A j).card) :
    ∃ U : J → EuclideanSpace ℝ (Fin r) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ j x, U j x ∈ Lᗮ) ∧ (∀ j x i, i ∉ A j → U j x i = 0) := by
  choose U horth hsupp using fun j => exists_retained_orthogonal_frame (A j) L (h j)
  exact ⟨U, horth, hsupp⟩

#print axioms exists_retained_orthogonal_frame
#print axioms exists_retained_orthogonal_frame_family
#print axioms frame_adjoint_norm_sq_le_shifted_retained
#print axioms frame_adjoint_sub_mem
#print axioms frame_adjoint_norm_sq_le_sum_retained
end UCEscape
