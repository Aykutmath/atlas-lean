import BMConeSupport
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

/-- A closed convex set contains a point if every unit-direction support reaches that point.
Proved from the actual Hilbert projection theorem, rather than assumed separation. -/
theorem mem_of_unit_support {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} (hKne : K.Nonempty) (hKcomplete : IsComplete K) (hKconvex : Convex ℝ K)
    (b : E) (hsupport : ∀ u : E, ‖u‖=1 → ∃ z ∈ K, ⟪u,b⟫_ℝ ≤ ⟪u,z⟫_ℝ) : b ∈ K := by
  by_contra hb
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKcomplete hKconvex b
  have hne : b-v ≠ 0 := by intro h; apply hb; exact (sub_eq_zero.mp h).symm ▸ hv
  have hn : 0 < ‖b-v‖ := norm_pos_iff.mpr hne
  let u : E := ‖b-v‖⁻¹ • (b-v)
  have hu : ‖u‖=1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  obtain ⟨z,hz,hs⟩ := hsupport u hu
  have hs' : ⟪b-v,b⟫_ℝ ≤ ⟪b-v,z⟫_ℝ := by
    change ⟪‖b-v‖⁻¹ • (b-v),b⟫_ℝ ≤ ⟪‖b-v‖⁻¹ • (b-v),z⟫_ℝ at hs
    rw [real_inner_smul_left, real_inner_smul_left] at hs
    exact (mul_le_mul_iff_right₀ (inv_pos.mpr hn)).mp hs
  have hp := (norm_eq_iInf_iff_real_inner_le_zero hKconvex hv).mp hmin z hz
  rw [inner_sub_right] at hp
  have he : ⟪b-v,b⟫_ℝ - ⟪b-v,v⟫_ℝ = ‖b-v‖^2 := by
    rw [← inner_sub_right, real_inner_self_eq_norm_sq]
  nlinarith

def conditionedFrobeniusBall (d : ℕ) (κ R : ℝ) : Set (HMat d) :=
  {S | frobeniusOperator S ∈ conditionCone d κ} ∩ Metric.closedBall 0 R

theorem conditionedFrobeniusBall_compact (d : ℕ) (κ R : ℝ) :
    IsCompact (conditionedFrobeniusBall d κ R) :=
  (isCompact_closedBall (0 : HMat d) R).inter_left
    ((isClosed_conditionCone d κ).preimage (continuous_frobeniusOperator d d))

theorem conditionedFrobeniusBall_convex (d : ℕ) (κ R : ℝ) :
    Convex ℝ (conditionedFrobeniusBall d κ R) :=
  ((convex_conditionCone d κ).linear_preimage (operatorFrobeniusLinearEquiv d d).symm.toLinearMap).inter
    (convex_closedBall (0 : HMat d) R)

theorem conditionedFrobeniusBall_zero (d : ℕ) (κ : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (0 : HMat d) ∈ conditionedFrobeniusBall d κ R := by
  constructor
  · have he : frobeniusOperator (0 : HMat d) = 0 := by
      apply (operatorFrobeniusLinearEquiv d d).injective
      simp only [operatorFrobeniusLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, operatorFrobenius_frobeniusOperator]
      rfl
    change frobeniusOperator (0 : HMat d) ∈ conditionCone d κ
    rw [he]
    exact zero_mem_conditionCone d κ
  · simpa only [Metric.mem_closedBall, dist_self] using hR

/-- Exact affine feasibility with a quantitative Frobenius radius, from a directional support
condition. This is the deterministic endpoint of the proposed expectation-Gordon route. -/
theorem affine_feasible_of_unit_support {d n : ℕ} {κ R : ℝ} (hR : 0 < R)
    (A : HMat d →L[ℝ] Euclid n) (b : Euclid n)
    (hsupport : ∀ u : Euclid n, ‖u‖=1 → ∃ S ∈ conditionedUnit d κ,
      ⟪u,b⟫_ℝ ≤ R*⟪u,A (operatorFrobenius S)⟫_ℝ) :
    ∃ S : Op d, S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖ ≤ R ∧
      A (operatorFrobenius S) = b := by
  let K := A '' conditionedFrobeniusBall d κ R
  have hKcompact : IsCompact K := (conditionedFrobeniusBall_compact d κ R).image A.continuous
  have hKconvex : Convex ℝ K := (conditionedFrobeniusBall_convex d κ R).linear_image A.toLinearMap
  have hKne : K.Nonempty := ⟨A 0,0,conditionedFrobeniusBall_zero d κ hR.le,rfl⟩
  have hb : b ∈ K := mem_of_unit_support hKne hKcompact.isComplete hKconvex b (by
    intro u hu
    obtain ⟨S,hS,hs⟩ := hsupport u hu
    refine ⟨A (R • operatorFrobenius S), ⟨R • operatorFrobenius S, ?_, rfl⟩, ?_⟩
    · constructor
      · have he : frobeniusOperator (R • operatorFrobenius S) = R • S := by
          change (operatorFrobeniusLinearEquiv d d).symm (R • operatorFrobenius S) = R • S
          rw [map_smul]
          change R • frobeniusOperator (operatorFrobenius S) = R • S
          rw [frobeniusOperator_operatorFrobenius]
        change frobeniusOperator (R • operatorFrobenius S) ∈ conditionCone d κ
        rw [he]
        exact conditionCone_smul hR.le hS.1
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR, hS.2, mul_one]
    · simpa only [map_smul, real_inner_smul_right] using hs)
  obtain ⟨S,hS,hAb⟩ := hb
  refine ⟨frobeniusOperator S,hS.1,?_,?_⟩
  · simpa only [operatorFrobenius_frobeniusOperator, Metric.mem_closedBall, dist_zero_right] using hS.2
  · simpa only [operatorFrobenius_frobeniusOperator] using hAb

end BMGeometry
