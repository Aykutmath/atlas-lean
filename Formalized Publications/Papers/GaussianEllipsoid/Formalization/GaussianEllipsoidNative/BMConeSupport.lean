import BMConditionEigen
import BMIsotropicGaussian

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

def conditionedUnit (d : ℕ) (κ : ℝ) : Set (Op d) :=
  {S | S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖=1}

def conditionedSupport (d : ℕ) (κ : ℝ) (G : HMat d) : ℝ :=
  sSup {z : ℝ | ∃ S ∈ conditionedUnit d κ, z = ⟪G,operatorFrobenius S⟫_ℝ}

theorem id_mem_conditionCone {d : ℕ} {κ : ℝ} (hκ : 1 ≤ κ) :
    ContinuousLinearMap.id ℝ (Euclid d) ∈ conditionCone d κ := by
  refine ⟨isPSD_id d, ?_⟩
  intro x y hx hy
  simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, hx, hy,
    one_pow, mul_one] using hκ

theorem conditionedUnit_nonempty {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    (conditionedUnit d κ).Nonempty := by
  refine ⟨normalize (ContinuousLinearMap.id ℝ (Euclid d)),
    normalize_mem_conditionCone (id_mem_conditionCone hκ), ?_⟩
  apply normalize_unit
  apply norm_pos_iff.mp
  rw [frobenius_id_norm]
  exact Real.sqrt_pos.mpr (by exact_mod_cast hd)

theorem conditionedSupport_bddAbove (d : ℕ) (κ : ℝ) (G : HMat d) :
    BddAbove {z : ℝ | ∃ S ∈ conditionedUnit d κ, z = ⟪G,operatorFrobenius S⟫_ℝ} := by
  refine ⟨‖G‖, ?_⟩
  rintro z ⟨S,hS,rfl⟩
  simpa [hS.2] using real_inner_le_norm G (operatorFrobenius S)

theorem le_conditionedSupport {d : ℕ} {κ : ℝ} (G : HMat d) {S : Op d}
    (hS : S ∈ conditionedUnit d κ) : ⟪G,operatorFrobenius S⟫_ℝ ≤ conditionedSupport d κ G :=
  le_csSup (conditionedSupport_bddAbove d κ G) ⟨S,hS,rfl⟩

theorem conditionedSupport_le_norm {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (G : HMat d) :
    conditionedSupport d κ G ≤ ‖G‖ := by
  obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd hκ
  change sSup {z : ℝ | ∃ S ∈ conditionedUnit d κ, z = ⟪G,operatorFrobenius S⟫_ℝ} ≤ _
  apply csSup_le
  · exact ⟨_,S,hS,rfl⟩
  rintro z ⟨T,hT,rfl⟩
  simpa [hT.2] using real_inner_le_norm G (operatorFrobenius T)

theorem neg_norm_le_conditionedSupport {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (G : HMat d) :
    -‖G‖ ≤ conditionedSupport d κ G := by
  obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd hκ
  have h := (abs_le.mp (norm_inner_le_norm (𝕜 := ℝ) G (operatorFrobenius S))).1
  simp only [Real.norm_eq_abs, hS.2, mul_one] at h
  exact h.trans (le_conditionedSupport G hS)

theorem conditionedSupport_le_add {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) (G H : HMat d) :
    conditionedSupport d κ G ≤ conditionedSupport d κ H + ‖G-H‖ := by
  obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd hκ
  change sSup {z : ℝ | ∃ S ∈ conditionedUnit d κ, z = ⟪G,operatorFrobenius S⟫_ℝ} ≤ _
  apply csSup_le
  · exact ⟨_,S,hS,rfl⟩
  rintro z ⟨T,hT,rfl⟩
  have h1 := le_conditionedSupport H hT
  have h2 := real_inner_le_norm (G-H) (operatorFrobenius T)
  rw [inner_sub_left, hT.2, mul_one] at h2
  linarith

theorem conditionedSupport_lipschitz {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ) :
    LipschitzWith 1 (conditionedSupport d κ) := by
  apply LipschitzWith.of_dist_le_mul
  intro G H
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  have h1 := conditionedSupport_le_add hd hκ G H
  have h2 := conditionedSupport_le_add hd hκ H G
  rw [norm_sub_rev] at h2
  constructor <;> linarith

theorem conditionedSupport_le_psd {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 1 ≤ κ)
    (T : Op d) (hT : T.toLinearMap.IsSymmetric) :
    conditionedSupport d κ (operatorFrobenius T) ≤ ‖operatorFrobenius (positivePart T hT)‖ := by
  obtain ⟨S,hS⟩ := conditionedUnit_nonempty hd hκ
  change sSup {z : ℝ | ∃ S ∈ conditionedUnit d κ, z = ⟪operatorFrobenius T,operatorFrobenius S⟫_ℝ} ≤ _
  apply csSup_le
  · exact ⟨_,S,hS,rfl⟩
  rintro z ⟨U,hU,rfl⟩
  exact psd_unitBall_support_le T hT hU.1.1 (le_of_eq hU.2)

theorem conditionedSupport_lower_of_good_event {d : ℕ} (hd : 0 < d)
    (T : Op d) (hT : T.toLinearMap.IsSymmetric) {a b C ε κ : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hκ : 0 ≤ κ) (hκε : C+ε ≤ κ*ε)
    (hop : ‖T‖ ≤ C * Real.sqrt d)
    (hlow : a * d ≤ ‖operatorFrobenius (positivePart T hT)‖)
    (hupper : ‖operatorFrobenius T‖ ≤ b * d) :
    ‖operatorFrobenius (positivePart T hT)‖ - ε*d*(1+b/a) ≤
      conditionedSupport d κ (operatorFrobenius T) := by
  obtain ⟨S,hS,hn,hsupp⟩ := exists_conditioned_unit_witness_of_good_event hd T hT ha hε hκ hκε hop hlow hupper
  exact hsupp.trans (le_conditionedSupport _ ⟨hS,hn⟩)

end BMGeometry
