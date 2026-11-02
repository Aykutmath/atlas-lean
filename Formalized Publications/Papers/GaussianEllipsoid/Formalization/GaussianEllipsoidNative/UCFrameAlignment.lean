import UCFrameCover
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Normed.Module.Normalize

/-! Quantitative orthogonal alignment of fixed-size frames by pairs of reflections. -/
noncomputable section
set_option maxHeartbeats 800000
open GaussianEllipsoid
open scoped BigOperators InnerProductSpace
namespace GaussianEllipsoid.UCFrameGeometry

def isoCLM {d : ℕ} (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) : Euclid d →L[ℝ] Euclid d :=
  O.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem isoCLM_apply {d : ℕ} (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) (x : Euclid d) :
    isoCLM O x = O x := rfl

theorem isoCLM_norm_le {d : ℕ} (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) : ‖isoCLM O‖ ≤ 1 :=
  O.toLinearIsometry.norm_toContinuousLinearMap_le

theorem reflection_unit_apply {d : ℕ} {a : Euclid d} (ha : ‖a‖ = 1) (x : Euclid d) :
    (ℝ ∙ a).reflection x = (2:ℝ) • (⟪a,x⟫_ℝ • a) - x := by
  simp [Submodule.reflection_singleton_apply, ha, two_smul, two_mul, add_smul]

theorem reflection_unit_difference_le {d : ℕ} {a b : Euclid d}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (x : Euclid d) :
    ‖(ℝ ∙ a).reflection x - (ℝ ∙ b).reflection x‖ ≤ 4*‖a-b‖*‖x‖ := by
  rw [reflection_unit_apply ha, reflection_unit_apply hb]
  have he : (2:ℝ) • (⟪a,x⟫_ℝ • a) - x - ((2:ℝ) • (⟪b,x⟫_ℝ • b) - x) =
      (2:ℝ) • (⟪a,x⟫_ℝ • (a-b) + ⟪a-b,x⟫_ℝ • b) := by
    rw [inner_sub_left]
    module
  rw [he, norm_smul, Real.norm_eq_abs]
  norm_num only [show |(2:ℝ)| = 2 by norm_num]
  have hnorm := norm_add_le (⟪a,x⟫_ℝ • (a-b)) (⟪a-b,x⟫_ℝ • b)
  simp only [norm_smul, Real.norm_eq_abs, hb, mul_one] at hnorm
  have h1 := abs_real_inner_le_norm a x
  rw [ha, one_mul] at h1
  have h2 := abs_real_inner_le_norm (a-b) x
  have h3 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (a-b))
  nlinarith

/-- The normalized midpoint of nearby unit vectors remains quantitatively close. -/
theorem normalized_midpoint_close {d : ℕ} {a b : Euclid d}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ‖a-b‖ ≤ 1) :
    a+b ≠ 0 ∧ ‖NormedSpace.normalize (a+b) - b‖ ≤ 2*‖a-b‖ := by
  let t : ℝ := ‖a+b‖
  have he : a+b-(2:ℝ) • b = a-b := by module
  have hrev : |t-2| ≤ ‖a-b‖ := by
    simpa only [t, he, norm_smul, Real.norm_eq_abs, show |(2:ℝ)| = 2 by norm_num, hb, mul_one] using
      abs_norm_sub_norm_le (a+b) ((2:ℝ) • b)
  have ht1 : 1 ≤ t := by have h := (abs_le.mp hrev).1; linarith
  have ht : 0 < t := by linarith
  have hz : a+b ≠ 0 := by intro h; simp [t,h] at ht
  refine ⟨hz,?_⟩
  have heq : NormedSpace.normalize (a+b)-b =
      t⁻¹ • (a-b) + (2*t⁻¹-1) • b := by
    unfold NormedSpace.normalize
    change t⁻¹ • (a+b)-b = _
    module
  have hcoeff : |2*t⁻¹-1| ≤ ‖a-b‖/t := by
    have hh : 2*t⁻¹-1 = (2-t)/t := by field_simp
    rw [hh, abs_div, abs_of_pos ht]
    apply div_le_div_of_nonneg_right _ ht.le
    simpa only [abs_sub_comm] using hrev
  have hd : ‖a-b‖/t ≤ ‖a-b‖ := div_le_self (norm_nonneg _) ht1
  rw [heq]
  calc
    _ ≤ ‖t⁻¹ • (a-b)‖ + ‖(2*t⁻¹-1) • b‖ := norm_add_le _ _
    _ = ‖a-b‖/t + |2*t⁻¹-1| := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), hb, mul_one]
      ring
    _ ≤ 2*‖a-b‖ := by linarith

/-- A nearby unit-vector alignment fixes every common orthogonal vector.
Its operator distance from identity is bounded independently of ambient d. -/
theorem exists_small_vector_alignment {d : ℕ} {a b : Euclid d}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ‖a-b‖ ≤ 1) :
    ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
      O a = b ∧
      (∀ x, ⟪a,x⟫_ℝ = 0 → ⟪b,x⟫_ℝ = 0 → O x = x) ∧
      ‖isoCLM O - ContinuousLinearMap.id ℝ (Euclid d)‖ ≤ 8*‖a-b‖ := by
  obtain ⟨hz,hclose⟩ := normalized_midpoint_close ha hb hab
  let s := NormedSpace.normalize (a+b)
  have hs : ‖s‖ = 1 := NormedSpace.norm_normalize hz
  let R := (ℝ ∙ s).reflection
  let S := (ℝ ∙ b).reflection
  let O := R.trans S
  have hspan : (ℝ ∙ s) = ℝ ∙ (a+b) := by
    apply Submodule.span_singleton_smul_eq
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hz))
  have hR : R a = b := by
    have hh := Submodule.reflection_sub (v := a) (w := -b) (by simpa [hb] using ha)
    rw [sub_neg_eq_add, Submodule.reflection_orthogonal_apply] at hh
    change (ℝ ∙ s).reflection a = b
    simpa only [hspan] using (neg_inj.mp hh)
  have hS : S b = b := Submodule.reflection_mem_subspace_eq_self
    (Submodule.mem_span_singleton_self b)
  refine ⟨O,?_,?_,?_⟩
  · change S (R a) = b
    rw [hR,hS]
  · intro x hax hbx
    have hsx : ⟪s,x⟫_ℝ = 0 := by
      dsimp [s,NormedSpace.normalize]
      simp only [real_inner_smul_left, inner_add_left, hax, hbx, add_zero, mul_zero]
    have hRx : R x = -x := by
      change (ℝ ∙ s).reflection x = -x
      simp [Submodule.reflection_singleton_apply,hsx]
    have hSx : S x = -x := by
      change (ℝ ∙ b).reflection x = -x
      simp [Submodule.reflection_singleton_apply,hbx]
    change S (R x) = x
    rw [hRx,map_neg,hSx,neg_neg]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    change ‖O x-x‖ ≤ (8*‖a-b‖)*‖x‖
    have hdiff : ‖O x-x‖ = ‖R x-S x‖ := by
      calc
        _ = ‖S (R x)-S (S x)‖ := by
          change ‖S (R x)-x‖ = _
          rw [Submodule.reflection_reflection]
        _ = ‖S (R x-S x)‖ := by rw [map_sub]
        _ = _ := S.norm_map _
    rw [hdiff]
    have hh := reflection_unit_difference_le hs hb x
    have hc := mul_le_mul_of_nonneg_right hclose (norm_nonneg x)
    change ‖R x-S x‖ ≤ _ at hh
    nlinarith

theorem isoCLM_trans_sub_id_le {d : ℕ}
    (O P : Euclid d ≃ₗᵢ[ℝ] Euclid d) :
    ‖isoCLM (O.trans P) - ContinuousLinearMap.id ℝ (Euclid d)‖ ≤
      ‖isoCLM P - ContinuousLinearMap.id ℝ (Euclid d)‖ +
      ‖isoCLM O - ContinuousLinearMap.id ℝ (Euclid d)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  change ‖P (O x)-x‖ ≤ _
  have hP := ContinuousLinearMap.le_opNorm
    (isoCLM P-ContinuousLinearMap.id ℝ (Euclid d)) (O x)
  have hO := ContinuousLinearMap.le_opNorm
    (isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)) x
  change ‖P (O x)-O x‖ ≤ ‖isoCLM P-ContinuousLinearMap.id ℝ (Euclid d)‖*‖O x‖ at hP
  change ‖O x-x‖ ≤ ‖isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)‖*‖x‖ at hO
  rw [O.norm_map] at hP
  calc
    _ ≤ ‖P (O x)-O x‖ + ‖O x-x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by nlinarith [hP,hO]

/-- Align the first k columns while preserving a dimension-independent norm bound. -/
theorem align_first_columns {d j : ℕ} (U V : FrobeniusMatrix d j)
    (hU : IsFrame U) (hV : IsFrame V) (hclose : ‖U-V‖ ≤ 1/(9:ℝ)^j) :
    ∀ k : ℕ, k ≤ j → ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
      (∀ i : Fin j, i.val < k → O (U i) = V i) ∧
      ‖isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)‖ ≤ ((9:ℝ)^k-1)*‖U-V‖ := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨LinearIsometryEquiv.refl ℝ (Euclid d),?_,?_⟩
      · intro i hi
        omega
      · change ‖ContinuousLinearMap.id ℝ (Euclid d)-ContinuousLinearMap.id ℝ (Euclid d)‖ ≤ _
        simp
  | succ k ih =>
      intro hk
      obtain ⟨O,hO,hOnorm⟩ := ih (by omega)
      let ik : Fin j := ⟨k,by omega⟩
      let a := O (U ik)
      let b := V ik
      have ha : ‖a‖ = 1 := by dsimp [a]; rw [O.norm_map, hU.norm_eq_one]
      have hb : ‖b‖ = 1 := hV.norm_eq_one ik
      have hcol : ‖U ik-V ik‖ ≤ ‖U-V‖ := column_norm_le_frobenius (U-V) ik
      have hdev : ‖a-U ik‖ ≤ ((9:ℝ)^k-1)*‖U-V‖ := by
        have hh := ContinuousLinearMap.le_opNorm
          (isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)) (U ik)
        change ‖a-U ik‖ ≤ ‖isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)‖*‖U ik‖ at hh
        rw [hU.norm_eq_one, mul_one] at hh
        exact hh.trans hOnorm
      have habδ : ‖a-b‖ ≤ (9:ℝ)^k*‖U-V‖ := by
        have ht := norm_sub_le_norm_sub_add_norm_sub a (U ik) b
        change ‖a-b‖ ≤ ‖a-U ik‖ + ‖U ik-V ik‖ at ht
        nlinarith [ht,hdev,hcol]
      have hpow : (9:ℝ)^k ≤ (9:ℝ)^j :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hq : (9:ℝ)^j*‖U-V‖ ≤ 1 := by
        have hh := (le_div_iff₀ (by positivity : (0:ℝ)<9^j)).mp hclose
        nlinarith
      have hab : ‖a-b‖ ≤ 1 := habδ.trans
        ((mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hq)
      obtain ⟨H,hHa,hHfix,hHnorm⟩ := exists_small_vector_alignment ha hb hab
      refine ⟨O.trans H,?_,?_⟩
      · intro i hi
        change H (O (U i)) = V i
        by_cases hik : i.val < k
        · have hki : ik ≠ i := by
            intro he
            have hv := congrArg Fin.val he
            dsimp [ik] at hv
            omega
          have haorth : ⟪a,V i⟫_ℝ = 0 := by
            rw [← hO i hik]
            change ⟪O (U ik),O (U i)⟫_ℝ = 0
            rw [O.inner_map_map]
            exact hU.inner_eq_zero hki
          have hborth : ⟪b,V i⟫_ℝ = 0 := hV.inner_eq_zero hki
          rw [hO i hik]
          exact hHfix (V i) haorth hborth
        · have he : i = ik := Fin.ext (by dsimp [ik]; omega)
          subst i
          exact hHa
      · have hh : ‖isoCLM H-ContinuousLinearMap.id ℝ (Euclid d)‖ ≤
            8*((9:ℝ)^k*‖U-V‖) :=
          hHnorm.trans (mul_le_mul_of_nonneg_left habδ (by norm_num))
        calc
          _ ≤ ‖isoCLM H-ContinuousLinearMap.id ℝ (Euclid d)‖ +
              ‖isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)‖ := isoCLM_trans_sub_id_le O H
          _ ≤ 8*((9:ℝ)^k*‖U-V‖) + ((9:ℝ)^k-1)*‖U-V‖ := add_le_add hh hOnorm
          _ = ((9:ℝ)^(k+1)-1)*‖U-V‖ := by rw [pow_succ]; ring

/-- Explicit fixed-rank alignment: C_j=9^j and epsilon_j=9^(-j).
The constants do not depend on ambient dimension d. -/
theorem frame_alignment {d j : ℕ} (U V : FrobeniusMatrix d j)
    (hU : IsFrame U) (hV : IsFrame V) (hclose : ‖U-V‖ ≤ 1/(9:ℝ)^j) :
    ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
      (∀ i, O (U i) = V i) ∧
      ‖isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)‖ ≤ (9:ℝ)^j*‖U-V‖ := by
  obtain ⟨O,hO,hOnorm⟩ := align_first_columns U V hU hV hclose j le_rfl
  refine ⟨O,fun i => hO i i.isLt,hOnorm.trans ?_⟩
  nlinarith [norm_nonneg (U-V)]

/-- Existential form with precisely the operator norm of the genuine Euclidean
isometry's continuous linear map, including the empty-frame case. -/
theorem exists_frame_alignment_constants (j : ℕ) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧
      ∀ (d : ℕ) (U V : FrobeniusMatrix d j), IsFrame U → IsFrame V → ‖U-V‖ ≤ ε →
      ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
        (∀ i, O (U i) = V i) ∧
        ‖O.toContinuousLinearEquiv.toContinuousLinearMap-ContinuousLinearMap.id ℝ (Euclid d)‖
          ≤ C*‖U-V‖ := by
  refine ⟨(9:ℝ)^j,1/(9:ℝ)^j,by positivity,by positivity,?_⟩
  intro d U V hU hV hclose
  exact frame_alignment U V hU hV hclose

/-- An exact column alignment carries the whole head subspace exactly. -/
theorem alignment_map_span {d j : ℕ} {U V : FrobeniusMatrix d j}
    (O : Euclid d ≃ₗᵢ[ℝ] Euclid d) (hO : ∀ i, O (U i) = V i) :
    Submodule.map O.toLinearEquiv.toLinearMap
      (Submodule.span ℝ (Set.range fun i => U i)) =
      Submodule.span ℝ (Set.range fun i => V i) := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨u,⟨i,rfl⟩,rfl⟩
    exact ⟨i,(hO i).symm⟩
  · rintro ⟨i,rfl⟩
    exact ⟨U i,⟨i,rfl⟩,hO i⟩

/-- A finite family of deterministic frames to which every orthonormal frame
can be carried by an orthogonal transformation within operator distance t of
identity. Its entropy is O_j(d), with no ambient-dimension loss in alignment. -/
theorem exists_aligned_frame_net (d j : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ N : Finset (FrobeniusMatrix d j),
      (∀ V ∈ N, IsFrame V) ∧
      (N.card:ℝ) ≤ (1+2*Real.sqrt (j:ℝ)/(min 1 t/(9:ℝ)^j))^(d*j) ∧
      ∀ U : FrobeniusMatrix d j, IsFrame U →
        ∃ V ∈ N, ∃ O : Euclid d ≃ₗᵢ[ℝ] Euclid d,
          (∀ i, O (U i) = V i) ∧
          ‖isoCLM O-ContinuousLinearMap.id ℝ (Euclid d)‖ < t := by
  let ε := min 1 t/(9:ℝ)^j
  have hp : (0:ℝ) < 9^j := by positivity
  have hε : 0 < ε := div_pos (lt_min (by norm_num) ht) hp
  have hεle : ε ≤ 1/(9:ℝ)^j :=
    div_le_div_of_nonneg_right (min_le_left _ _) hp.le
  obtain ⟨N,hN,hcard,hcover⟩ := exists_internal_frame_net d j hε
  refine ⟨N,hN,hcard,?_⟩
  intro U hU
  obtain ⟨V,hVN,hUV⟩ := hcover U hU
  obtain ⟨O,hO,hnorm⟩ := frame_alignment U V hU (hN V hVN) (hUV.le.trans hεle)
  refine ⟨V,hVN,O,hO,?_⟩
  calc
    _ ≤ (9:ℝ)^j*‖U-V‖ := hnorm
    _ < (9:ℝ)^j*ε := mul_lt_mul_of_pos_left hUV hp
    _ = min 1 t := by dsimp [ε]; field_simp
    _ ≤ t := min_le_right _ _

end GaussianEllipsoid.UCFrameGeometry
