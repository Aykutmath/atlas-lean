import GaussianCappedRealMoment

/-! Reconstructed proof development, 2026-10-03. New source, not recovered
original. Drafts are unverified until the recorded pinned compiler checks. -/
noncomputable section
open MeasureTheory ProbabilityTheory Finset
open GaussianTensorMoments GaussianEllipsoid.CappedSimplex GaussianEllipsoid.SmallBall
namespace GaussianMixedNormHelpers

/-- Uniform-subset Wishart moments at the paper exponent, bounded by the
smallest residual shape. All exponents remain real. -/
theorem reconstructed_uniform_real_moment_coarse
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (r m : ℕ) (hr : 2 ≤ r) (hm : 2*r ≤ m)
    (T : Finset κ) (e : Fin m ≃ T) :
    extendedRealMoment (Measure.pi (fun _ : κ => gaussianProductLaw (Fin r)))
      ((r:ℝ)/2) (fun i => if i ∈ T then (m:ℝ)⁻¹ else 0) ≤
    ENNReal.ofReal (((m:ℝ)/((m:ℝ)-2*r+1))^((r:ℝ)*((r:ℝ)/2))) := by
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have hmR : 2*(r:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m:ℝ) := by linarith
  have hq : 0 < (m:ℝ)-2*r+1 := by linarith
  have hs : 1 ≤ (r:ℝ)/2 := by linarith
  have hshape : ∀ j : Fin r, (r:ℝ)/2 < ((m-j.val:ℕ):ℝ)/2 := by
    intro j
    rw [Nat.cast_sub (by omega)]
    have hj : (j.val:ℝ) < r := by exact_mod_cast j.isLt
    linarith
  rw [selected_uniform_extended_real_moment r m (by omega) ((r:ℝ)/2)
    ((m:ℝ)⁻¹) (by positivity) (by positivity) hshape T e]
  apply ENNReal.ofReal_le_ofReal
  have hprod : (∏ j : Fin r, (2:ℝ)^(-((r:ℝ)/2)) *
      (Real.Gamma (((m-j.val:ℕ):ℝ)/2-(r:ℝ)/2) /
        Real.Gamma (((m-j.val:ℕ):ℝ)/2))) ≤
      (((m:ℝ)-2*r+1)^(-((r:ℝ)/2)))^r := by
    calc
      _ ≤ ∏ _j : Fin r, ((m:ℝ)-2*r+1)^(-((r:ℝ)/2)) := by
        apply Finset.prod_le_prod
        · intro j _
          exact mul_nonneg (by positivity)
            (div_nonneg (Real.Gamma_pos_of_pos (sub_pos.mpr (hshape j))).le
              (Real.Gamma_pos_of_pos (by linarith [hshape j])).le)
        · intro j _
          have hj : (j.val:ℝ)+1 ≤ r := by exact_mod_cast j.isLt
          have hqj : 0 < ((m-j.val:ℕ):ℝ)-(r:ℝ) := by linarith [hshape j]
          have hid : ((m-j.val:ℕ):ℝ)/2-(r:ℝ)/2 =
              (((m-j.val:ℕ):ℝ)-(r:ℝ))/2 := by ring
          have hid' : ((m-j.val:ℕ):ℝ)/2 =
              (((m-j.val:ℕ):ℝ)-(r:ℝ))/2+(r:ℝ)/2 := by ring
          rw [hid, hid']
          apply (reconstructed_gamma_factor_bound _ _ hqj hs).trans
          apply Real.rpow_le_rpow_of_nonpos hq
          · rw [Nat.cast_sub (by omega)]
            linarith
          · linarith
      _ = _ := by simp
  calc
    _ ≤ (((m:ℝ)⁻¹)^r)^(-((r:ℝ)/2)) *
        (((m:ℝ)-2*r+1)^(-((r:ℝ)/2)))^r :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = _ := by
      rw [inv_pow, Real.rpow_neg_eq_inv_rpow, inv_inv]
      have hmPow : ((m:ℝ)^r)^((r:ℝ)/2) = (m:ℝ)^((r:ℝ)*((r:ℝ)/2)) :=
        (Real.rpow_natCast_mul (Nat.cast_nonneg m) r ((r:ℝ)/2)).symm
      have hqPow : (((m:ℝ)-2*r+1)^(-((r:ℝ)/2)))^r =
          ((m:ℝ)-2*r+1)^(-((r:ℝ)*((r:ℝ)/2))) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
        congr 1
        ring
      rw [hmPow, hqPow, Real.rpow_neg hq.le, ← div_eq_mul_inv,
        ← Real.div_rpow (Nat.cast_nonneg m) hq.le]


/-- Exact floor choice for the reciprocal-cap comparison, including its
numerical margin required by the paper's displayed θ-dependent constant. -/
theorem reconstructed_paper_floor_margin (r : ℕ) (hr : 2 ≤ r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2) :
    let m := Nat.floor ((r:ℝ)/θ^2)
    2*r ≤ m ∧ θ^2/(r:ℝ) ≤ (m:ℝ)⁻¹ ∧
      (m:ℝ)/((m:ℝ)-2*r+1) ≤ (1-2*θ^2)⁻¹ := by
  dsimp only
  let m := Nat.floor ((r:ℝ)/θ^2)
  have hrR : (2:ℝ) ≤ r := by exact_mod_cast hr
  have ht : 0 < θ^2 := sq_pos_of_pos hθ0
  have ht2 : θ^2 < 1/2 := paper_theta_sq_lt_half hθ0 hθ
  have hx : 0 ≤ (r:ℝ)/θ^2 := by positivity
  have hmle : (m:ℝ) ≤ (r:ℝ)/θ^2 := Nat.floor_le hx
  have hmlt : (r:ℝ)/θ^2 < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hmdim : 2*r ≤ m := by
    apply (Nat.le_floor_iff hx).mpr
    push_cast
    apply (le_div_iff₀ ht).mpr
    nlinarith
  have hmR : 2*(r:ℝ) ≤ m := by exact_mod_cast hmdim
  have hmpos : 0 < (m:ℝ) := by linarith
  have hq : 0 < (m:ℝ)-2*r+1 := by linarith
  have hb : 0 < 1-2*θ^2 := by linarith
  refine ⟨hmdim, ?_, ?_⟩
  · rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by linarith : 0 < (r:ℝ)) hmpos).mpr
    have hh := (le_div_iff₀ ht).mp hmle
    nlinarith
  · rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hq hb).mpr
    have hh := (div_lt_iff₀ ht).mp hmlt
    nlinarith

theorem paper_uniform_capped_determinant_moment (r N : ℕ) (hr : 2 ≤ r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ < 1/Real.sqrt 2)
    (w : Fin N → ℝ) (hwSum : ∑ i, w i = 1)
    (hwCap : ∀ i, 0 ≤ w i ∧ w i ≤ θ^2/(r:ℝ)) :
    (∫⁻ g : Fin N → Fin r → ℝ,
      ((ENNReal.ofReal (weightedGram g w).det)^((r:ℝ)/2))⁻¹
        ∂Measure.pi (fun _ : Fin N => gaussianProductLaw (Fin r))) ≤
      ENNReal.ofReal ((1-2*θ^2)^(-((r:ℝ)*((r:ℝ)/2)))) := by
  let m := Nat.floor ((r:ℝ)/θ^2)
  have hmargin := reconstructed_paper_floor_margin r hr hθ0 hθ
  change 2*r ≤ m ∧ θ^2/(r:ℝ) ≤ (m:ℝ)⁻¹ ∧
    (m:ℝ)/((m:ℝ)-2*r+1) ≤ (1-2*θ^2)⁻¹ at hmargin
  have hm : 0 < m := by omega
  have hw : w ∈ slice ((m:ℝ)⁻¹) 1 :=
    ⟨fun i => ⟨(hwCap i).1, (hwCap i).2.trans hmargin.2.1⟩, hwSum⟩
  obtain ⟨T, hT⟩ := exists_card_subset_of_reciprocal_cap hm hw
  have hcard : Fintype.card T = m := by rw [Fintype.card_coe, hT]
  let e : Fin m ≃ T := (Fintype.equivFinOfCardEq hcard).symm
  change extendedRealMoment _ ((r:ℝ)/2) w ≤ _
  apply (reconstructed_extendedRealMoment_le_uniform_subset _ _ (by positivity)
    m hm hw T hT).trans
  apply (reconstructed_uniform_real_moment_coarse r m hr hmargin.1 T e).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ((1-2*θ^2)⁻¹)^((r:ℝ)*((r:ℝ)/2)) :=
      Real.rpow_le_rpow (by
        have hmR : 2*(r:ℝ) ≤ m := by exact_mod_cast hmargin.1
        apply div_nonneg (Nat.cast_nonneg _)
        linarith) hmargin.2.2 (by positivity)
    _ = _ := (Real.rpow_neg_eq_inv_rpow _ _).symm

end GaussianMixedNormHelpers
#print axioms GaussianMixedNormHelpers.paper_uniform_capped_determinant_moment
