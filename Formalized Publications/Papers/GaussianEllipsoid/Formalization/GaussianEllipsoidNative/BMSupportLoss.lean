import BMPSDProjection

noncomputable section
open scoped BigOperators InnerProductSpace
open GaussianEllipsoid
namespace BMGeometry

/-- Scalar normalization estimate, retaining the possibly negative trace term. -/
theorem perturb_quotient_lower {p s e g z : ℝ}
    (hp : 0 < p) (he : 0 ≤ e) (hg : 0 ≤ g)
    (hps : p ≤ s) (hsp : s ≤ p+e) (hz : -(g*e) ≤ z) :
    p - e * (1+g/p) ≤ (p^2+z)/s := by
  have hs : 0 < s := hp.trans_le hps
  have hfirst : p-e ≤ p^2/s := by
    apply (le_div_iff₀ hs).mpr
    have h1 := mul_le_mul_of_nonneg_left hsp hp.le
    have h2 := mul_le_mul_of_nonneg_left hps he
    nlinarith
  have hsecond : -(g*e)/p ≤ z/s := by
    apply (div_le_div_iff₀ hp hs).mpr
    have h1 := mul_le_mul_of_nonneg_left hps (mul_nonneg hg he)
    have h2 := mul_le_mul_of_nonneg_right hz hp.le
    nlinarith
  have hsum := add_le_add hfirst hsecond
  calc
    p-e*(1+g/p) = (p-e) + -(g*e)/p := by ring
    _ ≤ p^2/s + z/s := hsum
    _ = (p^2+z)/s := by ring

theorem opTrace_abs_le {d : ℕ} (T : Op d) : |opTrace T| ≤ ‖operatorFrobenius T‖ * Real.sqrt d := by
  have h := norm_inner_le_norm (𝕜 := ℝ) (operatorFrobenius T)
    (operatorFrobenius (ContinuousLinearMap.id ℝ (Euclid d)))
  simpa only [Real.norm_eq_abs, opTrace, frobenius_id_norm] using h

/-- A fully explicit finite-dimensional support lower bound for the normalized PSD perturbation. -/
theorem normalized_perturb_support_lower {d : ℕ} (T : Op d)
    (hT : T.toLinearMap.IsSymmetric) {t : ℝ} (ht : 0 ≤ t)
    (hp : 0 < ‖operatorFrobenius (positivePart T hT)‖) :
    ‖operatorFrobenius (positivePart T hT)‖ - t * Real.sqrt d *
      (1 + ‖operatorFrobenius T‖ / ‖operatorFrobenius (positivePart T hT)‖) ≤
      ⟪operatorFrobenius T, operatorFrobenius (normalize (perturb T hT t))⟫_ℝ := by
  rw [normalized_perturb_pairing]
  apply perturb_quotient_lower hp (mul_nonneg ht (Real.sqrt_nonneg _)) (norm_nonneg _)
    (perturb_norm_lower T hT ht) (perturb_norm_upper T hT ht)
  have h := mul_le_mul_of_nonneg_left (abs_le.mp (opTrace_abs_le T)).1 ht
  nlinarith

/-- The support bound produces an actual unit-Frobenius bounded-condition PSD matrix. -/
theorem exists_conditioned_unit_witness {d : ℕ} (T : Op d)
    (hT : T.toLinearMap.IsSymmetric) {t κ : ℝ} (ht : 0 ≤ t) (hκ : 0 ≤ κ)
    (hbound : ‖T‖ + t ≤ κ*t) (hp : 0 < ‖operatorFrobenius (positivePart T hT)‖) :
    ∃ S : Op d, S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖ = 1 ∧
      ‖operatorFrobenius (positivePart T hT)‖ - t * Real.sqrt d *
        (1 + ‖operatorFrobenius T‖ / ‖operatorFrobenius (positivePart T hT)‖) ≤
        ⟪operatorFrobenius T, operatorFrobenius S⟫_ℝ := by
  refine ⟨normalize (perturb T hT t), normalize_mem_conditionCone
    (perturb_mem_conditionCone T hT ht hκ hbound), ?_, normalized_perturb_support_lower T hT ht hp⟩
  apply normalize_unit
  apply norm_pos_iff.mp
  exact hp.trans_le (perturb_norm_lower T hT ht)

/-- Dimension-uniform deterministic specialization. On the usual Gaussian good event,
`p ≥ a d`, `||G||F ≤ b d`, `||G||op ≤ C √d`, one fixed κ works for all d. -/
theorem exists_conditioned_unit_witness_of_good_event {d : ℕ} (hd : 0 < d)
    (T : Op d) (hT : T.toLinearMap.IsSymmetric) {a b C ε κ : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hκ : 0 ≤ κ) (hκε : C+ε ≤ κ*ε)
    (hop : ‖T‖ ≤ C * Real.sqrt d)
    (hlow : a * d ≤ ‖operatorFrobenius (positivePart T hT)‖)
    (hupper : ‖operatorFrobenius T‖ ≤ b * d) :
    ∃ S : Op d, S ∈ conditionCone d κ ∧ ‖operatorFrobenius S‖ = 1 ∧
      ‖operatorFrobenius (positivePart T hT)‖ - ε * d * (1+b/a) ≤
        ⟪operatorFrobenius T, operatorFrobenius S⟫_ℝ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hsq : (Real.sqrt d)^2 = (d : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp : 0 < ‖operatorFrobenius (positivePart T hT)‖ := (mul_pos ha hd').trans_le hlow
  have hb : 0 ≤ b := by nlinarith [norm_nonneg (operatorFrobenius T)]
  have hr : ‖operatorFrobenius T‖ / ‖operatorFrobenius (positivePart T hT)‖ ≤ b/a := by
    apply (div_le_div_iff₀ hp ha).mpr
    have h1 := mul_le_mul_of_nonneg_left hupper ha.le
    have h2 := mul_le_mul_of_nonneg_left hlow hb
    nlinarith
  obtain ⟨S,hS,hn,hsupp⟩ := exists_conditioned_unit_witness T hT
    (t := ε * Real.sqrt d) (mul_nonneg hε.le (Real.sqrt_nonneg _)) hκ
    (by have h := mul_le_mul_of_nonneg_right hκε (Real.sqrt_nonneg d); nlinarith) hp
  refine ⟨S,hS,hn,?_⟩
  have heq : ε * Real.sqrt d * Real.sqrt d = ε*d := by nlinarith
  rw [heq] at hsupp
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hr 1)
    (mul_nonneg hε.le hd'.le)
  linarith

end BMGeometry
