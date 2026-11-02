import BMRationalLossData

/-!
# Dimension-free clipped-loss transfer for every 1 ≤ r < 4/3

The proof only uses the explicit rational loss and a deterministic empirical
4/3-moment bound. In particular, the threshold is independent of the sample size.
-/

noncomputable section
open scoped BigOperators
open BMClippedL1Bridge

namespace BMAllRTransfer

/-- Any moment exponent strictly greater than one admits a uniform tail cap. -/
lemma fractional_tail_cap {q K ε : ℝ} (hq : 1 < q) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ K / R ^ (q - 1) < ε / 3 := by
  let B : ℝ := 3 * (K + 1) / ε
  have hB : 0 < B := by dsimp [B]; positivity
  have hq0 : q - 1 ≠ 0 := by linarith
  refine ⟨B ^ (q - 1)⁻¹, Real.rpow_pos_of_pos hB _, ?_⟩
  have hroot : (B ^ (q - 1)⁻¹) ^ (q - 1) = B := by
    rw [← Real.rpow_mul hB.le, inv_mul_cancel₀ hq0, Real.rpow_one]
  rw [hroot]
  apply (div_lt_iff₀ hB).2
  have hbudget : ε / 3 * B = K + 1 := by
    dsimp [B]
    field_simp
  rw [hbudget]
  linarith

/-- Generic uniform clipping threshold, valid for every q > 1. -/
theorem exists_smoothLoss_threshold {q K ε : ℝ}
    (hq : 1 < q) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (n : ℕ), 0 < n → ∀ (x : Fin n → ℝ),
      (∑ i, |x i| ^ q) ≤ K * n →
      (∑ i, smoothLoss (x i)) / n ≤ η →
      (∑ i, |x i|) / n < ε := by
  obtain ⟨R, hR, htail⟩ := fractional_tail_cap hq hK hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let η : ℝ := (ε / 3) * smoothLoss δ / R
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (mul_pos (by positivity) (smoothLoss_pos hδ)) hR
  refine ⟨η, hη, ?_⟩
  intro n hn x hmoment hloss
  have hbridge := empirical_abs_le_smoothLoss_add_moment hn x hδ hR hq hmoment
  have hmiddle : (R / smoothLoss δ) * ((∑ i, smoothLoss (x i)) / n) ≤ ε / 3 := by
    calc
      _ ≤ (R / smoothLoss δ) * η :=
        mul_le_mul_of_nonneg_left hloss (div_nonneg hR.le (smoothLoss_pos hδ).le)
      _ = ε / 3 := by
        dsimp [η]
        field_simp [(smoothLoss_pos hδ).ne', hR.ne']
  dsimp [δ] at hbridge
  linarith

/-- Raising the residual to r ≥ 1 increases its clipped loss by at most two. -/
lemma smoothLoss_abs_rpow_le {r : ℝ} (hr : 1 ≤ r) (t : ℝ) :
    smoothLoss (|t| ^ r) ≤ 2 * smoothLoss t := by
  by_cases ht : |t| ≤ 1
  · have hpow := Real.rpow_le_self_of_le_one (abs_nonneg t) ht hr
    have hg := smoothLoss_gap (Real.rpow_nonneg (abs_nonneg t) r) hpow
    linarith [smoothLoss_nonneg t]
  · have hg := smoothLoss_gap (show (0 : ℝ) ≤ 1 by norm_num)
      (le_of_lt (lt_of_not_ge ht))
    have hhalf : smoothLoss 1 = (1 / 2 : ℝ) := by norm_num [smoothLoss]
    rw [hhalf] at hg
    linarith [smoothLoss_lt_one (|t| ^ r)]

/-- Uniform deterministic conversion from the literal bounded potential to
empirical r-risk, for the full open range 1 ≤ r < 4/3. -/
theorem exists_potential_threshold {r K ε : ℝ}
    (hr : 1 ≤ r) (hrq : r < 4 / 3) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (n : ℕ), 0 < n → ∀ (y : Fin n → ℝ),
      (∑ i, |y i - 1| ^ (4 / 3 : ℝ)) ≤ K * n →
      (∑ i, BMRationalLossData.potential (y i)) / n ≤ η →
      (∑ i, |y i - 1| ^ r) / n < ε := by
  have hrpos : 0 < r := by linarith
  have hq : 1 < (4 / 3 : ℝ) / r := (lt_div_iff₀ hrpos).2 (by simpa using hrq)
  obtain ⟨η, hη, htransfer⟩ := exists_smoothLoss_threshold hq hK hε
  refine ⟨η / 2, by positivity, ?_⟩
  intro n hn y hm hl
  let x : Fin n → ℝ := fun i => |y i - 1| ^ r
  have hx : ∀ i, 0 ≤ x i := fun i => Real.rpow_nonneg (abs_nonneg _) _
  have hmoment : (∑ i, |x i| ^ ((4 / 3 : ℝ) / r)) ≤ K * n := by
    calc
      _ = ∑ i, |y i - 1| ^ (4 / 3 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_of_nonneg (hx i)]
        dsimp [x]
        rw [← Real.rpow_mul (abs_nonneg _)]
        congr 1
        field_simp
      _ ≤ K * n := hm
  have hsum : (∑ i, smoothLoss (x i)) ≤ 2 * (∑ i, BMRationalLossData.potential (y i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => smoothLoss_abs_rpow_le hr (y i - 1)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hloss : (∑ i, smoothLoss (x i)) / n ≤ η := by
    have hdiv := div_le_div_of_nonneg_right hsum hnR.le
    rw [mul_div_assoc] at hdiv
    linarith
  have hout := htransfer n hn x hmoment hloss
  simpa only [abs_of_nonneg (hx _)] using hout

end BMAllRTransfer

#print axioms BMAllRTransfer.fractional_tail_cap
#print axioms BMAllRTransfer.exists_smoothLoss_threshold
#print axioms BMAllRTransfer.smoothLoss_abs_rpow_le
#print axioms BMAllRTransfer.exists_potential_threshold
