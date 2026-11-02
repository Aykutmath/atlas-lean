import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
# A bounded smooth loss controls empirical L1 under a fractional moment bound

This file is deterministic. It supplies the clipping/uniform-integrability step
needed after bounded smooth loss comparison; the fractional-moment estimate is
an explicit input, not an assumed probabilistic conclusion.
-/

open scoped BigOperators

namespace BMClippedL1Bridge


/-- A bounded, nonnegative, globally smooth loss, vanishing only at zero. -/
noncomputable def smoothLoss (t : ℝ) : ℝ := t ^ 2 / (1 + t ^ 2)

lemma smoothLoss_nonneg (t : ℝ) : 0 ≤ smoothLoss t := by
  unfold smoothLoss
  positivity

lemma smoothLoss_lt_one (t : ℝ) : smoothLoss t < 1 := by
  unfold smoothLoss
  apply (div_lt_one (by positivity)).2
  linarith

lemma smoothLoss_zero : smoothLoss 0 = 0 := by norm_num [smoothLoss]

lemma smoothLoss_contDiff : ContDiff ℝ ⊤ smoothLoss := by
  unfold smoothLoss
  fun_prop (disch := intro x; positivity)

lemma smoothLoss_pos {δ : ℝ} (hδ : 0 < δ) : 0 < smoothLoss δ := by
  unfold smoothLoss
  positivity

/-- A positive loss gap outside any neighborhood of zero. -/
lemma smoothLoss_gap {δ t : ℝ} (hδ : 0 ≤ δ) (ht : δ ≤ |t|) :
    smoothLoss δ ≤ smoothLoss t := by
  have hsq : δ ^ 2 ≤ t ^ 2 := by
    have h := sq_le_sq₀ hδ (abs_nonneg t) |>.2 ht
    simpa only [sq_abs] using h
  unfold smoothLoss
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- Pointwise tail control by any moment strictly above one. -/
lemma tail_le_fractional_moment {r R q : ℝ} (hR : 0 < R)
    (hr : R ≤ r) (hq : 1 < q) :
    r ≤ r ^ q / R ^ (q - 1) := by
  have hrpos : 0 < r := lt_of_lt_of_le hR hr
  have hp : R ^ (q - 1) ≤ r ^ (q - 1) :=
    Real.rpow_le_rpow hR.le hr (by linarith)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hR _)).2
  calc
    r * R ^ (q - 1) ≤ r * r ^ (q - 1) := mul_le_mul_of_nonneg_left hp hrpos.le
    _ = r ^ (q - 1) * r := mul_comm _ _
    _ = r ^ ((q - 1) + 1) := (Real.rpow_add_one hrpos.ne' _).symm
    _ = r ^ q := by congr 1; ring

/-- Generic low/middle/tail split. Only positivity and a loss gap are required. -/
theorem abs_le_clipped_loss_add_tail
    (φ : ℝ → ℝ) {t δ R c q : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 < R) (hc : 0 < c) (hq : 1 < q)
    (hφ : 0 ≤ φ t) (hgap : δ ≤ |t| → c ≤ φ t) :
    |t| ≤ δ + (R / c) * φ t + |t| ^ q / R ^ (q - 1) := by
  have hmiddle : 0 ≤ (R / c) * φ t := mul_nonneg (div_nonneg hR.le hc.le) hφ
  have htail : 0 ≤ |t| ^ q / R ^ (q - 1) := by positivity
  by_cases hlow : |t| ≤ δ
  · linarith
  by_cases hbounded : |t| ≤ R
  · have hgap' := hgap (le_of_lt (lt_of_not_ge hlow))
    have hcap : R ≤ (R / c) * φ t := by
      calc
        R = (R / c) * c := by field_simp
        _ ≤ (R / c) * φ t := mul_le_mul_of_nonneg_left hgap' (div_nonneg hR.le hc.le)
    linarith
  · have ht := tail_le_fractional_moment hR (le_of_lt (lt_of_not_ge hbounded)) hq
    linarith

/-- The explicit rational smooth potential version of the pointwise estimate. -/
theorem abs_le_smoothLoss_add_tail {t δ R q : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hq : 1 < q) :
    |t| ≤ δ + (R / smoothLoss δ) * smoothLoss t + |t| ^ q / R ^ (q - 1) :=
  abs_le_clipped_loss_add_tail smoothLoss hδ.le hR (smoothLoss_pos hδ) hq
    (smoothLoss_nonneg t) (smoothLoss_gap hδ.le)

/-- Finite-sum form, before division by the sample count. -/
theorem sum_abs_le_clipped_loss_add_tail {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (φ : ℝ → ℝ) {δ R c q : ℝ}
    (hδ : 0 ≤ δ) (hR : 0 < R) (hc : 0 < c) (hq : 1 < q)
    (hφ : ∀ i ∈ s, 0 ≤ φ (r i))
    (hgap : ∀ i ∈ s, δ ≤ |r i| → c ≤ φ (r i)) :
    ∑ i ∈ s, |r i| ≤ (s.card : ℝ) * δ +
      (R / c) * (∑ i ∈ s, φ (r i)) + (∑ i ∈ s, |r i| ^ q) / R ^ (q - 1) := by
  calc
    ∑ i ∈ s, |r i| ≤ ∑ i ∈ s, (δ + (R / c) * φ (r i) +
        |r i| ^ q / R ^ (q - 1)) := by
      exact Finset.sum_le_sum fun i hi =>
        abs_le_clipped_loss_add_tail φ hδ hR hc hq (hφ i hi) (hgap i hi)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, Finset.mul_sum, Finset.sum_div]

/-- Empirical mean version under a concrete finite-sum moment bound. -/
theorem empirical_abs_le_smoothLoss_add_moment {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) {δ R q K : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hq : 1 < q)
    (hmoment : (∑ i, |r i| ^ q) ≤ K * n) :
    (∑ i, |r i|) / n ≤ δ + (R / smoothLoss δ) *
      ((∑ i, smoothLoss (r i)) / n) + K / R ^ (q - 1) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum := sum_abs_le_clipped_loss_add_tail Finset.univ r smoothLoss
    hδ.le hR (smoothLoss_pos hδ) hq
    (fun i _ => smoothLoss_nonneg (r i)) (fun i _ => smoothLoss_gap hδ.le)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hm : (∑ i, |r i| ^ q) / R ^ (q - 1) ≤ K * n / R ^ (q - 1) :=
    div_le_div_of_nonneg_right hmoment (Real.rpow_pos_of_pos hR _).le
  apply (div_le_iff₀ hnreal).2
  calc
    ∑ i, |r i| ≤ (n : ℝ) * δ + (R / smoothLoss δ) *
        (∑ i, smoothLoss (r i)) + K * n / R ^ (q - 1) := by linarith
    _ = _ := by
      field_simp [hnreal.ne', (smoothLoss_pos hδ).ne',
        (Real.rpow_pos_of_pos hR (q - 1)).ne']

/-- The exponent q=6/5 used in the BM L1-risk application. -/
theorem empirical_abs_le_smoothLoss_six_fifths {n : ℕ} (hn : 0 < n)
    (r : Fin n → ℝ) {δ R K : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hmoment : (∑ i, |r i| ^ (6 / 5 : ℝ)) ≤ K * n) :
    (∑ i, |r i|) / n ≤ δ + (R / smoothLoss δ) *
      ((∑ i, smoothLoss (r i)) / n) + K / R ^ (1 / 5 : ℝ) := by
  simpa only [show (6 / 5 : ℝ) - 1 = 1 / 5 by norm_num] using
    empirical_abs_le_smoothLoss_add_moment hn r hδ hR
    (show (1 : ℝ) < 6 / 5 by norm_num) hmoment

/-- The first derivative is explicit. -/
lemma smoothLoss_hasDerivAt (t : ℝ) :
    HasDerivAt smoothLoss (2 * t / (1 + t ^ 2) ^ 2) t := by
  convert! ((hasDerivAt_id t).pow 2).div
    ((hasDerivAt_const t 1).add ((hasDerivAt_id t).pow 2))
    (by positivity : (1 : ℝ) + t ^ 2 ≠ 0) using 1
  simp [smoothLoss]
  ring

lemma smoothLoss_deriv (t : ℝ) :
    deriv smoothLoss t = 2 * t / (1 + t ^ 2) ^ 2 :=
  (smoothLoss_hasDerivAt t).deriv

/-- The derivative has a global bound, as required by bounded C1-loss comparison. -/
lemma smoothLoss_abs_deriv_le_one (t : ℝ) : |deriv smoothLoss t| ≤ 1 := by
  have hden : |(1 + t ^ 2) ^ 2| = (1 + t ^ 2) ^ 2 := abs_of_nonneg (sq_nonneg _)
  have htwo : |(2 : ℝ)| = 2 := by norm_num
  rw [smoothLoss_deriv, abs_div, abs_mul, htwo, hden]
  apply (div_le_one (by positivity)).2
  have hsq : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [sq_nonneg (|t| - 1), sq_nonneg (t ^ 2)]

/-- Explicit choice of a tail cap with a strict ε/3 tail budget. -/
lemma six_fifths_tail_cap {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ K / R ^ (1 / 5 : ℝ) < ε / 3 := by
  let B : ℝ := 3 * (K + 1) / ε
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B ^ 5, pow_pos hB _, ?_⟩
  have hroot : (B ^ 5) ^ (1 / 5 : ℝ) = B := by
    rw [← Real.rpow_natCast_mul hB.le]
    norm_num
  rw [hroot]
  apply (div_lt_iff₀ hB).2
  have hbudget : ε / 3 * B = K + 1 := by
    dsimp [B]
    field_simp
  rw [hbudget]
  linarith

/-- Uniform deterministic conversion of arbitrarily small bounded smooth loss
into arbitrarily small empirical L1 risk under a uniform q=6/5 moment bound.
The loss threshold depends only on K and ε, never on n or the residual vector. -/
theorem exists_smoothLoss_threshold {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (n : ℕ), 0 < n → ∀ (r : Fin n → ℝ),
      (∑ i, |r i| ^ (6 / 5 : ℝ)) ≤ K * n →
      (∑ i, smoothLoss (r i)) / n ≤ η →
      (∑ i, |r i|) / n < ε := by
  obtain ⟨R, hR, htail⟩ := six_fifths_tail_cap hK hε
  let δ : ℝ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let η : ℝ := (ε / 3) * smoothLoss δ / R
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (mul_pos (by positivity) (smoothLoss_pos hδ)) hR
  refine ⟨η, hη, ?_⟩
  intro n hn r hmoment hloss
  have hbridge := empirical_abs_le_smoothLoss_six_fifths hn r hδ hR hmoment
  have hmiddle : (R / smoothLoss δ) * ((∑ i, smoothLoss (r i)) / n) ≤ ε / 3 := by
    calc
      _ ≤ (R / smoothLoss δ) * η :=
        mul_le_mul_of_nonneg_left hloss (div_nonneg hR.le (smoothLoss_pos hδ).le)
      _ = ε / 3 := by
        dsimp [η]
        field_simp [(smoothLoss_pos hδ).ne', hR.ne']
  dsimp [δ] at hbridge
  linarith

/-- Feasibility is preserved: arbitrarily small bounded smooth loss over any
constrained candidate class yields arbitrarily small L1 over that same class. -/
theorem exists_small_L1_of_small_smoothLoss {α : Type*} {n : ℕ}
    (hn : 0 < n) (P : α → Prop) (r : α → Fin n → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hmoment : ∀ a, P a → (∑ i, |r a i| ^ (6 / 5 : ℝ)) ≤ K * n)
    (hloss : ∀ η : ℝ, 0 < η → ∃ a, P a ∧ (∑ i, smoothLoss (r a i)) / n ≤ η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a, P a ∧ (∑ i, |r a i|) / n < ε := by
  obtain ⟨η, hη, htransfer⟩ := exists_smoothLoss_threshold hK hε
  obtain ⟨a, ha, hsmall⟩ := hloss η hη
  exact ⟨a, ha, htransfer n hn (r a) (hmoment a ha) hsmall⟩

/-- Coarse but uniform fractional-moment control after shifting by one. -/
lemma abs_sub_one_six_fifths_le (a : ℝ) :
    |a - 1| ^ (6 / 5 : ℝ) ≤ 4 * (|a| ^ (6 / 5 : ℝ) + 1) := by
  have htri : |a - 1| ≤ |a| + 1 := by simpa using abs_sub_le a 0 1
  have htwo : (2 : ℝ) ^ (6 / 5 : ℝ) ≤ 4 := by
    calc
      (2 : ℝ) ^ (6 / 5 : ℝ) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hnonneg : 0 ≤ |a| ^ (6 / 5 : ℝ) := Real.rpow_nonneg (abs_nonneg a) _
  by_cases ha : |a| ≤ 1
  · have hb : |a - 1| ≤ 2 := by linarith
    have hp := Real.rpow_le_rpow (abs_nonneg (a - 1)) hb (show (0 : ℝ) ≤ 6 / 5 by norm_num)
    nlinarith
  · have hb : |a - 1| ≤ 2 * |a| := by linarith
    calc
      |a - 1| ^ (6 / 5 : ℝ) ≤ (2 * |a|) ^ (6 / 5 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg (a - 1)) hb (by norm_num)
      _ = (2 : ℝ) ^ (6 / 5 : ℝ) * |a| ^ (6 / 5 : ℝ) :=
        Real.mul_rpow (by norm_num) (abs_nonneg a)
      _ ≤ 4 * |a| ^ (6 / 5 : ℝ) := mul_le_mul_of_nonneg_right htwo hnonneg
      _ ≤ 4 * (|a| ^ (6 / 5 : ℝ) + 1) := by linarith

/-- Finite-sum version of the shift bound; the moment constant becomes 4(K+1). -/
theorem sum_abs_sub_one_six_fifths_le {n : ℕ} (a : Fin n → ℝ) {K : ℝ}
    (hmoment : (∑ i, |a i| ^ (6 / 5 : ℝ)) ≤ K * n) :
    (∑ i, |a i - 1| ^ (6 / 5 : ℝ)) ≤ (4 * (K + 1)) * n := by
  calc
    (∑ i, |a i - 1| ^ (6 / 5 : ℝ)) ≤ ∑ i, 4 * (|a i| ^ (6 / 5 : ℝ) + 1) :=
      Finset.sum_le_sum fun i _ => abs_sub_one_six_fifths_le (a i)
    _ = 4 * ((∑ i, |a i| ^ (6 / 5 : ℝ)) + n) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ ≤ 4 * (K * n + n) := by linarith
    _ = (4 * (K + 1)) * n := by ring

end BMClippedL1Bridge

#print axioms BMClippedL1Bridge.smoothLoss_contDiff
#print axioms BMClippedL1Bridge.smoothLoss_abs_deriv_le_one
#print axioms BMClippedL1Bridge.abs_le_clipped_loss_add_tail
#print axioms BMClippedL1Bridge.sum_abs_le_clipped_loss_add_tail
#print axioms BMClippedL1Bridge.empirical_abs_le_smoothLoss_six_fifths
#print axioms BMClippedL1Bridge.exists_smoothLoss_threshold
#print axioms BMClippedL1Bridge.exists_small_L1_of_small_smoothLoss

#print axioms BMClippedL1Bridge.abs_sub_one_six_fifths_le
#print axioms BMClippedL1Bridge.sum_abs_sub_one_six_fifths_le
