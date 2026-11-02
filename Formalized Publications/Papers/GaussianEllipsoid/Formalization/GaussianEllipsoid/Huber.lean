/-
Copyright (c) 2026 Aykut Arslan. All rights reserved.
Kernel-checked scalar Huber loss, its nonnegative-branch inverse, and comparison bounds.
Paper Section 4.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

noncomputable section

namespace GaussianEllipsoid

/-- The scalar Huber loss, with the paper's cutoff and factor one half. -/
def huber (t : Real) : Real :=
  if |t| <= 1 then t ^ 2 / 2 else |t| - 1 / 2

/-- The exact quadratic branch, including both cutoff endpoints. -/
theorem huber_of_abs_le_one {t : Real} (h : |t| <= 1) :
    huber t = t ^ 2 / 2 := by
  simp only [huber, ite_eq_left h]

/-- The exact linear branch. -/
theorem huber_of_one_lt_abs {t : Real} (h : 1 < |t|) :
    huber t = |t| - 1 / 2 := by
  simp only [huber, ite_eq_right (not_le.mpr h)]

@[simp] theorem huber_zero : huber 0 = 0 := by norm_num [huber]

@[simp] theorem huber_neg (t : Real) : huber (-t) = huber t := by
  simp only [huber, abs_neg, neg_sq]

@[simp] theorem huber_abs (t : Real) : huber |t| = huber t := by
  simp only [huber, abs_abs, sq_abs]

theorem huber_nonneg (t : Real) : 0 <= huber t := by
  by_cases h : |t| <= 1
  next =>
    rw [huber_of_abs_le_one h]
    positivity
  next =>
    rw [huber_of_one_lt_abs (lt_of_not_ge h)]
    have habs : 1 < |t| := lt_of_not_ge h
    linarith

/-- The objective comparison with the paper's approximate L1 fit. -/
theorem huber_le_abs (t : Real) : huber t <= |t| := by
  by_cases h : |t| <= 1
  next =>
    rw [huber_of_abs_le_one h]
    have hprod := mul_nonneg (abs_nonneg t) (sub_nonneg.mpr h)
    nlinarith [sq_abs t, abs_nonneg t]
  next =>
    rw [huber_of_one_lt_abs (lt_of_not_ge h)]
    linarith

/-- A branch formula convenient for nonnegative radii. -/
theorem huber_of_nonneg_le_one {t : Real} (ht : 0 <= t) (h : t <= 1) :
    huber t = t ^ 2 / 2 := by
  apply huber_of_abs_le_one
  simpa only [abs_of_nonneg ht] using h

/-- A branch formula convenient for nonnegative radii. -/
theorem huber_of_one_lt {t : Real} (h : 1 < t) :
    huber t = t - 1 / 2 := by
  have ht : 0 <= t := by linarith
  rw [huber_of_one_lt_abs (by simpa only [abs_of_nonneg ht] using h)]
  rw [abs_of_nonneg ht]

/-- Strict increase on the nonnegative half-line, needed for the inverse step. -/
theorem huber_strict_mono_nonneg {s t : Real} (hs : 0 <= s) (hst : s < t) :
    huber s < huber t := by
  have ht : 0 <= t := by linarith
  by_cases hs1 : s <= 1
  next =>
    rw [huber_of_nonneg_le_one hs hs1]
    by_cases ht1 : t <= 1
    next =>
      rw [huber_of_nonneg_le_one ht ht1]
      have hprod := mul_pos (sub_pos.mpr hst) (show 0 < t + s by linarith)
      nlinarith
    next =>
      rw [huber_of_one_lt (lt_of_not_ge ht1)]
      have hprod := mul_nonneg (sub_nonneg.mpr hs1) (show 0 <= 1 + s by linarith)
      have ht1' : 1 < t := lt_of_not_ge ht1
      nlinarith
  next =>
    have hs1' : 1 < s := lt_of_not_ge hs1
    have ht1' : 1 < t := by linarith
    rw [huber_of_one_lt hs1', huber_of_one_lt ht1']
    linarith

theorem huber_mono_nonneg {s t : Real} (hs : 0 <= s) (hst : s <= t) :
    huber s <= huber t := by
  rcases lt_or_eq_of_le hst with hlt | heq
  next =>
    exact le_of_lt (huber_strict_mono_nonneg hs hlt)
  next =>
    rw [heq]

theorem huber_mono_abs {a b : Real} (h : |a| <= |b|) :
    huber a <= huber b := by
  calc
    huber a = huber |a| := (huber_abs a).symm
    _ <= huber |b| := huber_mono_nonneg (abs_nonneg a) h
    _ = huber b := huber_abs b

/-- Superadditivity on nonnegative inputs, rather than an assumed inverse rule. -/
theorem huber_superadditive {s t : Real} (hs : 0 <= s) (ht : 0 <= t) :
    huber s + huber t <= huber (s + t) := by
  have hsum : 0 <= s + t := add_nonneg hs ht
  by_cases hs1 : s <= 1
  next =>
    rw [huber_of_nonneg_le_one hs hs1]
    by_cases ht1 : t <= 1
    next =>
      rw [huber_of_nonneg_le_one ht ht1]
      by_cases hsum1 : s + t <= 1
      next =>
        rw [huber_of_nonneg_le_one hsum hsum1]
        nlinarith [mul_nonneg hs ht]
      next =>
        rw [huber_of_one_lt (lt_of_not_ge hsum1)]
        have hprodS := mul_nonneg hs (sub_nonneg.mpr hs1)
        have hprodT := mul_nonneg ht (sub_nonneg.mpr ht1)
        have hsum1' : 1 < s + t := lt_of_not_ge hsum1
        nlinarith
    next =>
      have ht1' : 1 < t := lt_of_not_ge ht1
      have hsum1' : 1 < s + t := by linarith
      rw [huber_of_one_lt ht1', huber_of_one_lt hsum1']
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
  next =>
    have hs1' : 1 < s := lt_of_not_ge hs1
    have hsum1' : 1 < s + t := by linarith
    rw [huber_of_one_lt hs1', huber_of_one_lt hsum1']
    by_cases ht1 : t <= 1
    next =>
      rw [huber_of_nonneg_le_one ht ht1]
      nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
    next =>
      rw [huber_of_one_lt (lt_of_not_ge ht1)]
      linarith

/-- The precise inverse comparison used after the deleted-row objective bound. -/
theorem abs_le_add_of_huber_le {a b e : Real} (he : 0 <= e)
    (h : huber a <= huber b + huber e) : |a| <= |b| + e := by
  by_contra hnot
  have hlt : |b| + e < |a| := lt_of_not_ge hnot
  have hstrict := huber_strict_mono_nonneg
    (add_nonneg (abs_nonneg b) he) hlt
  have hsuper := huber_superadditive (abs_nonneg b) he
  rw [huber_abs a] at hstrict
  rw [huber_abs b] at hsuper
  linarith

/-- The pointwise L1 estimate used with Jensen in the deleted sample. -/
theorem abs_le_sqrt_two_huber_add_two_huber (t : Real) :
    |t| <= Real.sqrt (2 * huber t) + 2 * huber t := by
  by_cases h : |t| <= 1
  next =>
    have heq : 2 * huber t = t ^ 2 := by
      rw [huber_of_abs_le_one h]
      ring
    have hsqrt : Real.sqrt (2 * huber t) = |t| := by
      rw [heq, Real.sqrt_sq_eq_abs]
    rw [hsqrt]
    linarith [huber_nonneg t]
  next =>
    have hgt : 1 < |t| := lt_of_not_ge h
    have hbranch := huber_of_one_lt_abs hgt
    nlinarith [Real.sqrt_nonneg (2 * huber t)]

/-- Pointwise square control on a bounded residual interval. -/
theorem sq_le_two_mul_huber_of_abs_le {t M : Real}
    (hM : 1 <= M) (htM : |t| <= M) : t ^ 2 <= 2 * M * huber t := by
  by_cases h : |t| <= 1
  next =>
    have hnonneg := huber_nonneg t
    have hprod := mul_nonneg (sub_nonneg.mpr hM) hnonneg
    have hbranch := huber_of_abs_le_one h
    nlinarith
  next =>
    have hgt : 1 < |t| := lt_of_not_ge h
    have hbranch := huber_of_one_lt_abs hgt
    have hM0 : 0 <= M := by linarith
    have hprod1 := mul_nonneg (abs_nonneg t) (sub_nonneg.mpr htM)
    have hprod2 := mul_nonneg hM0 (show 0 <= |t| - 1 by linarith)
    rw [hbranch]
    nlinarith [sq_abs t]

/-- The paper's cutoff-square expression, with the weak cutoff convention. -/
def truncatedSquare (t M : Real) : Real := if |t| <= M then t ^ 2 else 0

/-- The complementary tail uses a strict cutoff exactly as in the paper. -/
def tailSquare (t M : Real) : Real := if M < |t| then t ^ 2 else 0

theorem truncatedSquare_nonneg (t M : Real) : 0 <= truncatedSquare t M := by
  unfold truncatedSquare
  split_ifs <;> positivity

theorem tailSquare_nonneg (t M : Real) : 0 <= tailSquare t M := by
  unfold tailSquare
  split_ifs <;> positivity

theorem sq_eq_truncatedSquare_add_tailSquare (t M : Real) :
    t ^ 2 = truncatedSquare t M + tailSquare t M := by
  by_cases h : |t| <= M
  next =>
    simp [truncatedSquare, tailSquare, h, not_lt.mpr h]
  next =>
    simp [truncatedSquare, tailSquare, h, lt_of_not_ge h]

/-- Exact pointwise estimate at manuscript line 663. -/
theorem truncatedSquare_le_two_mul_huber (t : Real) {M : Real} (hM : 1 <= M) :
    truncatedSquare t M <= 2 * M * huber t := by
  by_cases ht : |t| <= M
  next =>
    simp only [truncatedSquare, ite_eq_left ht]
    exact sq_le_two_mul_huber_of_abs_le hM ht
  next =>
    simp only [truncatedSquare, ite_eq_right ht]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (huber_nonneg t)

/-- The exact small-error value used for e_d=b0/d. -/
theorem huber_div_eq_ridge_error {b0 d : Real} (hb0 : 0 <= b0) (hd : 0 < d)
    (hsmall : b0 / d <= 1) : huber (b0 / d) = b0 ^ 2 / (2 * d ^ 2) := by
  rw [huber_of_nonneg_le_one (div_nonneg hb0 hd.le) hsmall]
  field_simp [ne_of_gt hd]

/-- A source-facing residual comparison with e=b0/d and its exact ridge error. -/
theorem abs_le_add_div_of_huber_le {a b b0 d : Real}
    (hb0 : 0 <= b0) (hd : 0 < d) (hsmall : b0 / d <= 1)
    (h : huber a <= huber b + b0 ^ 2 / (2 * d ^ 2)) :
    |a| <= |b| + b0 / d := by
  apply abs_le_add_of_huber_le (div_nonneg hb0 hd.le)
  rw [huber_div_eq_ridge_error hb0 hd hsmall]
  exact h


/-- The inverse of the Huber loss restricted to nonnegative inputs.
The intended domain is nonnegative errors; negative inputs are not used. -/
def huberInv (error : Real) : Real :=
  if error <= 1 / 2 then Real.sqrt (2 * error) else error + 1 / 2

theorem huberInv_nonneg {error : Real} (_herror : 0 <= error) :
    0 <= huberInv error := by
  unfold huberInv
  split_ifs
  next =>
    exact Real.sqrt_nonneg _
  next =>
    linarith

/-- The explicit inverse really returns the error on its intended domain. -/
theorem huber_huberInv {error : Real} (herror : 0 <= error) :
    huber (huberInv error) = error := by
  by_cases hhalf : error <= 1 / 2
  next =>
    have hrad : 0 <= 2 * error := by linarith
    have hroot := Real.sqrt_nonneg (2 * error)
    have hsquare := Real.sq_sqrt hrad
    have hroot1 : Real.sqrt (2 * error) <= 1 := by nlinarith
    simp only [huberInv, ite_eq_left hhalf]
    rw [huber_of_nonneg_le_one hroot hroot1]
    nlinarith
  next =>
    have hlarge : 1 < error + 1 / 2 := by linarith
    simp only [huberInv, ite_eq_right hhalf]
    rw [huber_of_one_lt hlarge]
    ring

/-- The nonnegative inverse retrieves the absolute value of any real input. -/
theorem huberInv_huber (t : Real) : huberInv (huber t) = |t| := by
  by_cases ht : |t| <= 1
  next =>
    have hprod := mul_nonneg (sub_nonneg.mpr ht)
      (show 0 <= 1 + |t| by positivity)
    have hbranch := huber_of_abs_le_one ht
    have hhalf : huber t <= 1 / 2 := by nlinarith [sq_abs t]
    have heq : 2 * huber t = t ^ 2 := by nlinarith
    simp only [huberInv, ite_eq_left hhalf]
    rw [heq, Real.sqrt_sq_eq_abs]
  next =>
    have hgt : 1 < |t| := lt_of_not_ge ht
    have hbranch := huber_of_one_lt_abs hgt
    have hhalf : Not (huber t <= 1 / 2) := by linarith
    simp only [huberInv, ite_eq_right hhalf]
    linarith

/-- The literal inverse formulation of the paper's full-to-deleted comparison. -/
theorem abs_le_add_huberInv_of_huber_le {a b error : Real}
    (herror : 0 <= error) (h : huber a <= huber b + error) :
    |a| <= |b| + huberInv error := by
  apply abs_le_add_of_huber_le (huberInv_nonneg herror)
  rw [huber_huberInv herror]
  exact h

/-- Exact evaluation of e_d=phi_Hub^{-1}(epsilon_d) in the small-error regime. -/
theorem huberInv_ridge_error {b0 d : Real} (hb0 : 0 <= b0) (hd : 0 < d)
    (hsmall : b0 / d <= 1) :
    huberInv (b0 ^ 2 / (2 * d ^ 2)) = b0 / d := by
  rw [(huber_div_eq_ridge_error hb0 hd hsmall).symm, huberInv_huber]
  exact abs_of_nonneg (div_nonneg hb0 hd.le)

/-- The Huber loss is bounded by the `r`-th absolute moment for `1 ≤ r ≤ 2`.
On `|t| ≤ 1` this is `t^2/2 ≤ |t|^2 = |t|^(2:ℝ) ≤ |t|^r` (antitone in the
exponent on `[0,1]`); on `1 < |t|` it is `huber t ≤ |t| = |t|^1 ≤ |t|^r`
(monotone in the exponent on `[1,∞)`). Helper H2. -/
theorem huber_le_rpow {t r : Real} (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    huber t ≤ |t| ^ r := by
  by_cases h : |t| ≤ 1
  · rw [huber_of_abs_le_one h]
    have hcast : ((2 : Nat) : Real) = (2 : Real) := by norm_cast
    have hsq : |t| ^ (2 : Real) = t ^ 2 := by
      rw [← hcast, Real.rpow_natCast]
      exact sq_abs t
    have hmono : |t| ^ (2 : Real) ≤ |t| ^ r :=
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg t) h (by linarith) h2
    rw [← hsq]
    have hnn : (0 : Real) ≤ |t| ^ (2 : Real) :=
      Real.rpow_nonneg (abs_nonneg t) (2 : Real)
    linarith
  · have hgt : 1 < |t| := lt_of_not_ge h
    calc huber t ≤ |t| := huber_le_abs t
      _ = |t| ^ (1 : Real) := (Real.rpow_one _).symm
      _ ≤ |t| ^ r :=
          Real.rpow_le_rpow_of_exponent_le (le_of_lt hgt) h1

end GaussianEllipsoid
