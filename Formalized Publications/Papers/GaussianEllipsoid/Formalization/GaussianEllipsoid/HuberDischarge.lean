/-
Discharge of the Section 4 Huber-residual limit (paper Section 4,
main-proposition-3-1, in the dual-norm form `HuberResiduals`): the
Bandeira-Maillard approximate-fitting limit plus leave-one-out
optimality comparisons drive the centered Huber residuals to zero in
the dual mixed norm, in probability.
Mathematical source: paper.tex, Section 4.
-/
import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.GGlue
import GaussianEllipsoid.Huber
import GaussianEllipsoid.SelectorExists
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Order.Filter.Tendsto

noncomputable section

open scoped Matrix Matrix.Norms.Frobenius ENNReal Topology

namespace GaussianEllipsoid

/-! ### Deleted selectors (interface in `BelowObjects`) -/

/-- The ridge penalty is continuous (standalone version). -/
theorem ridgePenalty_continuous {d : Nat} :
    Continuous fun S : Square d => ridgePenalty d S := by
  have heq : (fun S : Square d => ridgePenalty d S)
      = fun S => ((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ)) * (‖S - 1‖) ^ 2 := by
    funext S
    simp [ridgePenalty, frobeniusNorm]
  rw [heq]
  simp only [pow_two]
  exact continuous_const.mul
    ((continuous_norm.comp (continuous_id.sub continuous_const)).mul
      (continuous_norm.comp (continuous_id.sub continuous_const)))

/-- The deleted objective is continuous. -/
theorem deletedHuberObjective_continuous {d n : Nat} (x : Sample d n)
    (j : Fin n) :
    Continuous fun S : Square d => deletedHuberObjective x j S := by
  have huber_part : Continuous fun S : Square d =>
      (∑ i ∈ Finset.univ.erase j, huber (residual x S i))
        / ((n : ℝ) - 1) := by
    apply Continuous.div_const
    exact continuous_finsetSum _ fun i _ =>
      huber_continuous.comp (residual_continuous x i)
  have heq : (fun S : Square d => deletedHuberObjective x j S)
      = fun S => (∑ i ∈ Finset.univ.erase j, huber (residual x S i))
        / ((n : ℝ) - 1) + ridgePenalty d S := by
    funext S
    rfl
  rw [heq]
  exact huber_part.add ridgePenalty_continuous

/-- Deleted selectors exist: Weierstrass on the compact spectral box. -/
theorem deletedHuberMinimizerExists {d n : Nat} {lo hi : Real}
    (hle : lo ≤ hi) (x : Sample d n) (j : Fin n) :
    ∃ S, IsDeletedMinimizer lo hi x j S := by
  have hcompact := isCompact_spectralBox d lo hi
  have hne := spectralBox_nonempty (d := d) hle
  have hcont : ContinuousOn (fun S => deletedHuberObjective x j S)
      (spectralBox d lo hi) :=
    (deletedHuberObjective_continuous x j).continuousOn
  obtain ⟨S, hSmem, hSmin⟩ := hcompact.exists_isMinOn hne hcont
  exact ⟨S, hSmem, isMinOn_iff.mp hSmin⟩

/-! ### Leave-one-out optimality comparison -/

/-- Comparing full and deleted optimality (via the rescaled
`G_{-j}` functional) bounds the left-out Huber residual. -/
theorem loo_huber_comparison {d n : Nat} {lo hi : Real}
    (x : Sample d n) (j : Fin n) (hn : 1 < n)
    {Sstar Sdel : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (hDel : IsDeletedMinimizer lo hi x j Sdel) :
    huber (residual x Sstar j) + ridgePenalty d Sstar
      ≤ huber (residual x Sdel j) + ridgePenalty d Sdel := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hn1R : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn1ne : (n : ℝ) - 1 ≠ 0 := ne_of_gt hn1R
  have hmemJ : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  -- Full optimality tested at the deleted selector.
  have hOPT1 := hStar.2 Sdel hDel.1
  -- Deleted optimality tested at the full selector.
  have hOPT2 := hDel.2 Sstar hStar.1
  unfold huberObjective empiricalHuber empiricalAverage at hOPT1
  simp only [Fintype.card_fin] at hOPT1
  unfold deletedHuberObjective at hOPT2
  -- Rescale the deleted inequality by `(n-1)/n` (the `G_{-j}` trick).
  have hscale : (0 : ℝ) ≤ ((n : ℝ) - 1) / n :=
    div_nonneg hn1R.le hnR.le
  have hOPT2s := mul_le_mul_of_nonneg_right hOPT2 hscale
  -- Split the full sums into the `j` term plus the erased rest.
  have hsplitStar := Finset.add_sum_erase Finset.univ
    (fun i => huber (residual x Sstar i)) hmemJ
  have hsplitDel := Finset.add_sum_erase Finset.univ
    (fun i => huber (residual x Sdel i)) hmemJ
  rw [← hsplitStar, ← hsplitDel] at hOPT1
  field_simp at hOPT1 hOPT2s
  linarith [hOPT1, hOPT2s]

/-! ### Ridge control and residual transfer (helper H2) -/

/-- Pointwise entry equation for `S - 1`. Holds by `rfl` (defeq through
the pi instances); `Pi.sub_apply` cannot fire through the semireducible
`Matrix` definition, so this bridge is used for rewrites below. -/
theorem huber_sub_entry {d : Nat} (S : Square d) (p q : Fin d) :
    (S - 1) p q = S p q - (1 : Square d) p q := rfl

/-- Uniform ridge-penalty bound on the spectral box: every entry of
`S - 1` is at most `|lo| + |hi| + 1` in absolute value, so the squared
Frobenius norm is at most `d^2` times the squared bound, and the
`d⁻²/(2d)` prefactor leaves `(|lo|+|hi|+1)^2/(2d)`. -/
theorem ridgePenalty_le_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    ridgePenalty d S ≤ (|lo| + |hi| + 1) ^ 2 / (2 * (d : Real)) := by
  set M : Real := |lo| + |hi| + 1 with hMdef
  have h1 : ∀ i j : Fin d, |(1 : Square d) i j| ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq]
      norm_num
    · simp only [Matrix.one_apply_ne hij]
      norm_num
  have hentry : ∀ i j : Fin d, |(S - 1) i j| ≤ M := by
    intro i j
    have hb := spectralBox_entry_bound hS i j
    have h1ij := h1 i j
    have htri : |(S - 1) i j| ≤ |S i j| + |(1 : Square d) i j| := by
      have h := abs_add_le (S i j) (-((1 : Square d) i j))
      rw [abs_neg] at h
      rw [huber_sub_entry S i j, sub_eq_add_neg]
      exact h
    rw [hMdef]
    linarith
  have hsq : ∀ i j : Fin d, ((S - 1) i j) ^ 2 ≤ M ^ 2 := by
    intro i j
    rw [← sq_abs ((S - 1) i j)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hentry i j) 2
  have hF : (frobeniusNorm (S - 1)) ^ 2 ≤ (d : Real) ^ 2 * M ^ 2 := by
    rw [frobeniusNorm_sq]
    calc ∑ i, ∑ j, ((S - 1) i j) ^ 2
        ≤ ∑ _i, ∑ _j, M ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hsq i j
      _ = (d : Real) ^ 2 * M ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
  by_cases hd0 : d = 0
  · subst hd0
    have hF0 : (frobeniusNorm (S - 1)) ^ 2 = 0 := by
      have hnn : (0 : Real) ≤ (frobeniusNorm (S - 1)) ^ 2 := sq_nonneg _
      have hle : (frobeniusNorm (S - 1)) ^ 2 ≤ 0 := by
        have h := hF
        simpa using h
      exact le_antisymm hle hnn
    unfold ridgePenalty
    rw [hF0]
    simp
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hdR : (0 : Real) < (d : Real) := Nat.cast_pos.mpr hpos
    have hd0' : (d : Real) ≠ 0 := ne_of_gt hdR
    have hd2 : (d : Real) ^ 2 ≠ 0 := pow_ne_zero 2 hd0'
    have hcoeff : (0 : Real) ≤ ((d : Real) ^ 2)⁻¹ / (2 * (d : Real)) := by
      apply div_nonneg (inv_nonneg.mpr (sq_nonneg _))
      linarith
    have hcan : ((d : Real) ^ 2)⁻¹ * ((d : Real) ^ 2 * M ^ 2) = M ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ hd2, one_mul]
    unfold ridgePenalty
    calc ((d : Real) ^ 2)⁻¹ / (2 * (d : Real)) * (frobeniusNorm (S - 1)) ^ 2
        ≤ ((d : Real) ^ 2)⁻¹ / (2 * (d : Real)) * ((d : Real) ^ 2 * M ^ 2) :=
          mul_le_mul_of_nonneg_left hF hcoeff
      _ = M ^ 2 / (2 * (d : Real)) := by
          calc ((d : Real) ^ 2)⁻¹ / (2 * (d : Real)) * ((d : Real) ^ 2 * M ^ 2)
              = (((d : Real) ^ 2)⁻¹ * ((d : Real) ^ 2 * M ^ 2)) /
                (2 * (d : Real)) := by ring
            _ = M ^ 2 / (2 * (d : Real)) := by rw [hcan]

/-! ### Leave-one-out residual transfer -/

/-- The ridge penalty is nonnegative. -/
theorem ridgePenalty_nonneg {d : Nat} (S : Square d) :
    0 ≤ ridgePenalty d S := by
  unfold ridgePenalty
  apply mul_nonneg _ (sq_nonneg _)
  apply div_nonneg (inv_nonneg.mpr (sq_nonneg _))
  positivity

/-- The left-out Huber residual is controlled by the deleted residual
plus the ridge-difference error. -/
theorem loo_huber_le {d n : Nat} {lo hi : Real} (x : Sample d n)
    (j : Fin n) (hn : 1 < n) {Sstar Sdel : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (hDel : IsDeletedMinimizer lo hi x j Sdel) :
    huber (residual x Sstar j)
      ≤ huber (residual x Sdel j)
        + (|lo| + |hi| + 1) ^ 2 / (d : ℝ) := by
  have hcomp := loo_huber_comparison x j hn hStar hDel
  have hR1 := ridgePenalty_le_of_mem_box hStar.1
  have hR2 := ridgePenalty_le_of_mem_box hDel.1
  have hn1 := ridgePenalty_nonneg Sstar
  have hn2 := ridgePenalty_nonneg Sdel
  have h2 : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))
      + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))
      = (|lo| + |hi| + 1) ^ 2 / (d : ℝ) := by
    ring_nf
  have hdiff : ridgePenalty d Sdel - ridgePenalty d Sstar
      ≤ (|lo| + |hi| + 1) ^ 2 / (d : ℝ) := by
    linarith [hR1, hR2, hn1, hn2, h2]
  linarith [hcomp, hdiff]

/-- Absolute residual transfer through the Huber inverse. -/
theorem loo_abs_le {d n : Nat} {lo hi : Real} (x : Sample d n)
    (j : Fin n) (hn : 1 < n) {Sstar Sdel : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (hDel : IsDeletedMinimizer lo hi x j Sdel) :
    |residual x Sstar j| ≤ |residual x Sdel j|
      + huberInv ((|lo| + |hi| + 1) ^ 2 / (d : ℝ)) := by
  have h := loo_huber_le x j hn hStar hDel
  have he : (0 : ℝ) ≤ (|lo| + |hi| + 1) ^ 2 / (d : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  exact abs_le_add_huberInv_of_huber_le he h

/-- Full-to-deleted tail-square comparison. -/
theorem loo_tailSquare_le {a b e M : Real}
    (hab : |a| ≤ |b| + e) (hM : 2 * e ≤ M) :
    tailSquare a M ≤ 2 * tailSquare b (M / 2) + 2 * e ^ 2 := by
  unfold tailSquare
  by_cases ha : M < |a|
  · have hb : M / 2 < |b| := by linarith [hab, ha, hM]
    simp only [ite_eq_left ha, ite_eq_left hb]
    have h1 : |a| ^ 2 ≤ (|b| + e) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hab 2
    rw [sq_abs a] at h1
    have h2 : (|b| + e) ^ 2 ≤ 2 * |b| ^ 2 + 2 * e ^ 2 := by
      nlinarith [sq_nonneg (|b| - e)]
    rw [sq_abs b] at h2
    linarith [h1, h2]
  · simp only [ite_eq_right ha]
    have hnn1 : (0 : ℝ) ≤ 2 * (if M / 2 < |b| then b ^ 2 else 0) := by
      by_cases hb : M / 2 < |b|
      · simp only [ite_eq_left hb]
        positivity
      · simp only [ite_eq_right hb]
        simp
    have hnn2 : (0 : ℝ) ≤ 2 * e ^ 2 := by positivity
    linarith [hnn1, hnn2]

/-! ### Midpoint convexity and selector uniqueness -/

/-- Midpoint convexity of Huber on the nonnegative ray. -/
theorem huber_midpoint_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    huber ((a + b) / 2) ≤ (huber a + huber b) / 2 := by
  by_cases ha1 : a ≤ 1 <;> by_cases hb1 : b ≤ 1
    <;> by_cases hm : (a + b) / 2 ≤ 1
  · rw [huber_of_nonneg_le_one (by linarith) hm,
      huber_of_nonneg_le_one ha ha1, huber_of_nonneg_le_one hb hb1]
    nlinarith [sq_nonneg (a - b)]
  · exfalso; linarith
  · rw [huber_of_nonneg_le_one (by linarith) hm,
      huber_of_nonneg_le_one ha ha1,
      huber_of_one_lt (by linarith : (1 : ℝ) < b)]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b),
      mul_nonneg (sub_nonneg.mpr ha1) (show (0 : ℝ) ≤ b - 1 by linarith)]
  · rw [huber_of_one_lt (by linarith : (1 : ℝ) < (a + b) / 2),
      huber_of_nonneg_le_one ha ha1,
      huber_of_one_lt (by linarith : (1 : ℝ) < b)]
    nlinarith [sq_nonneg (a - 1)]
  · rw [huber_of_nonneg_le_one (by linarith) hm,
      huber_of_one_lt (by linarith : (1 : ℝ) < a),
      huber_of_nonneg_le_one hb hb1]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b),
      mul_nonneg (show (0 : ℝ) ≤ a - 1 by linarith)
        (sub_nonneg.mpr hb1)]
  · rw [huber_of_one_lt (by linarith : (1 : ℝ) < (a + b) / 2),
      huber_of_one_lt (by linarith : (1 : ℝ) < a),
      huber_of_nonneg_le_one hb hb1]
    nlinarith [sq_nonneg (b - 1)]
  · exfalso; linarith
  · rw [huber_of_one_lt (by linarith : (1 : ℝ) < (a + b) / 2),
      huber_of_one_lt (by linarith : (1 : ℝ) < a),
      huber_of_one_lt (by linarith : (1 : ℝ) < b)]
    linarith

/-- Midpoint convexity of Huber on the whole line. -/
theorem huber_midpoint {a b : Real} :
    huber ((a + b) / 2) ≤ (huber a + huber b) / 2 := by
  have h1 : |(a + b) / 2| ≤ |(|a| + |b|) / 2| := by
    have hab := abs_add_le a b
    have h2 : |(a + b) / 2| = |a + b| / 2 := by
      rw [abs_div]; norm_num
    have hnn : (0 : ℝ) ≤ (|a| + |b|) / 2 := by positivity
    rw [abs_of_nonneg hnn, h2]; linarith
  calc huber ((a + b) / 2) ≤ huber ((|a| + |b|) / 2) := huber_mono_abs h1
    _ ≤ (huber |a| + huber |b|) / 2 :=
        huber_midpoint_nonneg (abs_nonneg _) (abs_nonneg _)
    _ = (huber a + huber b) / 2 := by rw [huber_abs, huber_abs]

/-- Entrywise parallelogram law for the squared Frobenius norm. -/
theorem frobenius_parallelogram {d : Nat} (X Y : Square d) :
    2 * (frobeniusNorm ((1/2 : ℝ) • (X + Y))) ^ 2
      + 2 * (frobeniusNorm ((1/2 : ℝ) • (X - Y))) ^ 2
      = (frobeniusNorm X) ^ 2 + (frobeniusNorm Y) ^ 2 := by
  have h1 : ∀ i j : Fin d,
      ((1/2 : ℝ) • (X + Y)) i j = (X i j + Y i j) / 2 := by
    intro i j
    have hs : ((1/2 : ℝ) • (X + Y)) i j
        = (1/2 : ℝ) • (X + Y) i j := rfl
    have ha : (X + Y) i j = X i j + Y i j := rfl
    rw [hs, ha, smul_eq_mul]; ring
  have h2 : ∀ i j : Fin d,
      ((1/2 : ℝ) • (X - Y)) i j = (X i j - Y i j) / 2 := by
    intro i j
    have hs : ((1/2 : ℝ) • (X - Y)) i j
        = (1/2 : ℝ) • (X - Y) i j := rfl
    have ha : (X - Y) i j = X i j - Y i j := rfl
    rw [hs, ha, smul_eq_mul]; ring
  have hentry : ∀ i j : Fin d,
      2 * (((1/2 : ℝ) • (X + Y)) i j) ^ 2
        + 2 * (((1/2 : ℝ) • (X - Y)) i j) ^ 2
        = (X i j) ^ 2 + (Y i j) ^ 2 := by
    intro i j
    rw [h1 i j, h2 i j]; ring
  have hsum : ∑ i, ∑ j, (2 * (((1/2 : ℝ) • (X + Y)) i j) ^ 2
      + 2 * (((1/2 : ℝ) • (X - Y)) i j) ^ 2)
      = ∑ i, ∑ j, ((X i j) ^ 2 + (Y i j) ^ 2) :=
    Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hentry i j
  rw [frobeniusNorm_sq, frobeniusNorm_sq, frobeniusNorm_sq,
    frobeniusNorm_sq]
  simp only [Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at hsum
  exact hsum

/-- The ridge penalty is strictly midpoint-convex in positive dimension. -/
theorem ridge_strict_midpoint {d : Nat} (hd : 1 ≤ d)
    {A B : Square d} (hne : A ≠ B) :
    ridgePenalty d ((1/2 : ℝ) • (A + B))
      < (ridgePenalty d A + ridgePenalty d B) / 2 := by
  have hdR : (0 : ℝ) < d := by
    have h01 : (0 : ℝ) < 1 := zero_lt_one
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hc : (0 : ℝ) < ((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ)) := by
    have h1 : (0 : ℝ) < ((d : ℝ) ^ 2)⁻¹ :=
      inv_pos.mpr (by nlinarith [hdR])
    have h2 : (0 : ℝ) < 2 * (d : ℝ) := by linarith
    exact div_pos h1 h2
  have hmid : (1/2 : ℝ) • (A + B) - 1
      = (1/2 : ℝ) • ((A - 1) + (B - 1)) := by
    module
  have hpara := frobenius_parallelogram (A - 1) (B - 1)
  have hne' : (A - 1) - (B - 1) ≠ 0 := by
    intro h0
    apply hne
    have : A - B = 0 := by
      have hAB : A - B = (A - 1) - (B - 1) := by abel
      rw [hAB, h0]
    exact sub_eq_zero.mp this
  have hpos : (0 : ℝ)
      < (frobeniusNorm ((1/2 : ℝ) • ((A - 1) - (B - 1)))) ^ 2 := by
    have hne'' : (1/2 : ℝ) • ((A - 1) - (B - 1)) ≠ 0 :=
      smul_ne_zero (by norm_num) hne'
    have hfn : frobeniusNorm ((1/2 : ℝ) • ((A - 1) - (B - 1))) ≠ 0 :=
      fun h => hne'' ((frobeniusNorm_eq_zero_iff _).mp h)
    exact sq_pos_of_ne_zero hfn
  have hlt : (frobeniusNorm ((1/2 : ℝ) • ((A - 1) + (B - 1)))) ^ 2
      < ((frobeniusNorm (A - 1)) ^ 2
        + (frobeniusNorm (B - 1)) ^ 2) / 2 := by
    linarith [hpara, hpos]
  unfold ridgePenalty
  rw [hmid]
  calc ((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ))
          * (frobeniusNorm ((1/2 : ℝ) • ((A - 1) + (B - 1)))) ^ 2
      < ((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ))
          * (((frobeniusNorm (A - 1)) ^ 2
            + (frobeniusNorm (B - 1)) ^ 2) / 2) :=
        mul_lt_mul_of_pos_left hlt hc
    _ = (((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ)) * (frobeniusNorm (A - 1)) ^ 2
          + ((d : ℝ) ^ 2)⁻¹ / (2 * (d : ℝ))
            * (frobeniusNorm (B - 1)) ^ 2) / 2 := by ring

/-- The spectral box is closed under midpoints. -/
theorem spectralBox_convex_mid {d : Nat} {lo hi : Real}
    {S T : Square d} (hS : S ∈ spectralBox d lo hi)
    (hT : T ∈ spectralBox d lo hi) :
    (1/2 : ℝ) • (S + T) ∈ spectralBox d lo hi := by
  constructor
  · have heq : (1/2 : ℝ) • (S + T) - lo • (1 : Square d)
        = (1/2 : ℝ) • ((S - lo • 1) + (T - lo • 1)) := by
      module
    rw [heq]
    exact (hS.1.add hT.1).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · have heq : hi • (1 : Square d) - (1/2 : ℝ) • (S + T)
        = (1/2 : ℝ) • (((hi • 1) - S) + ((hi • 1) - T)) := by
      module
    rw [heq]
    exact (hS.2.add hT.2).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- Residuals are affine in the matrix: midpoint residuals are midpoint
residuals. -/
theorem residual_mid {d n : Nat} (hd : 1 ≤ d) (x : Sample d n)
    (S T : Square d) (i : Fin n) :
    residual x ((1/2 : ℝ) • (S + T)) i
      = (residual x S i + residual x T i) / 2 := by
  have hsmul : ∀ (c : ℝ) (u v : Vector d),
      dotProduct u (c • v) = c * dotProduct u v := by
    intro c u v
    simp [dotProduct, Pi.smul_apply, smul_eq_mul, mul_left_comm,
      ← Finset.mul_sum]
  have hadd : ∀ (u v w : Vector d),
      dotProduct u (v + w) = dotProduct u v + dotProduct u w := by
    intro u v w
    simp [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hquad : quadratic ((1/2 : ℝ) • (S + T)) (x i)
      = (quadratic S (x i) + quadratic T (x i)) / 2 := by
    unfold quadratic
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, hsmul, hadd]
    ring
  have hdR : (0 : ℝ) < d := by
    have h01 : (0 : ℝ) < 1 := zero_lt_one
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsqrt : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hdR)
  unfold residual
  rw [hquad]
  field_simp
  ring

/-- The full objective is strictly midpoint-convex in positive
dimension. -/
theorem huberObjective_strict_midpoint {d n : Nat} (hd : 1 ≤ d)
    (x : Sample d n) {S T : Square d} (hne : S ≠ T) :
    huberObjective x ((1/2 : ℝ) • (S + T))
      < (huberObjective x S + huberObjective x T) / 2 := by
  have hdiv : ∀ (f : Fin n → ℝ),
      ∑ i, f i / 2 = (∑ i, f i) / 2 := by
    intro f
    calc ∑ i, f i / 2 = ∑ i, f i * (1/2 : ℝ) := by
            refine Finset.sum_congr rfl fun i _ => by ring
      _ = (∑ i, f i) * (1/2 : ℝ) := (Finset.sum_mul _ _ _).symm
      _ = (∑ i, f i) / 2 := by ring
  have hHub : empiricalHuber (residual x ((1/2 : ℝ) • (S + T)))
      ≤ (empiricalHuber (residual x S)
        + empiricalHuber (residual x T)) / 2 := by
    unfold empiricalHuber empiricalAverage
    simp only [Fintype.card_fin]
    have hcoord : ∀ i : Fin n, huber (residual x ((1/2 : ℝ) • (S + T)) i)
        ≤ (huber (residual x S i) + huber (residual x T i)) / 2 := by
      intro i
      rw [residual_mid hd x S T i]
      exact huber_midpoint
    have hle : ∑ i, huber (residual x ((1/2 : ℝ) • (S + T)) i)
        ≤ ∑ i, (huber (residual x S i)
          + huber (residual x T i)) / 2 :=
      Finset.sum_le_sum fun i _ => hcoord i
    have heq : ∑ i, (huber (residual x S i) + huber (residual x T i)) / 2
        = (∑ i, huber (residual x S i)
          + ∑ i, huber (residual x T i)) / 2 := by
      calc ∑ i, (huber (residual x S i) + huber (residual x T i)) / 2
          = ∑ i, (huber (residual x S i) / 2
            + huber (residual x T i) / 2) := by
              refine Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, huber (residual x S i) / 2
            + ∑ i, huber (residual x T i) / 2 :=
              Finset.sum_add_distrib
        _ = (∑ i, huber (residual x S i)) / 2
            + (∑ i, huber (residual x T i)) / 2 := by
              rw [hdiv, hdiv]
        _ = (∑ i, huber (residual x S i)
            + ∑ i, huber (residual x T i)) / 2 := by
              rw [add_div]
    have hle2 : ∑ i, huber (residual x ((1/2 : ℝ) • (S + T)) i)
        ≤ (∑ i, huber (residual x S i)
          + ∑ i, huber (residual x T i)) / 2 := by
      linarith [hle, heq]
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      simp
    · have hnR : (0 : ℝ) < n :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
      have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
      have hrw : ((∑ i, huber (residual x S i)) / (n : ℝ)
          + (∑ i, huber (residual x T i)) / (n : ℝ)) / 2
          = (((∑ i, huber (residual x S i))
            + (∑ i, huber (residual x T i))) / 2) / (n : ℝ) := by
        field_simp
      rw [hrw]
      have hside : (0 : ℝ) ≤ (n : ℝ) := hnR.le
      have hmain : ∑ i, huber (residual x ((1/2 : ℝ) • (S + T)) i)
          ≤ (∑ i, huber (residual x S i)
            + ∑ i, huber (residual x T i)) / 2 := hle2
      have hmono := div_le_div_of_nonneg_right hmain hside
      exact hmono
  have hRidge := ridge_strict_midpoint hd hne
  unfold huberObjective
  linarith [hHub, hRidge]

/-- Huber minimizers in the spectral box are unique. -/
theorem huberMinimizer_unique {d n : Nat} (hd : 1 ≤ d) {lo hi : Real}
    {x : Sample d n} {S T : Square d}
    (hS : IsHuberMinimizer lo hi x S) (hT : IsHuberMinimizer lo hi x T) :
    S = T := by
  by_contra hne
  have hmid := huberObjective_strict_midpoint hd x hne
  have hbox := spectralBox_convex_mid hS.1 hT.1
  have h1 := hS.2 _ hbox
  have h2 := hT.2 _ hbox
  linarith

/-- Aggregated LOO bound: summing the per-index comparison over `j` and
dividing by `n` bounds the full objective at the full selector by the
averaged held-out Huber losses plus averaged deleted ridges. -/
theorem loo_aggregate {d n : Nat} {lo hi : Real} (x : Sample d n)
    (hn : 1 < n) {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j)) :
    huberObjective x Sstar
      ≤ (∑ j, huber (residual x (Sdel j) j)) / (n : ℝ)
        + (∑ j, ridgePenalty d (Sdel j)) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum : (∑ j : Fin n,
        (huber (residual x Sstar j) + ridgePenalty d Sstar))
      ≤ ∑ j : Fin n,
        (huber (residual x (Sdel j) j) + ridgePenalty d (Sdel j)) :=
    Finset.sum_le_sum fun j _ => loo_huber_comparison x j hn hStar (hDel j)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hconst : (∑ _j : Fin n, ridgePenalty d Sstar)
      = (n : ℝ) * ridgePenalty d Sstar := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst] at hsum
  unfold huberObjective empiricalHuber empiricalAverage
  simp only [Fintype.card_fin]
  have hdiv := div_le_div_of_nonneg_right hsum hnR.le
  rw [add_div, add_div] at hdiv
  rw [mul_div_cancel_left₀ _ hnne] at hdiv
  linarith [hdiv]

/-- The averaged deleted-ridge term is uniformly `O(1/d)` on the box. -/
theorem loo_ridge_average {d n : Nat} {lo hi : Real} (x : Sample d n)
    (hn : 1 < n) (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j)) :
    (∑ j, ridgePenalty d (Sdel j)) / (n : ℝ)
      ≤ (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum : (∑ j : Fin n, ridgePenalty d (Sdel j))
      ≤ ∑ _j : Fin n, (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) :=
    Finset.sum_le_sum fun j _ =>
      ridgePenalty_le_of_mem_box (hDel j).1
  have hconst : (∑ _j : Fin n, (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
      = (n : ℝ) * ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hconst] at hsum
  have hdiv := div_le_div_of_nonneg_right hsum hnR.le
  rw [mul_div_cancel_left₀ _ hnne] at hdiv
  exact hdiv

/-- Selector risk bound: the full Huber risk at the selector is at most
the averaged held-out Huber loss plus the uniform `O(1/d)` ridge
remainder. -/
theorem huberSelector_risk_bound {d n : Nat} {lo hi : Real}
    (x : Sample d n) (hn : 1 < n) {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j)) :
    empiricalHuber (residual x Sstar)
      ≤ (∑ j, huber (residual x (Sdel j) j)) / (n : ℝ)
        + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) := by
  have hagg := loo_aggregate x hn hStar Sdel hDel
  have hridge := loo_ridge_average x hn Sdel hDel
  have hnn := ridgePenalty_nonneg (d := d) Sstar
  unfold huberObjective at hagg
  linarith [hagg, hridge, hnn]

/-- Centering is an `ℓ²` contraction: `‖center v‖₂ ≤ ‖v‖₂`. -/
theorem euclidNorm_center_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    euclidNorm (center v) ≤ euclidNorm v := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold euclidNorm center mean
  apply Real.sqrt_le_sqrt
  set S : ℝ := ∑ i, v i with hSdef
  set m : ℝ := S / (n : ℝ) with hmdef
  have hexpand : (∑ i : Fin n, (v i - m) ^ 2)
      = (∑ i : Fin n, (v i) ^ 2) - 2 * m * S + (n : ℝ) * m ^ 2 := by
    have hpt : ∀ i : Fin n, (v i - m) ^ 2
        = (v i) ^ 2 + (-2 * m * v i) + m ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hlin : (∑ i : Fin n, -2 * m * v i) = -2 * m * S := by
      have hpt2 : ∀ i : Fin n, -2 * m * v i = (-2 * m) * v i := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hpt2 i)]
      rw [← Finset.mul_sum, ← hSdef]
    have hconst : (∑ _i : Fin n, m ^ 2) = (n : ℝ) * m ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hlin, hconst]
    ring
  rw [hexpand]
  have hkey : (n : ℝ) * m ^ 2 - 2 * m * S = -(S ^ 2 / (n : ℝ)) := by
    rw [hmdef]
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ S ^ 2 / (n : ℝ) := div_nonneg (sq_nonneg _) hnR.le
  linarith [hkey, hnn]

/-- Centering at most doubles the sup norm: `‖center v‖ ≤ 2‖v‖`. -/
theorem supNorm_center_le {n : Nat} (hn : 0 < n) (v : Vector n) :
    ‖center v‖ ≤ 2 * ‖v‖ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hS : |∑ i, v i| ≤ (n : ℝ) * ‖v‖ := by
    calc |∑ i, v i| ≤ ∑ i, |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖v‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm v i
      _ = (n : ℝ) * ‖v‖ := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmean : |mean v| ≤ ‖v‖ := by
    unfold mean
    rw [abs_div, abs_of_pos hnR]
    rw [div_le_iff₀ hnR]
    linarith [hS]
  rw [pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ‖v‖)]
  intro i
  have htri : |center v i| ≤ |v i| + |mean v| := by
    unfold center
    calc |v i - mean v| = |(v i) + (-(mean v))| := by ring_nf
      _ ≤ |v i| + |-(mean v)| := abs_add_le _ _
      _ = |v i| + |mean v| := by rw [abs_neg]
  have hcoord : |v i| ≤ ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v i
  calc ‖center v i‖ = |center v i| := Real.norm_eq_abs _
    _ ≤ |v i| + |mean v| := htri
    _ ≤ ‖v‖ + ‖v‖ := add_le_add hcoord hmean
    _ = 2 * ‖v‖ := by ring

/-- Frobenius bound on the spectral box. -/
theorem frobeniusNorm_le_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    frobeniusNorm S ≤ (d : Real) * (|lo| + |hi|) := by
  set M : Real := |lo| + |hi| with hMdef
  have hsq : ∀ i j : Fin d, (S i j) ^ 2 ≤ M ^ 2 := by
    intro i j
    rw [← sq_abs (S i j)]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (spectralBox_entry_bound hS i j) 2
  have hF : (frobeniusNorm S) ^ 2 ≤ ((d : Real) * M) ^ 2 := by
    rw [frobeniusNorm_sq]
    calc ∑ i, ∑ j, (S i j) ^ 2
        ≤ ∑ _i, ∑ _j, M ^ 2 :=
          Finset.sum_le_sum fun i _ =>
            Finset.sum_le_sum fun j _ => hsq i j
      _ = ((d : Real) * M) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
  have hnn : (0 : Real) ≤ (d : Real) * M :=
    mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hfin := abs_le_of_sq_le_sq hF hnn
  rw [abs_of_nonneg (frobeniusNorm_nonneg S)] at hfin
  rw [hMdef] at hfin
  exact hfin

/-- Operator-norm bound on the spectral box. -/
theorem matrixOpNorm_le_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    matrixOpNorm S ≤ (d : Real) * (|lo| + |hi|) :=
  (matrixOpNorm_le_frobeniusNorm S).trans
    (frobeniusNorm_le_of_mem_box hS)

/-- Quadratic-form upper bound on the spectral box. -/
theorem quadratic_le_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    {x : Vector d} (hS : S ∈ spectralBox d lo hi) :
    quadratic S x ≤ (d : Real) * (|lo| + |hi|) * (euclidNorm x) ^ 2 := by
  calc quadratic S x ≤ |quadratic S x| := le_abs_self _
    _ ≤ matrixOpNorm S * (euclidNorm x) ^ 2 :=
        quadratic_abs_le_opNorm_mul_sq S x
    _ ≤ (d : Real) * (|lo| + |hi|) * (euclidNorm x) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (matrixOpNorm_le_of_mem_box hS) (sq_nonneg _)

/-- The selector's Huber risk is at most any box witness's `L^r` risk
plus the uniform ridge remainder (`huber ≤ |·|^r` for `1 ≤ r ≤ 2`). -/
theorem selector_huber_le_bmWitness {d n : Nat} {lo hi r : Real}
    (x : Sample d n) (hn : 0 < n) {Sstar Sbm : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (hbm : Sbm ∈ spectralBox d lo hi) (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    empiricalHuber (residual x Sstar)
      ≤ (1 / (n : ℝ)) * (∑ i, |residual x Sbm i| ^ r)
        + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hOPT := hStar.2 Sbm hbm
  unfold huberObjective at hOPT
  have hHub : empiricalHuber (residual x Sbm)
      ≤ (∑ i, |residual x Sbm i| ^ r) / (n : ℝ) := by
    unfold empiricalHuber empiricalAverage
    simp only [Fintype.card_fin]
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun i _ => huber_le_rpow h1 h2) hnR.le
  have hRstar := ridgePenalty_nonneg (d := d) Sstar
  have hRbm := ridgePenalty_le_of_mem_box hbm
  have heq : (1 / (n : ℝ)) * (∑ i, |residual x Sbm i| ^ r)
      = (∑ i, |residual x Sbm i| ^ r) / (n : ℝ) := by
    rw [mul_comm, mul_one_div]
  linarith [hOPT, hHub, hRstar, hRbm, heq]

/-- Below the BM threshold value there is always a box witness. -/
theorem bmMinRisk_witness {d n : Nat} (x : Sample d n) (hn : 0 < n)
    {lo hi r ε : Real} (hle : lo ≤ hi)
    (h : bmMinRisk d n x lo hi r < ε) :
    ∃ Sbm ∈ spectralBox d lo hi,
      (1 / (n : ℝ)) * (∑ i, |residual x Sbm i| ^ r) < ε := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hbdd : BddBelow {t : Real | ∃ S ∈ spectralBox d lo hi,
      t = (1 / (n : ℝ)) * ∑ i, |residual x S i| ^ r} := by
    refine ⟨0, ?_⟩
    intro t ht
    obtain ⟨S, _, rfl⟩ := ht
    exact mul_nonneg (one_div_nonneg.mpr hnR.le)
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hne : {t : Real | ∃ S ∈ spectralBox d lo hi,
      t = (1 / (n : ℝ)) * ∑ i, |residual x S i| ^ r}.Nonempty := by
    obtain ⟨S0, hS0⟩ := spectralBox_nonempty (d := d) hle
    exact ⟨_, S0, hS0, rfl⟩
  unfold bmMinRisk at h
  obtain ⟨t, ⟨Sbm, hSbm, rfl⟩, hlt⟩ := (csInf_lt_iff hbdd hne).mp h
  exact ⟨Sbm, hSbm, hlt⟩

/-- On the good BM event the selector's Huber risk is small. -/
theorem selector_huber_of_bmMinRisk {d n : Nat} (x : Sample d n)
    (hn : 0 < n) {lo hi r ε : Real} (hle : lo ≤ hi) {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar) (h1 : 1 ≤ r) (h2 : r ≤ 2)
    (h : bmMinRisk d n x lo hi r < ε) :
    empiricalHuber (residual x Sstar)
      < ε + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) := by
  obtain ⟨Sbm, hSbm, hlt⟩ := bmMinRisk_witness x hn hle h
  have hle2 := selector_huber_le_bmWitness x hn hStar hSbm h1 h2
  linarith

/-! ### Spectral box eigenstructure -/

/-- Box elements are Hermitian. -/
theorem isHermitian_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) : S.IsHermitian := by
  have h1 := hS.1.isHermitian
  have h2 : Matrix.IsHermitian (lo • (1 : Square d)) :=
    Matrix.isHermitian_one.smul (star_trivial lo)
  have h3 := h1.add h2
  rwa [sub_add_cancel] at h3

/-- Box elements are symmetric. -/
theorem isSymm_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) : S.IsSymm :=
  Matrix.isHermitian_iff_isSymm.mp (isHermitian_of_mem_box hS)

/-- Eigenvector Rayleigh quotient equals the eigenvalue. -/
theorem eigenvector_quadratic_eq {d : Nat} {S : Square d}
    (hS : S.IsHermitian) (j : Fin d) :
    quadratic S ⇑(hS.eigenvectorBasis j) = hS.eigenvalues j := by
  set v : Vector d := ⇑(hS.eigenvectorBasis j) with hv
  have hnorm : ‖hS.eigenvectorBasis j‖ = 1 :=
    hS.eigenvectorBasis.orthonormal.norm_eq_one j
  have hE : euclidNorm v = 1 := by
    rw [euclidNorm_eq_norm_toLp]
    exact hnorm
  have hsq := euclidNorm_sq v
  rw [hE, one_pow] at hsq
  have hdot : v ⬝ᵥ v = 1 := by
    have hde : ∀ i : Fin d, v i * v i = (v i) ^ 2 :=
      fun i => (pow_two _).symm
    calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
      _ = ∑ i, (v i) ^ 2 := Finset.sum_congr rfl fun i _ => hde i
      _ = 1 := hsq.symm
  have hmv := hS.mulVec_eigenvectorBasis j
  calc quadratic S v = v ⬝ᵥ (S *ᵥ v) := rfl
    _ = v ⬝ᵥ ((hS.eigenvalues j) • v) := by rw [hmv]
    _ = (hS.eigenvalues j) • (v ⬝ᵥ v) := dotProduct_smul _ _ _
    _ = hS.eigenvalues j := by rw [hdot, smul_eq_mul, mul_one]

/-- PSD quadratic forms are nonnegative (real form). -/
theorem posSemidef_quadratic_nonneg {d : Nat} {A : Square d}
    (hA : A.PosSemidef) (x : Vector d) : 0 ≤ quadratic A x := by
  have h := hA.re_dotProduct_nonneg x
  have hstar : star x = x := by
    funext i
    exact star_trivial _
  rw [hstar] at h
  simpa [quadratic] using h

/-- Box eigenvalues lie below `hi`. -/
theorem eigenvalues_le_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (j : Fin d) :
    (isHermitian_of_mem_box hS).eigenvalues j ≤ hi := by
  have hH := isHermitian_of_mem_box hS
  set v : Vector d := ⇑(hH.eigenvectorBasis j) with hv
  have hnn := posSemidef_quadratic_nonneg hS.2 v
  have hdot : v ⬝ᵥ v = 1 := by
    have hnorm : ‖hH.eigenvectorBasis j‖ = 1 :=
      hH.eigenvectorBasis.orthonormal.norm_eq_one j
    have hE : euclidNorm v = 1 := by
      rw [euclidNorm_eq_norm_toLp]
      exact hnorm
    have hsq := euclidNorm_sq v
    rw [hE, one_pow] at hsq
    calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
      _ = ∑ i, (v i) ^ 2 :=
          Finset.sum_congr rfl fun i _ => (pow_two _).symm
      _ = 1 := hsq.symm
  have hray := eigenvector_quadratic_eq hH j
  rw [← hv] at hray
  have hexpand : quadratic (hi • (1 : Square d) - S) v
      = hi * (v ⬝ᵥ v) - quadratic S v := by
    have hmv : (hi • (1 : Square d) - S) *ᵥ v
        = (hi • v) - (S *ᵥ v) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    calc quadratic (hi • (1 : Square d) - S) v
        = v ⬝ᵥ ((hi • (1 : Square d) - S) *ᵥ v) := rfl
      _ = v ⬝ᵥ ((hi • v) - (S *ᵥ v)) := by rw [hmv]
      _ = v ⬝ᵥ (hi • v) - v ⬝ᵥ (S *ᵥ v) := dotProduct_sub _ _ _
      _ = hi * (v ⬝ᵥ v) - quadratic S v := by
          simp only [dotProduct_smul, smul_eq_mul, quadratic]
  rw [hexpand, hdot, hray] at hnn
  simp at hnn
  linarith

/-- Eigenvectors from the orthonormal eigenbasis are unit. -/
theorem eigenvectorBasis_dot_self {d : Nat} {S : Square d}
    (hS : S.IsHermitian) (j : Fin d) :
    (⇑(hS.eigenvectorBasis j) : Vector d) ⬝ᵥ
      (⇑(hS.eigenvectorBasis j) : Vector d) = 1 := by
  set v : Vector d := ⇑(hS.eigenvectorBasis j) with hv
  have hnorm : ‖hS.eigenvectorBasis j‖ = 1 :=
    hS.eigenvectorBasis.orthonormal.norm_eq_one j
  have hE : euclidNorm v = 1 := by
    rw [euclidNorm_eq_norm_toLp]
    exact hnorm
  have hsq := euclidNorm_sq v
  rw [hE, one_pow] at hsq
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ = ∑ i, (v i) ^ 2 :=
        Finset.sum_congr rfl fun i _ => (pow_two _).symm
    _ = 1 := hsq.symm

/-- Box eigenvalues lie above `lo`. -/
theorem eigenvalues_ge_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) (j : Fin d) :
    lo ≤ (isHermitian_of_mem_box hS).eigenvalues j := by
  have hH := isHermitian_of_mem_box hS
  set v : Vector d := ⇑(hH.eigenvectorBasis j) with hv
  have hnn := posSemidef_quadratic_nonneg hS.1 v
  have hdot : v ⬝ᵥ v = 1 := by
    have h := eigenvectorBasis_dot_self hH j
    rwa [← hv] at h
  have hray := eigenvector_quadratic_eq hH j
  rw [← hv] at hray
  have hexpand : quadratic (S - lo • (1 : Square d)) v
      = quadratic S v - lo * (v ⬝ᵥ v) := by
    have hmv : (S - lo • (1 : Square d)) *ᵥ v
        = (S *ᵥ v) - (lo • v) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    calc quadratic (S - lo • (1 : Square d)) v
        = v ⬝ᵥ ((S - lo • (1 : Square d)) *ᵥ v) := rfl
      _ = v ⬝ᵥ ((S *ᵥ v) - (lo • v)) := by rw [hmv]
      _ = v ⬝ᵥ (S *ᵥ v) - v ⬝ᵥ (lo • v) := dotProduct_sub _ _ _
      _ = quadratic S v - lo * (v ⬝ᵥ v) := by
          simp only [dotProduct_smul, smul_eq_mul, quadratic]
  rw [hexpand, hdot, hray] at hnn
  simp at hnn
  linarith

/-- Trace interval on the box (entrywise). -/
theorem trace_mem_box_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    lo * (d : Real) ≤ S.trace ∧ S.trace ≤ hi * (d : Real) := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  constructor
  · calc lo * (d : Real) = ∑ _i : Fin d, lo := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ ∑ i, S i i :=
          Finset.sum_le_sum fun i _ => (spectralBox_diag hS).1
  · calc ∑ i, S i i ≤ ∑ _i : Fin d, hi :=
          Finset.sum_le_sum fun i _ => (spectralBox_diag hS).2
      _ = hi * (d : Real) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring

/-- Trace equals the eigenvalue sum on the box. -/
theorem trace_eq_sum_eigenvalues_box {d : Nat} {lo hi : Real} {S : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    S.trace = ∑ j, (isHermitian_of_mem_box hS).eigenvalues j := by
  have hH := isHermitian_of_mem_box hS
  have h := hH.trace_eq_sum_eigenvalues
  simpa using h

/-- Trace against a diagonal matrix. -/
theorem trace_mul_diagonal_eq {d : Nat} (B : Square d) (e : Fin d → Real) :
    (B * Matrix.diagonal e).trace = ∑ i, B i i * e i := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Spectral expansion of `Tr(SE)`: eigenvalue-weighted eigenvector
quadratic forms. -/
theorem trace_box_mul_expand {d : Nat} {lo hi : Real} {S E : Square d}
    (hS : S ∈ spectralBox d lo hi) :
    (S * E).trace = ∑ i, (isHermitian_of_mem_box hS).eigenvalues i *
      quadratic E ⇑((isHermitian_of_mem_box hS).eigenvectorBasis i) := by
  have hH := isHermitian_of_mem_box hS
  have hspec := hH.spectral_theorem
  set U : Square d := ↑hH.eigenvectorUnitary with hUdef
  have hcol : ∀ i l : Fin d, U l i
      = (⇑(hH.eigenvectorBasis i) : Vector d) l :=
    fun i l => hH.eigenvectorUnitary_apply l i
  have hstar : ∀ a b : Fin d, (star U) a b = U b a := by
    intro a b
    rw [Matrix.star_apply]
    exact star_trivial _
  have hstep1 : (S * E).trace
      = (((star U * E) * U) * Matrix.diagonal
        (RCLike.ofReal ∘ hH.eigenvalues)).trace := by
    conv_lhs => rw [hspec, Unitary.conjStarAlgAut_apply]
    simp only [mul_assoc, ← hUdef]
    rw [Matrix.trace_mul_cycle']
    simp only [mul_assoc]
  rw [hstep1, trace_mul_diagonal_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  have hB : (((star U * E) * U)) i i
      = quadratic E ⇑(hH.eigenvectorBasis i) := by
    simp only [Matrix.mul_apply, hstar, hcol, Finset.sum_mul]
    rw [Finset.sum_comm]
    unfold quadratic
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hB]
  have hof : RCLike.ofReal (hH.eigenvalues i) = hH.eigenvalues i := by simp
  rw [hof]
  ring

/-- Box elements are PSD when `lo ≥ 0`. -/
theorem posSemidef_of_mem_box {d : Nat} {lo hi : Real} {S : Square d}
    (hlo : 0 ≤ lo) (hS : S ∈ spectralBox d lo hi) : S.PosSemidef := by
  have h2 : (lo • (1 : Square d)).PosSemidef :=
    Matrix.PosSemidef.one.smul hlo
  have h3 := hS.1.add h2
  rwa [sub_add_cancel] at h3

/-- PSD trace inequality: `|Tr(SE)| ≤ Tr(S)‖E‖_op`. -/
theorem posSemidef_trace_mul_le {d : Nat} {lo hi : Real} {S E : Square d}
    (hS : S ∈ spectralBox d lo hi) (hpsd : S.PosSemidef) :
    |(S * E).trace| ≤ S.trace * matrixOpNorm E := by
  set hH := isHermitian_of_mem_box hS with hhH
  have hnn : ∀ i : Fin d, 0 ≤ hH.eigenvalues i :=
    fun i => hH.posSemidef_iff_eigenvalues_nonneg.mp hpsd i
  have heuclid : ∀ i : Fin d,
      (euclidNorm ⇑(hH.eigenvectorBasis i)) ^ 2 = 1 := by
    intro i
    rw [euclidNorm_sq]
    have h1 := eigenvectorBasis_dot_self hH i
    have h3 : (∑ j, ((⇑(hH.eigenvectorBasis i) : Vector d) j) ^ 2)
        = (⇑(hH.eigenvectorBasis i) : Vector d) ⬝ᵥ
          ⇑(hH.eigenvectorBasis i) :=
      Finset.sum_congr rfl fun j _ => pow_two _
    rw [h3, h1]
  have hq : ∀ i : Fin d,
      |quadratic E ⇑(hH.eigenvectorBasis i)| ≤ matrixOpNorm E := by
    intro i
    have h := quadratic_abs_le_opNorm_mul_sq E ⇑(hH.eigenvectorBasis i)
    rw [heuclid i, mul_one] at h
    exact h
  rw [trace_box_mul_expand hS]
  calc |∑ i, hH.eigenvalues i * quadratic E ⇑(hH.eigenvectorBasis i)|
      ≤ ∑ i, |hH.eigenvalues i * quadratic E ⇑(hH.eigenvectorBasis i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, hH.eigenvalues i * |quadratic E ⇑(hH.eigenvectorBasis i)| :=
        Finset.sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (hnn i)]
    _ ≤ ∑ i, hH.eigenvalues i * matrixOpNorm E :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hq i) (hnn i)
    _ = (∑ i, hH.eigenvalues i) * matrixOpNorm E :=
        (Finset.sum_mul _ _ _).symm
    _ = S.trace * matrixOpNorm E := by
        rw [← trace_eq_sum_eigenvalues_box hS]

/-- Quadratic forms as traces against rank-one matrices. -/
theorem quadratic_eq_trace_vecMulVec {d : Nat} (S : Square d) (x : Vector d) :
    quadratic S x = (S * Matrix.vecMulVec x x).trace := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The deleted sample covariance, omitting observation `j`. -/
def deletedCovariance {d n : Nat} (x : Sample d n) (j : Fin n) : Square d :=
  ((n : ℝ) - 1)⁻¹ • (∑ i ∈ Finset.univ.erase j,
    Matrix.vecMulVec (x i) (x i))

/-- Deleted average residual as a covariance trace. -/
theorem deleted_avg_residual_eq {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) (hd : 0 < d) (S : Square d) :
    (∑ i ∈ Finset.univ.erase j, residual x S i) / ((n : ℝ) - 1)
      = ((S * deletedCovariance x j).trace - (d : ℝ))
        / Real.sqrt (d : ℝ) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hn1ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hsqne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdR)
  have hcard : ((Finset.univ.erase j).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have hsum : ∑ i ∈ Finset.univ.erase j, quadratic S (x i)
      = ((n : ℝ) - 1) * (S * deletedCovariance x j).trace := by
    have h1 : ∀ i ∈ Finset.univ.erase j,
        quadratic S (x i) = (S * Matrix.vecMulVec (x i) (x i)).trace :=
      fun i _ => quadratic_eq_trace_vecMulVec S (x i)
    rw [Finset.sum_congr rfl h1]
    rw [← Matrix.trace_sum]
    have h2 : (∑ i ∈ Finset.univ.erase j,
          S * Matrix.vecMulVec (x i) (x i))
        = ((n : ℝ) - 1) • (S * deletedCovariance x j) := by
      rw [← Finset.mul_sum]
      unfold deletedCovariance
      rw [Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hn1ne, one_smul]
    rw [h2, Matrix.trace_smul, smul_eq_mul]
  have hres : ∀ i ∈ Finset.univ.erase j, residual x S i
      = (quadratic S (x i) - (d : ℝ)) / Real.sqrt (d : ℝ) := by
    intro i _
    rfl
  have hconst : (∑ _i ∈ Finset.univ.erase j, (d : ℝ))
      = ((n : ℝ) - 1) * (d : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hsplit : (∑ i ∈ Finset.univ.erase j,
        (quadratic S (x i) - (d : ℝ)) / Real.sqrt (d : ℝ))
      = ((∑ i ∈ Finset.univ.erase j, quadratic S (x i))
        - ((n : ℝ) - 1) * (d : ℝ)) / Real.sqrt (d : ℝ) := by
    rw [← Finset.sum_div _ _ _, Finset.sum_sub_distrib, hconst]
  rw [Finset.sum_congr rfl hres, hsplit, hsum]
  field_simp

/-- Deleted objective at the deleted selector is controlled by any box
witness's full Huber risk (the paper's `r_d` bound). -/
theorem deleted_obj_le_bmWitness {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) {lo hi : Real} {Sdel Sbm : Square d}
    (hDel : IsDeletedMinimizer lo hi x j Sdel)
    (hbm : Sbm ∈ spectralBox d lo hi) :
    deletedHuberObjective x j Sdel
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * empiricalHuber (residual x Sbm)
        + ridgePenalty d Sbm := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn1ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
  have hOPT := hDel.2 Sbm hbm
  unfold deletedHuberObjective at hOPT ⊢
  have hdrop : (∑ i ∈ Finset.univ.erase j, huber (residual x Sbm i))
      ≤ ∑ i, huber (residual x Sbm i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun i _ _ => huber_nonneg _)
  have hscale : (∑ i ∈ Finset.univ.erase j, huber (residual x Sbm i))
        / ((n : ℝ) - 1)
      ≤ ((n : ℝ) / ((n : ℝ) - 1))
        * empiricalHuber (residual x Sbm) := by
    unfold empiricalHuber empiricalAverage
    simp only [Fintype.card_fin]
    have h1 : (∑ i ∈ Finset.univ.erase j, huber (residual x Sbm i))
          / ((n : ℝ) - 1)
        ≤ (∑ i, huber (residual x Sbm i)) / ((n : ℝ) - 1) :=
      div_le_div_of_nonneg_right hdrop hn1.le
    have heq : (∑ i, huber (residual x Sbm i)) / ((n : ℝ) - 1)
        = ((n : ℝ) / ((n : ℝ) - 1))
          * ((∑ i, huber (residual x Sbm i)) / (n : ℝ)) := by
      field_simp
    linarith [h1, heq]
  linarith [hOPT, hscale]

/-- Deleted average absolute residual from the deleted Huber average
(the paper's `a_d = √(2r_d) + 2r_d` step, via Cauchy-Schwarz). -/
theorem deleted_abs_le_of_huberAvg {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) (S : Square d) {r : Real}
    (hr : (∑ i ∈ Finset.univ.erase j, huber (residual x S i))
      / ((n : ℝ) - 1) ≤ r) :
    (∑ i ∈ Finset.univ.erase j, |residual x S i|) / ((n : ℝ) - 1)
      ≤ Real.sqrt (2 * r) + 2 * r := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hcard : ((Finset.univ.erase j).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  have havg_nn : (0 : ℝ)
      ≤ (∑ i ∈ Finset.univ.erase j, huber (residual x S i))
        / ((n : ℝ) - 1) :=
    div_nonneg
      (Finset.sum_nonneg fun i _ => huber_nonneg _) hn1.le
  have hr_nn : (0 : ℝ) ≤ r := le_trans havg_nn hr
  have hterm : ∀ i ∈ Finset.univ.erase j, |residual x S i|
      ≤ Real.sqrt (2 * huber (residual x S i))
        + 2 * huber (residual x S i) :=
    fun i _ => abs_le_sqrt_two_huber_add_two_huber _
  have hCS : ((∑ i ∈ Finset.univ.erase j,
        Real.sqrt (2 * huber (residual x S i)))) ^ 2
      ≤ ((Finset.univ.erase j).card : ℝ)
        * (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i)) := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ.erase j)
      (f := fun i => Real.sqrt (2 * huber (residual x S i)))
    have hsq : ∀ i ∈ Finset.univ.erase j,
        (Real.sqrt (2 * huber (residual x S i))) ^ 2
          = 2 * huber (residual x S i) :=
      fun i _ => Real.sq_sqrt
        (mul_nonneg zero_le_two (huber_nonneg _))
    rwa [Finset.sum_congr rfl hsq] at h
  have h2r : (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i))
      / ((n : ℝ) - 1) ≤ 2 * r := by
    have hmul : (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i))
        = 2 * (∑ i ∈ Finset.univ.erase j, huber (residual x S i)) := by
      rw [Finset.mul_sum]
    rw [hmul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hr (by norm_num)
  have hsqrt_le : (∑ i ∈ Finset.univ.erase j,
        Real.sqrt (2 * huber (residual x S i))) / ((n : ℝ) - 1)
      ≤ Real.sqrt (2 * r) := by
    have hnn2 : (0 : ℝ) ≤ (∑ i ∈ Finset.univ.erase j,
        Real.sqrt (2 * huber (residual x S i))) / ((n : ℝ) - 1) :=
      div_nonneg
        (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _) hn1.le
    have hsq2 : ((∑ i ∈ Finset.univ.erase j,
        Real.sqrt (2 * huber (residual x S i))) / ((n : ℝ) - 1)) ^ 2
        ≤ (Real.sqrt (2 * r)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * r)]
      have hCS' : ((∑ i ∈ Finset.univ.erase j,
            Real.sqrt (2 * huber (residual x S i)))) ^ 2
          ≤ ((n : ℝ) - 1)
            * (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i)) := by
        rw [← hcard]
        exact hCS
      have hY : (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i))
          ≤ 2 * r * ((n : ℝ) - 1) :=
        (div_le_iff₀ hn1).mp h2r
      have hpos2 : (0 : ℝ) < ((n : ℝ) - 1) ^ 2 := by positivity
      rw [div_le_iff₀ hpos2]
      calc ((∑ i ∈ Finset.univ.erase j,
            Real.sqrt (2 * huber (residual x S i)))) ^ 2
          ≤ ((n : ℝ) - 1)
            * (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i)) := hCS'
        _ ≤ ((n : ℝ) - 1) * (2 * r * ((n : ℝ) - 1)) :=
            mul_le_mul_of_nonneg_left hY hn1.le
        _ = 2 * r * ((n : ℝ) - 1) ^ 2 := by ring
    have hab := abs_le_of_sq_le_sq hsq2 (Real.sqrt_nonneg _)
    rw [abs_of_nonneg hnn2] at hab
    exact hab
  have hmain : (∑ i ∈ Finset.univ.erase j, |residual x S i|)
        / ((n : ℝ) - 1)
      ≤ (∑ i ∈ Finset.univ.erase j,
          Real.sqrt (2 * huber (residual x S i))) / ((n : ℝ) - 1)
        + 2 * r := by
    have hle : (∑ i ∈ Finset.univ.erase j, |residual x S i|)
        ≤ (∑ i ∈ Finset.univ.erase j,
            Real.sqrt (2 * huber (residual x S i)))
          + (∑ i ∈ Finset.univ.erase j, 2 * huber (residual x S i)) := by
      have h := Finset.sum_le_sum (fun i hi => hterm i hi)
      rwa [Finset.sum_add_distrib] at h
    have hdiv := div_le_div_of_nonneg_right hle hn1.le
    rw [add_div] at hdiv
    linarith [hdiv, h2r]
  linarith [hmain, hsqrt_le]

/-- Trace increment from the covariance error. -/
theorem trace_covariance_split {d : Nat} (S C : Square d) :
    (S * C).trace - S.trace = (S * (C - 1)).trace := by
  have e1 : S * (C - 1) = S * C - S := by
    rw [Matrix.mul_sub, Matrix.mul_one]
  rw [e1]
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Matrix.sub_apply]
  rw [Finset.sum_sub_distrib]

/-- Trace localization for deleted selectors (paper Section 4:
`|TrS/d - 1| ≤ λ₊C_d + a_d/√d`). -/
theorem trace_localization {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) (hd : 0 < d) {lo hi : Real} (hlo : 0 ≤ lo)
    {Sdel : Square d} (hSdel : Sdel ∈ spectralBox d lo hi)
    {C a : Real}
    (hC : matrixOpNorm (deletedCovariance x j - 1) ≤ C)
    (ha : |(∑ i ∈ Finset.univ.erase j, residual x Sdel i)
      / ((n : ℝ) - 1)| ≤ a) :
    |Sdel.trace / (d : ℝ) - 1| ≤ hi * C + a / Real.sqrt (d : ℝ) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hsqpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hsqne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsqpos
  have hpsd := posSemidef_of_mem_box hlo hSdel
  have hTrI := trace_mem_box_of_mem_box hSdel
  have hTr_nn : (0 : ℝ) ≤ Sdel.trace :=
    le_trans (by positivity : (0 : ℝ) ≤ lo * (d : ℝ)) hTrI.1
  have hC_nn : (0 : ℝ) ≤ C :=
    le_trans (matrixOpNorm_nonneg _) hC
  have hTrE := posSemidef_trace_mul_le hSdel hpsd
    (E := deletedCovariance x j - 1)
  have hcross : |(Sdel * (deletedCovariance x j - 1)).trace|
      ≤ hi * (d : ℝ) * C := by
    have h1 : |(Sdel * (deletedCovariance x j - 1)).trace|
        ≤ Sdel.trace * C :=
      le_trans hTrE (mul_le_mul_of_nonneg_left hC hTr_nn)
    have h2 : Sdel.trace * C ≤ (hi * (d : ℝ)) * C :=
      mul_le_mul_of_nonneg_right hTrI.2 hC_nn
    linarith [h1, h2]
  have havg : |((Sdel * deletedCovariance x j).trace - (d : ℝ))|
      ≤ a * Real.sqrt (d : ℝ) := by
    have heq := deleted_avg_residual_eq x j hn hd Sdel
    rw [heq] at ha
    rw [abs_div, abs_of_pos hsqpos] at ha
    exact (div_le_iff₀ hsqpos).mp ha
  have hsplit := trace_covariance_split Sdel (deletedCovariance x j)
  have hdecomp : Sdel.trace - (d : ℝ)
      = ((Sdel * deletedCovariance x j).trace - (d : ℝ))
        - (Sdel * (deletedCovariance x j - 1)).trace := by
    linarith [hsplit]
  have hTrD : |Sdel.trace - (d : ℝ)| ≤ hi * (d : ℝ) * C
      + a * Real.sqrt (d : ℝ) := by
    have htri : |Sdel.trace - (d : ℝ)|
        ≤ |((Sdel * deletedCovariance x j).trace - (d : ℝ))|
          + |(Sdel * (deletedCovariance x j - 1)).trace| := by
      rw [hdecomp, sub_eq_add_neg]
      have h := abs_add_le
        ((Sdel * deletedCovariance x j).trace - (d : ℝ))
        (-(Sdel * (deletedCovariance x j - 1)).trace)
      rwa [abs_neg] at h
    linarith [htri, hcross, havg]
  have hgoal : |Sdel.trace / (d : ℝ) - 1|
      = |Sdel.trace - (d : ℝ)| / (d : ℝ) := by
    have he : Sdel.trace / (d : ℝ) - 1
        = (Sdel.trace - (d : ℝ)) / (d : ℝ) := by
      field_simp
    rw [he, abs_div, abs_of_pos hdR]
  rw [hgoal]
  have hdiv : |Sdel.trace - (d : ℝ)| / (d : ℝ)
      ≤ (hi * (d : ℝ) * C + a * Real.sqrt (d : ℝ)) / (d : ℝ) :=
    div_le_div_of_nonneg_right hTrD hdR.le
  have heq2 : (hi * (d : ℝ) * C + a * Real.sqrt (d : ℝ)) / (d : ℝ)
      = hi * C + a / Real.sqrt (d : ℝ) := by
    field_simp
    have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
      Real.mul_self_sqrt hdR.le
    linear_combination a * hsq
  linarith [hdiv, heq2]

/-- The deleted mean-shift `μ_j = (Tr S - d)/√d` (paper Section 4). -/
def deletedMeanShift (d : Nat) (S : Square d) : Real :=
  (S.trace - (d : ℝ)) / Real.sqrt (d : ℝ)

/-- Mean-shift bound from trace localization
(`|μ_j| ≤ √d·λ₊·C + a`). -/
theorem deletedMeanShift_le {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) (hd : 0 < d) {lo hi : Real} (hlo : 0 ≤ lo)
    {Sdel : Square d} (hSdel : Sdel ∈ spectralBox d lo hi)
    {C a : Real}
    (hC : matrixOpNorm (deletedCovariance x j - 1) ≤ C)
    (ha : |(∑ i ∈ Finset.univ.erase j, residual x Sdel i)
      / ((n : ℝ) - 1)| ≤ a) :
    |deletedMeanShift d Sdel| ≤ Real.sqrt (d : ℝ) * hi * C + a := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hsqpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hsqne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsqpos
  have hsq := Real.mul_self_sqrt hdR.le
  have hkey : (d : ℝ) / Real.sqrt (d : ℝ) = Real.sqrt (d : ℝ) := by
    rw [div_eq_iff hsqne]
    exact hsq.symm
  have hloc := trace_localization x j hn hd hlo hSdel hC ha
  have habs : |Sdel.trace / (d : ℝ) - 1|
      = |Sdel.trace - (d : ℝ)| / (d : ℝ) := by
    have he : Sdel.trace / (d : ℝ) - 1
        = (Sdel.trace - (d : ℝ)) / (d : ℝ) := by field_simp
    rw [he, abs_div, abs_of_pos hdR]
  rw [habs] at hloc
  have hTr : |Sdel.trace - (d : ℝ)|
      ≤ (d : ℝ) * (hi * C + a / Real.sqrt (d : ℝ)) := by
    have hle := (div_le_iff₀ hdR).mp hloc
    linarith [hle]
  have hmu : |deletedMeanShift d Sdel|
      = |Sdel.trace - (d : ℝ)| / Real.sqrt (d : ℝ) := by
    unfold deletedMeanShift
    rw [abs_div, abs_of_pos hsqpos]
  rw [hmu]
  calc |Sdel.trace - (d : ℝ)| / Real.sqrt (d : ℝ)
      ≤ ((d : ℝ) * (hi * C + a / Real.sqrt (d : ℝ)))
        / Real.sqrt (d : ℝ) :=
        div_le_div_of_nonneg_right hTr hsqpos.le
    _ = ((d : ℝ) / Real.sqrt (d : ℝ))
        * (hi * C + a / Real.sqrt (d : ℝ)) := by
        rw [div_mul_eq_mul_div]
    _ = Real.sqrt (d : ℝ) * hi * C + a := by
        rw [hkey, mul_add, mul_div_cancel₀ _ hsqne]
        ring

/-- The identity is operator-norm bounded by one. -/
theorem matrixOpNorm_one_le (d : Nat) : matrixOpNorm (1 : Square d) ≤ 1 :=
  matrixOpNorm_le_of_euclid_le zero_le_one
    (fun x => by rw [Matrix.one_mulVec, one_mul])

/-- Deleted covariance error decomposition (paper Section 4:
`Σ̂_{-j} - I = n/(n-1)(Σ̂ - I) + (I - x_jx_j^T)/(n-1)`). -/
theorem deletedCovariance_split {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) :
    deletedCovariance x j - 1
      = ((n : ℝ) / ((n : ℝ) - 1)) • (sampleCovariance x - 1)
        + (1 / ((n : ℝ) - 1))
          • (1 - Matrix.vecMulVec (x j) (x j)) := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hn1ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
  have hsplit : (∑ i ∈ Finset.univ.erase j,
        Matrix.vecMulVec (x i) (x i))
      = (∑ i, Matrix.vecMulVec (x i) (x i))
        - Matrix.vecMulVec (x j) (x j) := by
    have h := Finset.add_sum_erase Finset.univ
      (fun i => Matrix.vecMulVec (x i) (x i)) (Finset.mem_univ j)
    have h2 : (∑ i ∈ Finset.univ.erase j, Matrix.vecMulVec (x i) (x i))
        + Matrix.vecMulVec (x j) (x j)
        = ∑ i, Matrix.vecMulVec (x i) (x i) := by
      rw [add_comm]
      exact h
    exact eq_sub_iff_add_eq.mpr h2
  unfold deletedCovariance sampleCovariance
  rw [hsplit]
  ext k l
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.one_apply]
  field_simp
  ring

/-- Rank-one operator norm as a coordinate sum. -/
theorem matrixOpNorm_vecMulVec_self_le {d : Nat} (x : Vector d) :
    matrixOpNorm (Matrix.vecMulVec x x) ≤ ∑ k, ((x k) ^ 2) := by
  rw [matrixOpNorm_vecMulVec, ← pow_two, euclidNorm_sq]

/-- Deleted covariance error operator-norm bound. -/
theorem deletedCovariance_opNorm_le {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) :
    matrixOpNorm (deletedCovariance x j - 1)
      ≤ ((n : ℝ) / ((n : ℝ) - 1))
          * matrixOpNorm (sampleCovariance x - 1)
        + (1 / ((n : ℝ) - 1)) * (1 + ∑ k, (((x j) k) ^ 2)) := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have ha : (0 : ℝ) < (n : ℝ) / ((n : ℝ) - 1) :=
    div_pos hnR hn1
  have hb : (0 : ℝ) < 1 / ((n : ℝ) - 1) := one_div_pos.mpr hn1
  have hY : matrixOpNorm (1 - Matrix.vecMulVec (x j) (x j))
      ≤ 1 + ∑ k, (((x j) k) ^ 2) :=
    calc matrixOpNorm (1 - Matrix.vecMulVec (x j) (x j))
        = matrixOpNorm (1 + (-Matrix.vecMulVec (x j) (x j))) := by
          rw [sub_eq_add_neg]
      _ ≤ matrixOpNorm (1 : Square d)
          + matrixOpNorm (-Matrix.vecMulVec (x j) (x j)) :=
          matrixOpNorm_add_le _ _
      _ = matrixOpNorm (1 : Square d)
          + matrixOpNorm (Matrix.vecMulVec (x j) (x j)) := by
          rw [matrixOpNorm_neg]
      _ ≤ 1 + ∑ k, (((x j) k) ^ 2) :=
          add_le_add (matrixOpNorm_one_le d)
            (matrixOpNorm_vecMulVec_self_le (x j))
  rw [deletedCovariance_split x j hn]
  calc matrixOpNorm (((n : ℝ) / ((n : ℝ) - 1))
          • (sampleCovariance x - 1)
        + (1 / ((n : ℝ) - 1))
          • (1 - Matrix.vecMulVec (x j) (x j)))
      ≤ matrixOpNorm (((n : ℝ) / ((n : ℝ) - 1))
            • (sampleCovariance x - 1))
        + matrixOpNorm ((1 / ((n : ℝ) - 1))
            • (1 - Matrix.vecMulVec (x j) (x j))) :=
        matrixOpNorm_add_le _ _
    _ = |((n : ℝ) / ((n : ℝ) - 1))|
          * matrixOpNorm (sampleCovariance x - 1)
        + |(1 / ((n : ℝ) - 1))|
          * matrixOpNorm (1 - Matrix.vecMulVec (x j) (x j)) := by
        rw [matrixOpNorm_smul, matrixOpNorm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ ((n : ℝ) / ((n : ℝ) - 1))
          * matrixOpNorm (sampleCovariance x - 1)
        + (1 / ((n : ℝ) - 1)) * (1 + ∑ k, (((x j) k) ^ 2)) := by
        rw [abs_of_pos ha, abs_of_pos hb]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hY hb.le)

/-! ### Uniform deleted-covariance tail (`C_d`) -/

/-- Uniform tail for the deleted covariance error (paper Section 4:
`C_d = max_j ‖Σ̂_{-j} - I‖_op`), combining Davidson–Szarek covariance
concentration with the chi-square row-norm union bound. -/
theorem deletedCovariance_uniform_tail {d n : Nat} (hd : 0 < d) (hn : 1 < n)
    (hdn : (d : ℝ) ≤ (n : ℝ)) {t v : Real} (ht0 : 0 < t) (ht : t < 1 / 2)
    (hv : 0 ≤ v) (hDS : davidsonSzarekCovariance) :
    ((gaussianSampleLaw d n)
      {x | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1))
        * (4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ))
        + (1 / ((n : ℝ) - 1)) * (1 + v)
        < matrixOpNorm (deletedCovariance x j - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2)
        + (n : ℝ)
          * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) := by
  have hn0 : 0 < n := lt_trans (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have ha : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) :=
    (div_pos hnR hn1).le
  have hb : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) :=
    (one_div_pos.mpr hn1).le
  have hDS' : ((gaussianSampleLaw d n)
      {x | 4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
        < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2) :=
    hDS d n hd hn0 hdn
  have hB' : ((gaussianSampleLaw d n)
      (⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2})).toReal
      ≤ (n : ℝ)
        * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) :=
    rowNormSq_union_tail ht0 ht hv
  set u : Real :=
    4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ) with hu_def
  set A : Set (Sample d n) :=
    {x | u < matrixOpNorm (sampleCovariance x - 1)} with hA_def
  set B : Set (Sample d n) :=
    ⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2} with hB_def
  have hsub : {x : Sample d n | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1)) * u
        + (1 / ((n : ℝ) - 1)) * (1 + v)
        < matrixOpNorm (deletedCovariance x j - 1)} ⊆ A ∪ B := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    obtain ⟨j, hj⟩ := hx
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hA, hB⟩ := hcon
    simp only [hA_def, Set.mem_ofPred_eq] at hA
    simp only [hB_def, Set.mem_iUnion, Set.mem_ofPred_eq] at hB
    have hSamp : matrixOpNorm (sampleCovariance x - 1) ≤ u :=
      le_of_not_gt hA
    have hrow : ∀ j : Fin n, ∑ k, (((x j) k) ^ 2) ≤ v :=
      fun j => le_of_not_gt (fun h => hB ⟨j, h⟩)
    have hle := deletedCovariance_opNorm_le x j hn
    have hmono : ((n : ℝ) / ((n : ℝ) - 1))
            * matrixOpNorm (sampleCovariance x - 1)
          + (1 / ((n : ℝ) - 1)) * (1 + ∑ k, (((x j) k) ^ 2))
        ≤ ((n : ℝ) / ((n : ℝ) - 1)) * u
          + (1 / ((n : ℝ) - 1)) * (1 + v) :=
      add_le_add (mul_le_mul_of_nonneg_left hSamp ha)
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (hrow j)) hb)
    exact absurd (le_trans hle hmono) (not_le_of_gt hj)
  have hμ : (gaussianSampleLaw d n)
        {x : Sample d n | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1)) * u
          + (1 / ((n : ℝ) - 1)) * (1 + v)
          < matrixOpNorm (deletedCovariance x j - 1)}
      ≤ (gaussianSampleLaw d n) A + (gaussianSampleLaw d n) B :=
    le_trans (MeasureTheory.measure_mono hsub)
      (MeasureTheory.measure_union_le A B)
  have hAfin : (gaussianSampleLaw d n) A ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  have hBfin : (gaussianSampleLaw d n) B ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  calc ((gaussianSampleLaw d n)
          {x : Sample d n | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1)) * u
            + (1 / ((n : ℝ) - 1)) * (1 + v)
            < matrixOpNorm (deletedCovariance x j - 1)}).toReal
      ≤ ((gaussianSampleLaw d n) A + (gaussianSampleLaw d n) B).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) hμ
    _ = ((gaussianSampleLaw d n) A).toReal
          + ((gaussianSampleLaw d n) B).toReal :=
        ENNReal.toReal_add hAfin hBfin
    _ ≤ 2 * Real.exp (-(d : ℝ) / 2)
          + (n : ℝ)
            * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) :=
        add_le_add hDS' hB'

/-! ### Chaos measurability -/

/-- The quadratic form is jointly continuous in `(S, x)`. -/
theorem continuous_quadratic {d : Nat} :
    Continuous fun p : Square d × Vector d => quadratic p.1 p.2 := by
  unfold quadratic
  exact continuous_snd.dotProduct
    (continuous_fst.matrix_mulVec continuous_snd)

/-- The centered chaos `Z_j` is measurable for measurable selectors. -/
theorem measurable_chaos {d n : Nat} (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel) :
    Measurable fun x : Sample d n =>
      (quadratic (Sdel x) (x j) - (Sdel x).trace)
        / Real.sqrt (d : ℝ) := by
  have hquad : Measurable fun x : Sample d n =>
      quadratic (Sdel x) (x j) :=
    continuous_quadratic.measurable.comp
      (hSdel.prodMk (measurable_pi_apply j))
  have htr : Measurable fun x : Sample d n => (Sdel x).trace := by
    have heq : (fun x : Sample d n => (Sdel x).trace)
        = fun x => ∑ i, Sdel x i i := by
      funext x
      simp [Matrix.trace, Matrix.diag_apply]
    rw [heq]
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hSdel)
  exact (hquad.sub htr).div_const _

/-! ### Full-to-deleted tail transfer -/

/-- Full-to-deleted absolute comparison (paper Section 4:
`|a_j| ≤ |b_j| + e_d`). -/
theorem loo_abs_comparison {d n : Nat} {lo hi : Real}
    (x : Sample d n) (j : Fin n) (hn : 1 < n)
    {Sstar Sdel : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (hDel : IsDeletedMinimizer lo hi x j Sdel) :
    |residual x Sstar j|
      ≤ |residual x Sdel j|
        + huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) := by
  have hcomp := loo_huber_comparison x j hn hStar hDel
  have hRstar := ridgePenalty_nonneg (d := d) Sstar
  have hRdel := ridgePenalty_le_of_mem_box hDel.1
  have hle : huber (residual x Sstar j)
      ≤ huber (residual x Sdel j)
        + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) := by
    linarith [hcomp, hRstar, hRdel]
  have herr : (0 : ℝ) ≤ (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) :=
    div_nonneg (sq_nonneg _) (by positivity)
  exact abs_le_add_huberInv_of_huber_le herr hle

/-- Pointwise tail transfer: if `|a| ≤ |b| + e` and `M ≥ 2e`, then
`a²1_{|a|>M} ≤ 2b²1_{|b|>M/2} + 2e²`. -/
theorem tailSquare_transfer {a b e M : Real}
    (hM : 2 * e ≤ M) (h : |a| ≤ |b| + e) :
    tailSquare a M ≤ 2 * tailSquare b (M / 2) + 2 * e ^ 2 := by
  have hnn : (0 : ℝ) ≤ 2 * tailSquare b (M / 2) + 2 * e ^ 2 :=
    add_nonneg (mul_nonneg (by norm_num) (tailSquare_nonneg _ _))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  by_cases ha : M < |a|
  · have hb : M / 2 < |b| := by linarith [h, ha, hM]
    have h1 : |a| ^ 2 ≤ (|b| + e) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h 2
    have h2 : (|b| + e) ^ 2 ≤ 2 * |b| ^ 2 + 2 * e ^ 2 := by
      nlinarith [sq_nonneg (|b| - e)]
    have hsq : a ^ 2 ≤ 2 * b ^ 2 + 2 * e ^ 2 := by
      rw [← sq_abs a, ← sq_abs b]
      exact le_trans h1 h2
    simp only [tailSquare, ite_eq_left ha, ite_eq_left hb]
    exact hsq
  · simp only [tailSquare, ite_eq_right ha]
    exact hnn

/-- Averaged full-to-deleted tail transfer (paper Section 4). -/
theorem loo_tailSquare_average {d n : Nat} {lo hi : Real}
    (x : Sample d n) (hn : 1 < n) {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j))
    {M : Real}
    (hM : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M) :
    (∑ j, tailSquare (residual x Sstar j) M) / (n : ℝ)
      ≤ 2 * ((∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
          / (n : ℝ))
        + 2 * (huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))) ^ 2 := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  set e : Real := huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
    with he_def
  have hper : ∀ j : Fin n, tailSquare (residual x Sstar j) M
      ≤ 2 * tailSquare (residual x (Sdel j) j) (M / 2) + 2 * e ^ 2 :=
    fun j => tailSquare_transfer hM
      (loo_abs_comparison x j hn hStar (hDel j))
  have hsum : (∑ j, tailSquare (residual x Sstar j) M)
      ≤ 2 * (∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
        + (n : ℝ) * (2 * e ^ 2) := by
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hper j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hle
    have hconst : (∑ _j : Fin n, 2 * e ^ 2)
        = (n : ℝ) * (2 * e ^ 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rwa [hconst] at hle
  calc (∑ j, tailSquare (residual x Sstar j) M) / (n : ℝ)
      ≤ (2 * (∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
          + (n : ℝ) * (2 * e ^ 2)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hsum hnR.le
    _ = 2 * ((∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
          / (n : ℝ)) + 2 * e ^ 2 := by
        rw [add_div, mul_div_assoc, mul_div_cancel_left₀ _ hnne]

/-! ### Gaussian cubic-exponential integral (FTC) -/

/-- `t²e^{-ct²} → 0`. -/
theorem tendsto_sq_mul_exp_neg_sq_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => t ^ 2 * Real.exp (-c * t ^ 2))
      Filter.atTop (nhds 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hinner : Filter.Tendsto (fun t : ℝ => c * t ^ 2)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc
      (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hcne : c ≠ 0 := ne_of_gt hc
  have hcomp := hbase.comp hinner
  have hscale : Filter.Tendsto
      (fun t : ℝ => c⁻¹ * (((fun x : ℝ => x ^ 1 * Real.exp (-x)) ∘
        (fun t : ℝ => c * t ^ 2)) t))
      Filter.atTop (nhds (c⁻¹ * 0)) :=
    tendsto_const_nhds.mul hcomp
  rw [mul_zero] at hscale
  refine hscale.congr' ?_
  filter_upwards with t
  simp only [Function.comp_apply, pow_one]
  rw [neg_mul]
  field_simp

/-- `e^{-ct²} → 0`. -/
theorem tendsto_exp_neg_sq_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-c * t ^ 2))
      Filter.atTop (nhds 0) := by
  have h0 := Real.tendsto_exp_neg_atTop_nhds_zero
  have hinner : Filter.Tendsto (fun t : ℝ => c * t ^ 2)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc
      (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hcomp := h0.comp hinner
  refine hcomp.congr' ?_
  filter_upwards with t
  simp only [Function.comp_apply]
  rw [neg_mul]

/-- Derivative of the Gaussian cubic antiderivative. -/
theorem hasDerivAt_gaussCubic {c : ℝ} (hc : 0 < c) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -((t ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
      * Real.exp (-c * t ^ 2)))
      (x ^ 3 * Real.exp (-c * x ^ 2)) x := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h2c : (2 : ℝ) * c ≠ 0 := mul_ne_zero (by norm_num) hcne
  have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hcne
  have h2c2 : (2 : ℝ) * c ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hc2
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    have h := hasDerivAt_pow 2 x
    simpa using h
  have hP : HasDerivAt (fun t : ℝ => t ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
      ((2 * x) / (2 * c) + 0) x :=
    (hsq.div_const (2 * c)).add (hasDerivAt_const _ _)
  have hinner : HasDerivAt (fun t : ℝ => -c * t ^ 2)
      ((-c) * (2 * x)) x :=
    hsq.const_mul (-c)
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-c * t ^ 2))
      (Real.exp (-c * x ^ 2) * ((-c) * (2 * x))) x :=
    hinner.exp
  have h := hP.mul hE |>.neg
  have hval : -(((2 * x) / (2 * c) + 0) * Real.exp (-c * x ^ 2)
      + (x ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
        * (Real.exp (-c * x ^ 2) * ((-c) * (2 * x))))
      = x ^ 3 * Real.exp (-c * x ^ 2) := by
    field_simp
    ring
  rw [hval] at h
  exact h

/-- The Gaussian cubic antiderivative vanishes at infinity. -/
theorem tendsto_gaussCubicAnti_atTop {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => -((t ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
      * Real.exp (-c * t ^ 2))) Filter.atTop (nhds 0) := by
  have h1 := tendsto_sq_mul_exp_neg_sq_atTop hc
  have h2 := tendsto_exp_neg_sq_atTop hc
  have e : (fun t : ℝ => -((t ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
        * Real.exp (-c * t ^ 2)))
      = fun t => -((2 * c)⁻¹ * (t ^ 2 * Real.exp (-c * t ^ 2))
        + (2 * c ^ 2)⁻¹ * Real.exp (-c * t ^ 2)) := by
    funext t
    simp only [div_eq_mul_inv, one_mul]
    ring
  rw [e]
  have h3 : Filter.Tendsto (fun t : ℝ => (2 * c)⁻¹
        * (t ^ 2 * Real.exp (-c * t ^ 2))
        + (2 * c ^ 2)⁻¹ * Real.exp (-c * t ^ 2))
      Filter.atTop (nhds 0) := by
    have hmul1 : Filter.Tendsto
        (fun t : ℝ => (2 * c)⁻¹ * (t ^ 2 * Real.exp (-c * t ^ 2)))
        Filter.atTop (nhds ((2 * c)⁻¹ * 0)) :=
      tendsto_const_nhds.mul h1
    have hmul2 : Filter.Tendsto
        (fun t : ℝ => (2 * c ^ 2)⁻¹ * Real.exp (-c * t ^ 2))
        Filter.atTop (nhds ((2 * c ^ 2)⁻¹ * 0)) :=
      tendsto_const_nhds.mul h2
    have h := hmul1.add hmul2
    simpa using h
  have h4 := h3.neg
  simpa using h4

/-- Integrability of the Gaussian cubic on `Ioi 0`. -/
theorem integrableOn_Ioi_pow3_gauss {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ 3 * Real.exp (-c * t ^ 2)) (Set.Ioi 0) := by
  set F : ℝ → ℝ := fun t => -((t ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
    * Real.exp (-c * t ^ 2)) with hFdef
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt F (x ^ 3 * Real.exp (-c * x ^ 2)) x :=
    fun x _ => hasDerivAt_gaussCubic hc x
  have hderivIoi : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt F (x ^ 3 * Real.exp (-c * x ^ 2)) x :=
    fun x hx => hderiv x (le_of_lt (Set.mem_Ioi.mp hx))
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ),
      0 ≤ x ^ 3 * Real.exp (-c * x ^ 2) :=
    fun x hx => mul_nonneg
      (pow_nonneg (Set.mem_Ioi.mp hx).le 3) (Real.exp_nonneg _)
  have hcont : ContinuousWithinAt F (Set.Ici 0) 0 :=
    (hderiv 0 (Set.mem_Ici.mpr le_rfl)).continuousAt.continuousWithinAt
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) :=
    tendsto_gaussCubicAnti_atTop hc
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg
    hcont hderivIoi hpos hlim

/-- The Gaussian cubic moment `∫₀^∞ t³e^{-ct²} = 1/(2c²)`. -/
theorem integral_Ioi_pow3_gauss {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi 0, t ^ 3 * Real.exp (-c * t ^ 2)
      = 1 / (2 * c ^ 2) := by
  set F : ℝ → ℝ := fun t => -((t ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
    * Real.exp (-c * t ^ 2)) with hFdef
  have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt F (x ^ 3 * Real.exp (-c * x ^ 2)) x :=
    fun x _ => hasDerivAt_gaussCubic hc x
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ 3 * Real.exp (-c * t ^ 2)) (Set.Ioi 0) :=
    integrableOn_Ioi_pow3_gauss hc
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) :=
    tendsto_gaussCubicAnti_atTop hc
  have hval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint hlim
  have hF0 : F 0 = -(1 / (2 * c ^ 2)) := by
    rw [hFdef]
    show -((0 ^ 2 / (2 * c) + 1 / (2 * c ^ 2))
      * Real.exp (-c * 0 ^ 2)) = _
    norm_num [Real.exp_zero]
  refine hval.trans ?_
  rw [hF0]
  ring

/-! ### Linear-exponent tail integral (isolated helper result) -/

/- The two theorems below plus their three private helpers were proved
by an isolated helper agent in `/tmp/h2/H2Tail.lean` (mathlib-only
imports, independent exit-0 compile) and integrated here verbatim
(modulo namespace qualification). -/
/-- `t ^ n * exp (-β * t) → 0`: rescale to `(β * t) ^ n * exp (-(β * t))`. -/
private theorem pow_mul_exp_tendsto (β : ℝ) (hβ : 0 < β) (n : ℕ) :
    Filter.Tendsto (fun t : ℝ => t ^ n * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hβt : Filter.Tendsto (fun t : ℝ => β * t) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hβ Filter.tendsto_id
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hβt
  have hbn : β ^ n ≠ 0 := pow_ne_zero n hβ0
  have h2 := h.const_mul (β ^ n)⁻¹
  rw [mul_zero] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply]
  rw [mul_pow, show -(β * t) = -β * t by ring]
  field_simp

/-- The antiderivative `F(t) = -(P t) * exp (-β * t)` has derivative `t ^ 3 * exp (-β * t)`. -/
private theorem antideriv_hasDerivAt (β : ℝ) (hβ : 0 < β) (x : ℝ) :
    HasDerivAt (fun t : ℝ => -(t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
      * Real.exp (-β * t)) (x ^ 3 * Real.exp (-β * x)) x := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have e1 : HasDerivAt (fun t : ℝ => t ^ 3 / β) (3 * x ^ 2 / β) x := by
    have h := (hasDerivAt_pow 3 x).div_const β
    have hv : (3 : ℝ) * x ^ 2 / β = ((3 : ℕ) : ℝ) * x ^ (3 - 1) / β := by norm_num
    rw [hv]
    exact h
  have e2 : HasDerivAt (fun t : ℝ => 3 * t ^ 2 / β ^ 2) (6 * x / β ^ 2) x := by
    have h := ((hasDerivAt_pow 2 x).const_mul 3).div_const (β ^ 2)
    have hv : (6 : ℝ) * x / β ^ 2
        = 3 * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) / β ^ 2 := by
      norm_num [pow_one]
      ring
    rw [hv]
    exact h
  have e3 : HasDerivAt (fun t : ℝ => 6 * t / β ^ 3) (6 / β ^ 3) x := by
    have h := (HasDerivAt.const_mul 6 (hasDerivAt_id' x)).div_const (β ^ 3)
    have hv : (6 : ℝ) / β ^ 3 = 6 * 1 / β ^ 3 := by ring
    rw [hv]
    exact h
  have e4 : HasDerivAt (fun _ : ℝ => 6 / β ^ 4) 0 x := hasDerivAt_const x (6 / β ^ 4)
  have hP : HasDerivAt (fun t : ℝ => t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
      (((3 * x ^ 2 / β + 6 * x / β ^ 2) + 6 / β ^ 3) + 0) x :=
    ((e1.add e2).add e3).add e4
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-β * t)) (Real.exp (-β * x) * -β) x := by
    have h := HasDerivAt.exp (HasDerivAt.const_mul (-β) (hasDerivAt_id' x))
    have hv : Real.exp (-β * x) * -β = Real.exp (-β * x) * (-β * 1) := by ring
    rw [hv]
    exact h
  have hF := hP.neg.mul hE
  have hv : x ^ 3 * Real.exp (-β * x)
      = (-(((3 * x ^ 2 / β + 6 * x / β ^ 2) + 6 / β ^ 3) + 0)) * Real.exp (-β * x)
        + (-(((x ^ 3 / β + 3 * x ^ 2 / β ^ 2) + 6 * x / β ^ 3) + 6 / β ^ 4))
          * (Real.exp (-β * x) * -β) := by
    field_simp
    ring
  rw [hv]
  exact hF

/-- The antiderivative tends to 0 at infinity. -/
private theorem antideriv_tendsto (β : ℝ) (hβ : 0 < β) :
    Filter.Tendsto (fun t : ℝ => -(t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
      * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
  have h0 : Filter.Tendsto (fun t : ℝ => (t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
      * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
    have s1 : Filter.Tendsto (fun t : ℝ => t ^ 3 / β * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
      have h := (pow_mul_exp_tendsto β hβ 3).div_const β
      rw [zero_div] at h
      refine h.congr (fun t => ?_)
      ring
    have s2 : Filter.Tendsto (fun t : ℝ => 3 * t ^ 2 / β ^ 2 * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
      have h := ((pow_mul_exp_tendsto β hβ 2).const_mul 3).div_const (β ^ 2)
      rw [mul_zero, zero_div] at h
      refine h.congr (fun t => ?_)
      ring
    have s3 : Filter.Tendsto (fun t : ℝ => 6 * t / β ^ 3 * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
      have h := ((pow_mul_exp_tendsto β hβ 1).const_mul 6).div_const (β ^ 3)
      rw [mul_zero, zero_div] at h
      refine h.congr (fun t => ?_)
      ring
    have s4 : Filter.Tendsto (fun t : ℝ => 6 / β ^ 4 * Real.exp (-β * t)) Filter.atTop (𝓝 0) := by
      have h := (pow_mul_exp_tendsto β hβ 0).const_mul (6 / β ^ 4)
      rw [mul_zero] at h
      refine h.congr (fun t => ?_)
      simp only [pow_zero, one_mul]
    have h := ((s1.add s2).add s3).add s4
    simp only [add_zero] at h
    refine h.congr (fun t => ?_)
    ring
  have h := h0.neg
  rw [neg_zero] at h
  refine h.congr (fun t => ?_)
  ring

theorem integrableOn_Ioi_pow3_exp_neg (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 < β) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ 3 * Real.exp (-β * t)) (Set.Ioi A) := by
  have hderiv : ∀ x ∈ Set.Ici A, HasDerivAt (fun t : ℝ =>
      -(t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
        * Real.exp (-β * t)) (x ^ 3 * Real.exp (-β * x)) x :=
    fun x _ => antideriv_hasDerivAt β hβ x
  have hnonneg : ∀ x ∈ Set.Ioi A, 0 ≤ x ^ 3 * Real.exp (-β * x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans hA (le_of_lt hx)
    exact mul_nonneg (pow_nonneg hx0 3) (Real.exp_pos _).le
  have htend : Filter.Tendsto (fun t : ℝ =>
      -(t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
        * Real.exp (-β * t)) Filter.atTop (𝓝 0) :=
    antideriv_tendsto β hβ
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg htend

theorem integral_Ioi_pow3_exp_neg_le (A β : ℝ) (hA : 0 ≤ A) (hβ : 0 < β) :
    ∫ t in Set.Ioi A, t ^ 3 * Real.exp (-β * t)
      ≤ Real.exp (-β * A)
        * (A ^ 3 / β + 3 * A ^ 2 / β ^ 2 + 6 * A / β ^ 3 + 6 / β ^ 4) := by
  have hderiv : ∀ x ∈ Set.Ici A, HasDerivAt (fun t : ℝ =>
      -(t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
        * Real.exp (-β * t)) (x ^ 3 * Real.exp (-β * x)) x :=
    fun x _ => antideriv_hasDerivAt β hβ x
  have hnonneg : ∀ x ∈ Set.Ioi A, 0 ≤ x ^ 3 * Real.exp (-β * x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans hA (le_of_lt hx)
    exact mul_nonneg (pow_nonneg hx0 3) (Real.exp_pos _).le
  have htend : Filter.Tendsto (fun t : ℝ =>
      -(t ^ 3 / β + 3 * t ^ 2 / β ^ 2 + 6 * t / β ^ 3 + 6 / β ^ 4)
        * Real.exp (-β * t)) Filter.atTop (𝓝 0) :=
    antideriv_tendsto β hβ
  have heq : ∫ t in Set.Ioi A, t ^ 3 * Real.exp (-β * t)
      = 0 - (-(A ^ 3 / β + 3 * A ^ 2 / β ^ 2 + 6 * A / β ^ 3 + 6 / β ^ 4)
        * Real.exp (-β * A)) :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnonneg htend
  rw [heq]
  have hEq : 0 - (-(A ^ 3 / β + 3 * A ^ 2 / β ^ 2 + 6 * A / β ^ 3 + 6 / β ^ 4)
        * Real.exp (-β * A))
      = Real.exp (-β * A)
        * (A ^ 3 / β + 3 * A ^ 2 / β ^ 2 + 6 * A / β ^ 3 + 6 / β ^ 4) := by
    ring
  exact le_of_eq hEq

/-! ### Hanson–Wright fourth moment (layer cake) -/

/-- The centered chaos `Z_j` for a deleted selector function. -/
def chaosZ {d n : Nat} (Sdel : Sample d n → Square d) (j : Fin n)
    (x : Sample d n) : Real :=
  (quadratic (Sdel x) (x j) - (Sdel x).trace) / Real.sqrt (d : ℝ)

/-- Measurability of the chaos, in `chaosZ` form. -/
theorem measurable_chaosZ {d n : Nat} (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel) :
    Measurable (chaosZ Sdel j) :=
  measurable_chaos j Sdel hSdel

/-- Fourth moment of the chaos from Hanson–Wright tails, via layer cake.
Uniform in `d ≥ 1`, `n`, `j`. -/
theorem hansonWright_fourthMoment {d n : Nat} (hd : 1 ≤ d) (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel)
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ Sdel j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) :
    ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4) ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4) := by
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hsqpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hβ : (0 : ℝ) < cHW * Real.sqrt (d : ℝ) := mul_pos hcHW hsqpos
  have hZmeas : Measurable (chaosZ Sdel j) :=
    measurable_chaosZ j Sdel hSdel
  have f_nn : 0 ≤ᵐ[gaussianSampleLaw d n]
      (fun x => |chaosZ Sdel j x|) :=
    Filter.Eventually.of_forall fun x => abs_nonneg _
  have f_mble : AEMeasurable
      (fun x => |chaosZ Sdel j x|) (gaussianSampleLaw d n) :=
    hZmeas.norm.aemeasurable
  have hLC := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul
    (gaussianSampleLaw d n) f_nn f_mble (show (0 : ℝ) < 4 by norm_num)
  have e41 : ((4 : ℝ) - 1) = 3 := by norm_num
  have hLC3 := hLC
  rw [e41] at hLC3
  have h4 : ∀ y : ℝ, |y| ^ (4 : ℝ) = y ^ 4 := fun y => by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by simp, Real.rpow_natCast,
      show (4 : ℕ) = 2 * 2 by norm_num]
    simp only [pow_mul]
    rw [sq_abs]
  have hfun : (fun x : Sample d n =>
      ENNReal.ofReal ((chaosZ Sdel j x) ^ 4))
      = fun x => ENNReal.ofReal (|chaosZ Sdel j x| ^ (4 : ℝ)) := by
    funext x
    rw [h4]
  have ht3 : ∀ t : ℝ, t ^ (3 : ℝ) = t ^ 3 := fun t => by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by simp, Real.rpow_natCast]
  set G : ℝ → ℝ := fun t => 2 * (t ^ 3 * Real.exp (-cHW * t ^ 2))
    with hGdef
  set L : ℝ → ℝ := fun t =>
      2 * (t ^ 3 * Real.exp (-(cHW * Real.sqrt (d : ℝ)) * t))
    with hLdef
  have hexp_split : ∀ t : ℝ,
      2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ)))
        ≤ 2 * Real.exp (-cHW * t ^ 2)
          + 2 * Real.exp (-cHW * t * Real.sqrt (d : ℝ)) := by
    intro t
    rcases le_total (t ^ 2) (t * Real.sqrt (d : ℝ)) with h | h
    · rw [min_eq_left h]
      have hnn : (0 : ℝ)
          ≤ 2 * Real.exp (-cHW * t * Real.sqrt (d : ℝ)) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      linarith
    · rw [min_eq_right h, ← mul_assoc]
      have hnn : (0 : ℝ) ≤ 2 * Real.exp (-cHW * t ^ 2) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      linarith
  have hbound : ∀ t ∈ Set.Ioi (0 : ℝ),
      (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
        * ENNReal.ofReal (t ^ (3 : ℝ))
      ≤ ENNReal.ofReal (G t + L t) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := (Set.mem_Ioi.mp ht).le
    have hfin : (gaussianSampleLaw d n)
        {a | t < |chaosZ Sdel j a|} ≠ ∞ :=
      (MeasureTheory.measure_lt_top _ _).ne
    have hμ : (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
        ≤ ENNReal.ofReal (2 * Real.exp (-cHW * t ^ 2)
          + 2 * Real.exp (-cHW * t * Real.sqrt (d : ℝ))) :=
      calc (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
          = ENNReal.ofReal (((gaussianSampleLaw d n)
              {a | t < |chaosZ Sdel j a|}).toReal) :=
            (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal
            (2 * Real.exp (-cHW * min (t ^ 2)
              (t * Real.sqrt (d : ℝ)))) :=
            ENNReal.ofReal_le_ofReal (hHW t ht0)
        _ ≤ ENNReal.ofReal (2 * Real.exp (-cHW * t ^ 2)
            + 2 * Real.exp (-cHW * t * Real.sqrt (d : ℝ))) :=
            ENNReal.ofReal_le_ofReal (hexp_split t)
    have hnn : (0 : ℝ) ≤ 2 * Real.exp (-cHW * t ^ 2)
        + 2 * Real.exp (-cHW * t * Real.sqrt (d : ℝ)) :=
      add_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
        (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    calc (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
            * ENNReal.ofReal (t ^ (3 : ℝ))
        ≤ ENNReal.ofReal (2 * Real.exp (-cHW * t ^ 2)
            + 2 * Real.exp (-cHW * t * Real.sqrt (d : ℝ)))
          * ENNReal.ofReal (t ^ (3 : ℝ)) :=
          mul_le_mul_left hμ _
      _ = ENNReal.ofReal (G t + L t) := by
          rw [ht3 t, ← ENNReal.ofReal_mul hnn]
          congr 1
          simp only [hGdef, hLdef]
          rw [show (-(cHW * Real.sqrt (d : ℝ))) * t
            = -cHW * t * Real.sqrt (d : ℝ) from by ring]
          ring
  have hae : ∀ᵐ t ∂(MeasureTheory.Measure.restrict
        MeasureTheory.volume (Set.Ioi 0)),
        (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
          * ENNReal.ofReal (t ^ (3 : ℝ))
        ≤ ENNReal.ofReal (G t + L t) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => hbound t ht)
  have hmono : (∫⁻ t in Set.Ioi 0,
        (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
          * ENNReal.ofReal (t ^ (3 : ℝ)))
        ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (G t + L t) :=
    MeasureTheory.lintegral_mono_ae hae
  have hGcont : Continuous G := by
    simp only [hGdef]
    exact continuous_const.mul ((continuous_pow 3).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))))
  have hLcont : Continuous L := by
    simp only [hLdef]
    exact continuous_const.mul ((continuous_pow 3).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  have hGae : AEMeasurable (fun t => ENNReal.ofReal (G t))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    (ENNReal.continuous_ofReal.comp hGcont).measurable.aemeasurable
  have hLae : AEMeasurable (fun t => ENNReal.ofReal (L t))
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    (ENNReal.continuous_ofReal.comp hLcont).measurable.aemeasurable
  have hGnn_mem : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ G t := by
    intro t ht
    simp only [hGdef]
    exact mul_nonneg (by norm_num) (mul_nonneg
      (pow_nonneg (Set.mem_Ioi.mp ht).le 3) (Real.exp_nonneg _))
  have hLnn_mem : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ L t := by
    intro t ht
    simp only [hLdef]
    exact mul_nonneg (by norm_num) (mul_nonneg
      (pow_nonneg (Set.mem_Ioi.mp ht).le 3) (Real.exp_nonneg _))
  have hGnn : 0 ≤ᵐ[MeasureTheory.Measure.restrict
      MeasureTheory.volume (Set.Ioi 0)] G :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => hGnn_mem t ht)
  have hLnn : 0 ≤ᵐ[MeasureTheory.Measure.restrict
      MeasureTheory.volume (Set.Ioi 0)] L :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun t ht => hLnn_mem t ht)
  have hGint : MeasureTheory.Integrable G
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    MeasureTheory.Integrable.const_mul
      (integrableOn_Ioi_pow3_gauss hcHW) 2
  have hLint : MeasureTheory.Integrable L
      (MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)) :=
    MeasureTheory.Integrable.const_mul
      (integrableOn_Ioi_pow3_exp_neg 0 _ (le_refl 0) hβ) 2
  have hβ4 : (cHW * Real.sqrt (d : ℝ)) ^ 4
      = cHW ^ 4 * (d : ℝ) ^ 2 := by
    rw [mul_pow]
    have hsq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
      Real.sq_sqrt hdR.le
    have h4 : Real.sqrt (d : ℝ) ^ 4 = (d : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsq]
    rw [h4]
  have hLint0 := integral_Ioi_pow3_exp_neg_le 0
    (cHW * Real.sqrt (d : ℝ)) (le_refl 0) hβ
  have hRHS : Real.exp (-(cHW * Real.sqrt (d : ℝ)) * 0)
        * ((0 : ℝ) ^ 3 / (cHW * Real.sqrt (d : ℝ))
          + 3 * (0 : ℝ) ^ 2 / (cHW * Real.sqrt (d : ℝ)) ^ 2
          + 6 * (0 : ℝ) / (cHW * Real.sqrt (d : ℝ)) ^ 3
          + 6 / (cHW * Real.sqrt (d : ℝ)) ^ 4)
      = 6 / (cHW ^ 4 * (d : ℝ) ^ 2) := by
    rw [hβ4]
    norm_num [Real.exp_zero]
  rw [hRHS] at hLint0
  have hvalG : ∫ t in Set.Ioi 0, G t = 1 / cHW ^ 2 := by
    have h := integral_Ioi_pow3_gauss hcHW
    have hcm : ∫ t in Set.Ioi 0, 2 * (t ^ 3 * Real.exp (-cHW * t ^ 2))
        = 2 * ∫ t in Set.Ioi 0, t ^ 3 * Real.exp (-cHW * t ^ 2) :=
      MeasureTheory.integral_const_mul 2 _
    have hc2ne : (cHW : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hcHW)
    have h2c2 : (2 : ℝ) * cHW ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) hc2ne
    simp only [hGdef]
    rw [hcm, h]
    field_simp
  have hvalL : ∫ t in Set.Ioi 0, L t ≤ 12 / (cHW ^ 4 * (d : ℝ) ^ 2) := by
    have hcm : ∫ t in Set.Ioi 0,
          2 * (t ^ 3 * Real.exp (-(cHW * Real.sqrt (d : ℝ)) * t))
        = 2 * ∫ t in Set.Ioi 0,
          t ^ 3 * Real.exp (-(cHW * Real.sqrt (d : ℝ)) * t) :=
      MeasureTheory.integral_const_mul 2 _
    simp only [hLdef]
    rw [hcm]
    have hle := mul_le_mul_of_nonneg_left hLint0
      (show (0 : ℝ) ≤ 2 by norm_num)
    have heq : (2 : ℝ) * (6 / (cHW ^ 4 * (d : ℝ) ^ 2))
        = 12 / (cHW ^ 4 * (d : ℝ) ^ 2) := by ring
    rw [heq] at hle
    exact hle
  have hsplit : (∫⁻ t in Set.Ioi 0, ENNReal.ofReal (G t + L t))
      = ENNReal.ofReal (∫ t in Set.Ioi 0, G t)
        + ENNReal.ofReal (∫ t in Set.Ioi 0, L t) := by
    have hcongr : (fun t : ℝ => ENNReal.ofReal (G t + L t))
        =ᵐ[MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)]
        (fun t => ENNReal.ofReal (G t) + ENNReal.ofReal (L t)) :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun t ht =>
          ENNReal.ofReal_add (hGnn_mem t ht) (hLnn_mem t ht))
    rw [MeasureTheory.lintegral_congr_ae hcongr,
      MeasureTheory.lintegral_add_left' hGae _]
    congr 1
    · exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        hGint hGnn).symm
    · exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        hLint hLnn).symm
  have hdRpos : (0 : ℝ) < d :=
    Nat.cast_pos.mpr (lt_of_lt_of_le zero_lt_one hd)
  have hd2 : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by
    have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ zero_le_one h1d 2
  have hd2pos : (0 : ℝ) < (d : ℝ) ^ 2 := pow_pos hdRpos 2
  have hfrac_gen : ∀ K : ℝ, 0 ≤ K →
      K / (cHW ^ 4 * (d : ℝ) ^ 2) ≤ K / cHW ^ 4 := by
    intro K hK
    have hK4 : (0 : ℝ) ≤ K / cHW ^ 4 :=
      div_nonneg hK (pow_nonneg hcHW.le 4)
    rw [← div_div, div_le_iff₀ hd2pos]
    have h := mul_le_mul_of_nonneg_left hd2 hK4
    simpa using h
  have hreal : 4 * (1 / cHW ^ 2 + 12 / (cHW ^ 4 * (d : ℝ) ^ 2))
      ≤ 4 / cHW ^ 2 + 48 / cHW ^ 4 := by
    have h48 := hfrac_gen 48 (by norm_num)
    have e : 4 * (1 / cHW ^ 2 + 12 / (cHW ^ 4 * (d : ℝ) ^ 2))
        = 4 / cHW ^ 2 + 4 * (12 / (cHW ^ 4 * (d : ℝ) ^ 2)) := by
      ring
    have e2 : 4 * (12 / (cHW ^ 4 * (d : ℝ) ^ 2))
        = 48 / (cHW ^ 4 * (d : ℝ) ^ 2) := by ring
    rw [e, e2]
    exact add_le_add le_rfl h48
  calc ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4)
          ∂(gaussianSampleLaw d n)
      = ENNReal.ofReal 4 * ∫⁻ t in Set.Ioi 0,
        (gaussianSampleLaw d n) {a | t < |chaosZ Sdel j a|}
          * ENNReal.ofReal (t ^ (3 : ℝ)) := by
        rw [hfun]
        exact hLC3
    _ ≤ ENNReal.ofReal 4 * ∫⁻ t in Set.Ioi 0,
        ENNReal.ofReal (G t + L t) :=
        mul_le_mul_right hmono _
    _ = ENNReal.ofReal 4 * (ENNReal.ofReal (∫ t in Set.Ioi 0, G t)
        + ENNReal.ofReal (∫ t in Set.Ioi 0, L t)) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4) := by
        rw [hvalG]
        have hLle : ENNReal.ofReal (∫ t in Set.Ioi 0, L t)
            ≤ ENNReal.ofReal (12 / (cHW ^ 4 * (d : ℝ) ^ 2)) :=
          ENNReal.ofReal_le_ofReal hvalL
        have hnn1 : (0 : ℝ) ≤ 1 / cHW ^ 2 :=
          div_nonneg zero_le_one (pow_nonneg hcHW.le 2)
        have hnn2 : (0 : ℝ) ≤ 12 / (cHW ^ 4 * (d : ℝ) ^ 2) :=
          div_nonneg (by norm_num)
            (mul_nonneg (pow_nonneg hcHW.le 4)
              (pow_nonneg (Nat.cast_nonneg _) 2))
        calc ENNReal.ofReal 4 * (ENNReal.ofReal (1 / cHW ^ 2)
                + ENNReal.ofReal (∫ t in Set.Ioi 0, L t))
            ≤ ENNReal.ofReal 4 * (ENNReal.ofReal (1 / cHW ^ 2)
              + ENNReal.ofReal (12 / (cHW ^ 4 * (d : ℝ) ^ 2))) :=
              mul_le_mul_right (add_le_add le_rfl hLle) _
          _ = ENNReal.ofReal
              (4 * (1 / cHW ^ 2 + 12 / (cHW ^ 4 * (d : ℝ) ^ 2))) := by
              rw [← ENNReal.ofReal_add hnn1 hnn2,
                ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          _ ≤ ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4) :=
              ENNReal.ofReal_le_ofReal hreal

/-! ### Empirical UI: pointwise bounds -/

/-- Pointwise chaos tail bound: on `|μ| ≤ K`, with `T = L - K`,
`tailSquare (Z+μ) L ≤ 2·tailSquare Z T + 2K²·1_{|Z|>T}`. -/
theorem tailSquare_chaos_le {Z μ K L T : Real}
    (hμ : |μ| ≤ K) (hT : T = L - K) :
    tailSquare (Z + μ) L
      ≤ 2 * tailSquare Z T
        + 2 * K ^ 2 * (if T < |Z| then (1 : ℝ) else 0) := by
  have hnn : (0 : ℝ) ≤ 2 * tailSquare Z T
      + 2 * K ^ 2 * (if T < |Z| then (1 : ℝ) else 0) :=
    add_nonneg (mul_nonneg (by norm_num) (tailSquare_nonneg _ _))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K))
        (by split_ifs <;> norm_num))
  by_cases hb : L < |Z + μ|
  · have hab := abs_add_le Z μ
    have hZ : T < |Z| := by linarith [hb, hμ, hT, hab]
    have hm1 : (0 : ℝ) ≤ K - μ := by
      have h2 := (abs_le.mp hμ).2
      linarith
    have hm2 : (0 : ℝ) ≤ K + μ := by
      have h1 := (abs_le.mp hμ).1
      linarith
    simp only [tailSquare, ite_eq_left hb, ite_eq_left hZ]
    nlinarith [sq_nonneg (Z - μ), mul_nonneg hm1 hm2]
  · simp only [tailSquare, ite_eq_right hb]
    exact hnn

/-- Chi-square-style domination of the chaos tail by the fourth moment. -/
theorem chaos_tailSquare_le_fourthDiv {Z T : Real} (hT : 0 < T) :
    tailSquare Z T ≤ Z ^ 4 / T ^ 2 := by
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hZ4 : (0 : ℝ) ≤ Z ^ 4 := by positivity
  by_cases hZT : T < |Z|
  · have h1 : T ^ 2 < Z ^ 2 := by
      have h2 : T ^ 2 < |Z| ^ 2 := by
        have hm1 : (0 : ℝ) < |Z| - T := by linarith
        have hm2 : (0 : ℝ) < |Z| + T := by linarith [abs_nonneg Z]
        nlinarith [mul_pos hm1 hm2]
      rwa [sq_abs] at h2
    simp only [tailSquare, ite_eq_left hZT]
    rw [le_div_iff₀ hT2]
    nlinarith [mul_nonneg (sq_nonneg Z)
      (show (0 : ℝ) ≤ Z ^ 2 - T ^ 2 by linarith [h1])]
  · simp only [tailSquare, ite_eq_right hZT]
    exact div_nonneg hZ4 (le_of_lt hT2)

/-- Indicator domination by the fourth moment. -/
theorem chaos_ind_le_fourthDiv {Z T : Real} (hT : 0 < T) :
    (if T < |Z| then (1 : ℝ) else 0) ≤ Z ^ 4 / T ^ 4 := by
  have hT4 : (0 : ℝ) < T ^ 4 := by positivity
  have hZ4 : (0 : ℝ) ≤ Z ^ 4 := by positivity
  by_cases hZT : T < |Z|
  · have hTle : T ≤ |Z| := le_of_lt hZT
    have h1 : T ^ 4 ≤ |Z| ^ 4 := pow_le_pow_left₀ hT.le hTle 4
    have h2 : |Z| ^ (4 : ℕ) = Z ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num]
      simp only [pow_mul]
      rw [sq_abs]
    rw [h2] at h1
    simp only [ite_eq_left hZT]
    rw [le_div_iff₀ hT4, one_mul]
    exact h1
  · simp only [ite_eq_right hZT]
    exact div_nonneg hZ4 (le_of_lt hT4)

/-! ### Empirical UI: averaged bounds -/

/-- Measurability of an absolute-value composition. -/
theorem measurable_abs_comp {d n : Nat} {f : Sample d n → Real}
    (hf : Measurable f) : Measurable fun x => |f x| := by
  have hnorm := hf.norm
  have heq : (fun x => |f x|) = (fun x => ‖f x‖) := by
    funext x
    exact (Real.norm_eq_abs _).symm
  rwa [heq]

/-- Measurability of a `tailSquare` composition. -/
theorem measurable_tailSquare_comp {d n : Nat} {f : Sample d n → Real}
    (hf : Measurable f) (M : Real) :
    Measurable fun x => tailSquare (f x) M := by
  have hset : MeasurableSet {x | M < |f x|} :=
    measurableSet_lt measurable_const (measurable_abs_comp hf)
  unfold tailSquare
  exact Measurable.ite hset (hf.pow_const 2) measurable_const

/-- Measurability of a tail indicator composition. -/
theorem measurable_tailInd {d n : Nat} {f : Sample d n → Real}
    (hf : Measurable f) (T : Real) :
    Measurable fun x => (if T < |f x| then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_lt measurable_const
    (measurable_abs_comp hf)) measurable_const measurable_const

/-- Expected chaos tail from the fourth moment. -/
theorem lintegral_tailSquare_le_fourth {d n : Nat} (hd : 1 ≤ d) (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel)
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ Sdel j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {T : Real} (hT : 0 < T) :
    ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T)
        ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2) := by
  have hZ : Measurable (chaosZ Sdel j) := measurable_chaosZ j Sdel hSdel
  have h4 := hansonWright_fourthMoment hd j Sdel hSdel hcHW hHW
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hc2 : (0 : ℝ) < cHW ^ 2 := by positivity
  have hc4 : (0 : ℝ) < cHW ^ 4 := by positivity
  have hdivnn : (0 : ℝ) ≤ 1 / T ^ 2 := div_nonneg zero_le_one hT2.le
  have hdom : ∀ x : Sample d n,
      ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T)
        ≤ ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 2) := fun x =>
    ENNReal.ofReal_le_ofReal (chaos_tailSquare_le_fourthDiv hT)
  have hmono : ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T)
        ∂(gaussianSampleLaw d n)
      ≤ ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 2)
        ∂(gaussianSampleLaw d n) :=
    MeasureTheory.lintegral_mono hdom
  have hcongr : (fun x : Sample d n =>
        ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 2))
      = fun x => ENNReal.ofReal (1 / T ^ 2)
        * ENNReal.ofReal ((chaosZ Sdel j x) ^ 4) := by
    funext x
    rw [show (chaosZ Sdel j x) ^ 4 / T ^ 2
      = (1 / T ^ 2) * (chaosZ Sdel j x) ^ 4 by
        rw [div_eq_mul_inv, one_div, mul_comm]]
    exact ENNReal.ofReal_mul hdivnn
  have hZ4meas : Measurable fun x : Sample d n =>
      ENNReal.ofReal ((chaosZ Sdel j x) ^ 4) :=
    ENNReal.continuous_ofReal.measurable.comp (hZ.pow_const 4)
  have hfac : ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 2)
        ∂(gaussianSampleLaw d n)
      = ENNReal.ofReal (1 / T ^ 2)
        * ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4)
          ∂(gaussianSampleLaw d n) := by
    rw [hcongr]
    exact MeasureTheory.lintegral_const_mul _ hZ4meas
  have hle : ENNReal.ofReal (1 / T ^ 2)
        * ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4)
          ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (1 / T ^ 2)
        * ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4) :=
    mul_le_mul_right h4 _
  have hre : ENNReal.ofReal (1 / T ^ 2)
        * ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4)
      = ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2) := by
    rw [← ENNReal.ofReal_mul hdivnn]
    congr 1
    conv_rhs => rw [div_eq_mul_inv]
    rw [one_div]
    exact mul_comm _ _
  exact le_trans hmono (le_trans (le_of_eq hfac) (le_trans hle (le_of_eq hre)))

/-- Expected chaos tail indicator from the fourth moment. -/
theorem lintegral_chaosInd_le_fourth {d n : Nat} (hd : 1 ≤ d) (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel)
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ Sdel j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {T : Real} (hT : 0 < T) :
    ∫⁻ x, ENNReal.ofReal (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)
        ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) := by
  have hZ : Measurable (chaosZ Sdel j) := measurable_chaosZ j Sdel hSdel
  have h4 := hansonWright_fourthMoment hd j Sdel hSdel hcHW hHW
  have hT4 : (0 : ℝ) < T ^ 4 := by positivity
  have hdivnn : (0 : ℝ) ≤ 1 / T ^ 4 := div_nonneg zero_le_one hT4.le
  have hdom : ∀ x : Sample d n,
      ENNReal.ofReal (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)
        ≤ ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 4) := fun x =>
    ENNReal.ofReal_le_ofReal (chaos_ind_le_fourthDiv hT)
  have hmono : ∫⁻ x, ENNReal.ofReal
          (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)
        ∂(gaussianSampleLaw d n)
      ≤ ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 4)
        ∂(gaussianSampleLaw d n) :=
    MeasureTheory.lintegral_mono hdom
  have hcongr : (fun x : Sample d n =>
        ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 4))
      = fun x => ENNReal.ofReal (1 / T ^ 4)
        * ENNReal.ofReal ((chaosZ Sdel j x) ^ 4) := by
    funext x
    rw [show (chaosZ Sdel j x) ^ 4 / T ^ 4
      = (1 / T ^ 4) * (chaosZ Sdel j x) ^ 4 by
        rw [div_eq_mul_inv, one_div, mul_comm]]
    exact ENNReal.ofReal_mul hdivnn
  have hZ4meas : Measurable fun x : Sample d n =>
      ENNReal.ofReal ((chaosZ Sdel j x) ^ 4) :=
    ENNReal.continuous_ofReal.measurable.comp (hZ.pow_const 4)
  have hfac : ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4 / T ^ 4)
        ∂(gaussianSampleLaw d n)
      = ENNReal.ofReal (1 / T ^ 4)
        * ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4)
          ∂(gaussianSampleLaw d n) := by
    rw [hcongr]
    exact MeasureTheory.lintegral_const_mul _ hZ4meas
  have hle : ENNReal.ofReal (1 / T ^ 4)
        * ∫⁻ x, ENNReal.ofReal ((chaosZ Sdel j x) ^ 4)
          ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (1 / T ^ 4)
        * ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4) :=
    mul_le_mul_right h4 _
  have hre : ENNReal.ofReal (1 / T ^ 4)
        * ENNReal.ofReal (4 / cHW ^ 2 + 48 / cHW ^ 4)
      = ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) := by
    rw [← ENNReal.ofReal_mul hdivnn]
    congr 1
    conv_rhs => rw [div_eq_mul_inv]
    rw [one_div]
    exact mul_comm _ _
  exact le_trans hmono (le_trans (le_of_eq hfac) (le_trans hle (le_of_eq hre)))

/-- Averaged chaos-plus-shift tail bound (empirical UI, per row). -/
theorem averagedChaos_tail_le {d n : Nat} (hd : 1 ≤ d) (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel)
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ Sdel j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    (μfn : Sample d n → Real) (_hμfn : Measurable μfn)
    {K L T : Real} (hT : 0 < T) (hTdef : T = L - K)
    (hμ : ∀ x, |μfn x| ≤ K) :
    ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x + μfn x) L)
        ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) := by
  have hZ : Measurable (chaosZ Sdel j) := measurable_chaosZ j Sdel hSdel
  have htail := lintegral_tailSquare_le_fourth hd j Sdel hSdel hcHW hHW hT
  have hind := lintegral_chaosInd_le_fourth hd j Sdel hSdel hcHW hHW hT
  have hc2 : (0 : ℝ) < cHW ^ 2 := by positivity
  have hc4 : (0 : ℝ) < cHW ^ 4 := by positivity
  have hM4 : (0 : ℝ) ≤ 4 / cHW ^ 2 + 48 / cHW ^ 4 :=
    add_nonneg (div_nonneg (by norm_num) hc2.le)
      (div_nonneg (by norm_num) hc4.le)
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hT4 : (0 : ℝ) < T ^ 4 := by positivity
  have hM4T2 : (0 : ℝ) ≤ (4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2 :=
    div_nonneg hM4 hT2.le
  have hM4T4 : (0 : ℝ) ≤ (4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4 :=
    div_nonneg hM4 hT4.le
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  have hK2 : (0 : ℝ) ≤ 2 * K ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg K)
  have h2M2 : (0 : ℝ) ≤ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2) :=
    mul_nonneg h2nn hM4T2
  have hKM4 : (0 : ℝ) ≤ (2 * K ^ 2)
      * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) :=
    mul_nonneg hK2 hM4T4
  have hdom : ∀ x : Sample d n,
      ENNReal.ofReal (tailSquare (chaosZ Sdel j x + μfn x) L)
        ≤ ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T
          + 2 * K ^ 2 * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)) :=
    fun x => ENNReal.ofReal_le_ofReal
      (tailSquare_chaos_le (hμ x) hTdef)
  have hmono : ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x + μfn x) L)
        ∂(gaussianSampleLaw d n)
      ≤ ∫⁻ x, ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T
          + 2 * K ^ 2 * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0))
        ∂(gaussianSampleLaw d n) :=
    MeasureTheory.lintegral_mono hdom
  have hAmeas : Measurable fun x : Sample d n =>
      ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((measurable_tailSquare_comp hZ T).const_mul 2)
  have hcongr : (fun x : Sample d n => ENNReal.ofReal
          (2 * tailSquare (chaosZ Sdel j x) T
            + 2 * K ^ 2 * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)))
      = fun x => ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T)
        + ENNReal.ofReal (2 * K ^ 2
          * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)) := by
    funext x
    apply ENNReal.ofReal_add
    · exact mul_nonneg (by norm_num) (tailSquare_nonneg _ _)
    · apply mul_nonneg hK2
      split_ifs <;> norm_num
  have hsplit : ∫⁻ x, ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T
          + 2 * K ^ 2 * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0))
        ∂(gaussianSampleLaw d n)
      = ∫⁻ x, ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T)
          ∂(gaussianSampleLaw d n)
        + ∫⁻ x, ENNReal.ofReal (2 * K ^ 2
            * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0))
          ∂(gaussianSampleLaw d n) := by
    rw [hcongr]
    exact MeasureTheory.lintegral_add_left hAmeas _
  have hTmeas : Measurable fun x : Sample d n =>
      ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T) :=
    ENNReal.continuous_ofReal.measurable.comp
      (measurable_tailSquare_comp hZ T)
  have hcongrA : (fun x : Sample d n =>
        ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T))
      = fun x => ENNReal.ofReal 2
        * ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T) := by
    funext x
    exact ENNReal.ofReal_mul h2nn
  have hfacA : ∫⁻ x, ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T)
        ∂(gaussianSampleLaw d n)
      = ENNReal.ofReal 2
        * ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T)
          ∂(gaussianSampleLaw d n) := by
    rw [hcongrA]
    exact MeasureTheory.lintegral_const_mul _ hTmeas
  have hImeas : Measurable fun x : Sample d n =>
      ENNReal.ofReal (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0) :=
    ENNReal.continuous_ofReal.measurable.comp (measurable_tailInd hZ T)
  have hcongrB : (fun x : Sample d n => ENNReal.ofReal (2 * K ^ 2
          * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)))
      = fun x => ENNReal.ofReal (2 * K ^ 2)
        * ENNReal.ofReal
          (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0) := by
    funext x
    exact ENNReal.ofReal_mul hK2
  have hfacB : ∫⁻ x, ENNReal.ofReal (2 * K ^ 2
          * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0))
        ∂(gaussianSampleLaw d n)
      = ENNReal.ofReal (2 * K ^ 2)
        * ∫⁻ x, ENNReal.ofReal
          (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)
          ∂(gaussianSampleLaw d n) := by
    rw [hcongrB]
    exact MeasureTheory.lintegral_const_mul _ hImeas
  have hleA : ENNReal.ofReal 2
        * ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x) T)
          ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal 2
        * ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2) :=
    mul_le_mul_right htail _
  have hleB : ENNReal.ofReal (2 * K ^ 2)
        * ∫⁻ x, ENNReal.ofReal
          (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)
          ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (2 * K ^ 2)
        * ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) :=
    mul_le_mul_right hind _
  have hre : ENNReal.ofReal 2
        * ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + ENNReal.ofReal (2 * K ^ 2)
          * ENNReal.ofReal ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)
      = ENNReal.ofReal (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) := by
    rw [← ENNReal.ofReal_mul h2nn, ← ENNReal.ofReal_mul hK2,
      ← ENNReal.ofReal_add h2M2 hKM4]
  calc ∫⁻ x, ENNReal.ofReal (tailSquare (chaosZ Sdel j x + μfn x) L)
          ∂(gaussianSampleLaw d n)
      ≤ ∫⁻ x, ENNReal.ofReal (2 * tailSquare (chaosZ Sdel j x) T
            + 2 * K ^ 2 * (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0))
          ∂(gaussianSampleLaw d n) := hmono
    _ = _ := hsplit
    _ = ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal
            (tailSquare (chaosZ Sdel j x) T) ∂(gaussianSampleLaw d n)
          + ENNReal.ofReal (2 * K ^ 2) * ∫⁻ x, ENNReal.ofReal
            (if T < |chaosZ Sdel j x| then (1 : ℝ) else 0)
            ∂(gaussianSampleLaw d n) := by rw [hfacA, hfacB]
    _ ≤ _ := add_le_add hleA hleB
    _ = _ := hre

/-! ### PHASE 5b-ix: residual–chaos split, shift measurability, UI instantiation -/

/-- Pointwise residual↔chaos identity (checkpoint §6.1): the deleted residual
splits as centered chaos plus the deleted mean-shift. Pure field algebra
(`√d ≠ 0` from `d ≥ 1`). -/
theorem residual_eq_chaos_add_shift {d n : Nat} (hd : 1 ≤ d)
    (Sdel : Sample d n → Square d) (j : Fin n) (x : Sample d n) :
    residual x (Sdel x) j
      = chaosZ Sdel j x + deletedMeanShift d (Sdel x) := by
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hsqne : Real.sqrt (d : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hdR)
  show (quadratic (Sdel x) (x j) - (d : ℝ)) / Real.sqrt (d : ℝ)
    = (quadratic (Sdel x) (x j) - (Sdel x).trace) / Real.sqrt (d : ℝ)
      + deletedMeanShift d (Sdel x)
  unfold deletedMeanShift
  field_simp
  ring

/-- Trace of a measurable selector is measurable (checkpoint §6.2 helper). -/
theorem measurable_trace_comp {d n : Nat}
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel) :
    Measurable fun x : Sample d n => (Sdel x).trace := by
  have heq : (fun x : Sample d n => (Sdel x).trace)
      = fun x => ∑ i, Sdel x i i := by
    funext x
    simp [Matrix.trace, Matrix.diag_apply]
  rw [heq]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hSdel)

/-- The deleted mean-shift process is measurable (checkpoint §6.2). -/
theorem measurable_deletedMeanShift {d n : Nat}
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel) :
    Measurable fun x => deletedMeanShift d (Sdel x) := by
  unfold deletedMeanShift
  exact ((measurable_trace_comp Sdel hSdel).sub measurable_const).div_const _

/-- The deleted residual process is measurable. -/
theorem measurable_deletedResidual {d n : Nat} (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel) :
    Measurable fun x : Sample d n => residual x (Sdel x) j := by
  have hquad : Measurable fun x : Sample d n =>
      quadratic (Sdel x) (x j) :=
    continuous_quadratic.measurable.comp
      (hSdel.prodMk (measurable_pi_apply j))
  have heq : (fun x : Sample d n => residual x (Sdel x) j)
      = fun x => (quadratic (Sdel x) (x j) - (d : ℝ))
        / Real.sqrt (d : ℝ) := rfl
  rw [heq]
  exact (hquad.sub measurable_const).div_const _

/-- UI instantiation at the deleted residuals (checkpoint §6.3): the
`averagedChaos_tail_le` bound transferred along `residual_eq_chaos_add_shift`,
conditional on a uniform shift bound `K`. -/
theorem deletedResidual_tail_of_shiftBound {d n : Nat} (hd : 1 ≤ d) (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel)
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ Sdel j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {K L T : Real} (hT : 0 < T) (hTdef : T = L - K)
    (hμ : ∀ x, |deletedMeanShift d (Sdel x)| ≤ K) :
    ∫⁻ x, ENNReal.ofReal (tailSquare (residual x (Sdel x) j) L)
        ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) := by
  have hfun : (fun x : Sample d n =>
        ENNReal.ofReal (tailSquare (residual x (Sdel x) j) L))
      = fun x => ENNReal.ofReal
        (tailSquare (chaosZ Sdel j x + deletedMeanShift d (Sdel x)) L) := by
    funext x
    rw [residual_eq_chaos_add_shift hd Sdel j x]
  rw [hfun]
  exact averagedChaos_tail_le hd j Sdel hSdel hcHW hHW
    (fun x => deletedMeanShift d (Sdel x))
    (measurable_deletedMeanShift Sdel hSdel) hT hTdef hμ

/-- Global deleted mean-shift bound from box membership (uniform in `x`,
no good event needed): `|μ| ≤ √d·(|lo| + |hi| + 1)`. -/
theorem deletedMeanShift_global_le {d : Nat} (hd : 1 ≤ d)
    {lo hi : Real} {S : Square d} (hS : S ∈ spectralBox d lo hi) :
    |deletedMeanShift d S| ≤ Real.sqrt (d : ℝ) * (|lo| + |hi| + 1) := by
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hdnn : (0 : ℝ) ≤ d := hdR.le
  have hsqpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hsqne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsqpos
  have hsq := Real.mul_self_sqrt hdR.le
  have hkey : (d : ℝ) / Real.sqrt (d : ℝ) = Real.sqrt (d : ℝ) := by
    rw [div_eq_iff hsqne]
    exact hsq.symm
  obtain ⟨hlo, hhi⟩ := trace_mem_box_of_mem_box hS
  have hTr : |S.trace| ≤ (|lo| + |hi|) * (d : ℝ) := by
    rw [abs_le]
    constructor
    · have h1 : -(|lo| * (d : ℝ)) ≤ lo * (d : ℝ) := by
        calc -(|lo| * (d : ℝ)) = -|lo| * (d : ℝ) := by ring
          _ ≤ lo * (d : ℝ) :=
            mul_le_mul_of_nonneg_right (neg_abs_le lo) hdnn
      have h2 : -((|lo| + |hi|) * (d : ℝ)) ≤ -(|lo| * (d : ℝ)) := by
        have hle : |lo| * (d : ℝ) ≤ (|lo| + |hi|) * (d : ℝ) :=
          mul_le_mul_of_nonneg_right
            (le_add_of_nonneg_right (abs_nonneg hi)) hdnn
        linarith
      linarith [hlo]
    · have h1 : hi * (d : ℝ) ≤ |hi| * (d : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self hi) hdnn
      have h2 : |hi| * (d : ℝ) ≤ (|lo| + |hi|) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (abs_nonneg lo)) hdnn
      linarith [hhi]
  have hmu : |deletedMeanShift d S|
      = |S.trace - (d : ℝ)| / Real.sqrt (d : ℝ) := by
    unfold deletedMeanShift
    rw [abs_div, abs_of_pos hsqpos]
  rw [hmu]
  have hnum : |S.trace - (d : ℝ)| ≤ (|lo| + |hi| + 1) * (d : ℝ) := by
    calc |S.trace - (d : ℝ)| ≤ |S.trace| + |(d : ℝ)| := abs_sub _ _
      _ = |S.trace| + (d : ℝ) := by rw [abs_of_nonneg hdnn]
      _ ≤ (|lo| + |hi|) * (d : ℝ) + (d : ℝ) := add_le_add hTr le_rfl
      _ = (|lo| + |hi| + 1) * (d : ℝ) := by ring
  calc |S.trace - (d : ℝ)| / Real.sqrt (d : ℝ)
        ≤ ((|lo| + |hi| + 1) * (d : ℝ)) / Real.sqrt (d : ℝ) :=
          div_le_div_of_nonneg_right hnum hsqpos.le
      _ = (|lo| + |hi| + 1) * ((d : ℝ) / Real.sqrt (d : ℝ)) := by ring
      _ = (|lo| + |hi| + 1) * Real.sqrt (d : ℝ) := by rw [hkey]
      _ = Real.sqrt (d : ℝ) * (|lo| + |hi| + 1) := by ring

/-- Per-row deleted-residual tail bound with the global shift constant
(checkpoint §6.3 with `K := √d·(|lo| + |hi| + 1)`). -/
theorem deletedResidual_tail_global {d n : Nat} (hd : 1 ≤ d) (j : Fin n)
    (Sdel : Sample d n → Square d) (hSdel : Measurable Sdel)
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ Sdel j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {lo hi : Real} (hSbox : ∀ x, Sdel x ∈ spectralBox d lo hi)
    {L T : Real} (hT : 0 < T)
    (hTdef : T = L - Real.sqrt (d : ℝ) * (|lo| + |hi| + 1)) :
    ∫⁻ x, ENNReal.ofReal (tailSquare (residual x (Sdel x) j) L)
        ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * (Real.sqrt (d : ℝ) * (|lo| + |hi| + 1)) ^ 2
          * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) :=
  deletedResidual_tail_of_shiftBound hd j Sdel hSdel hcHW hHW hT hTdef
    (fun x => deletedMeanShift_global_le hd (hSbox x))

/-- Mean-over-`j` Markov assembly (checkpoint §6.4): the deleted tail-mean
exceeds `ε` with probability at most `B/ε`, from per-row UI bounds
(`lintegral_finsetSum` + `mul_meas_ge_le_lintegral`). -/
theorem deletedTailMean_markov {d n : Nat} (hd : 1 ≤ d) (hn : 0 < n)
    (Sdel : Fin n → Sample d n → Square d)
    (hSdel : ∀ j, Measurable (Sdel j))
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {K L T : Real} (hT : 0 < T) (hTdef : T = L - K)
    (hμ : ∀ j : Fin n, ∀ x, |deletedMeanShift d (Sdel j x)| ≤ K)
    {ε : Real} (hε : 0 < ε) :
    ((gaussianSampleLaw d n)
      {x | ε ≤ (∑ j, tailSquare (residual x (Sdel j x) j) L)
        / (n : ℝ)}).toReal
      ≤ (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) / ε := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := (mul_pos hnR hε).le
  have hc2 : (0 : ℝ) < cHW ^ 2 := by positivity
  have hc4 : (0 : ℝ) < cHW ^ 4 := by positivity
  have hM4 : (0 : ℝ) ≤ 4 / cHW ^ 2 + 48 / cHW ^ 4 :=
    add_nonneg (div_nonneg (by norm_num) hc2.le)
      (div_nonneg (by norm_num) hc4.le)
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hT4 : (0 : ℝ) < T ^ 4 := by positivity
  have hB : (0 : ℝ) ≤ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
      + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) :=
    add_nonneg (mul_nonneg (by norm_num) (div_nonneg hM4 hT2.le))
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K))
        (div_nonneg hM4 hT4.le))
  have hmeas : ∀ j : Fin n, Measurable fun x : Sample d n =>
      ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L) :=
    fun j => ENNReal.continuous_ofReal.measurable.comp
      (measurable_tailSquare_comp
        (measurable_deletedResidual j (Sdel j) (hSdel j)) L)
  have hrow : ∀ j : Fin n,
      ∫⁻ x, ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L)
        ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) :=
    fun j => deletedResidual_tail_of_shiftBound hd j (Sdel j) (hSdel j)
      hcHW (hHW j) hT hTdef (hμ j)
  have hGsum : Measurable fun x : Sample d n =>
      ∑ j, ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L) :=
    Finset.measurable_sum _ fun j _ => hmeas j
  have hsum : ∫⁻ x, (∑ j, ENNReal.ofReal
      (tailSquare (residual x (Sdel j x) j) L)) ∂(gaussianSampleLaw d n)
      = ∑ j, ∫⁻ x, ENNReal.ofReal
        (tailSquare (residual x (Sdel j x) j) L) ∂(gaussianSampleLaw d n) :=
    MeasureTheory.lintegral_finsetSum _ fun j _ => hmeas j
  have hle : (∑ j : Fin n, ∫⁻ x, ENNReal.ofReal
      (tailSquare (residual x (Sdel j x) j) L) ∂(gaussianSampleLaw d n))
      ≤ (n : ℝ≥0∞)
        * ENNReal.ofReal (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
          + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) := by
    calc (∑ j : Fin n, ∫⁻ x, ENNReal.ofReal
            (tailSquare (residual x (Sdel j x) j) L)
            ∂(gaussianSampleLaw d n))
          ≤ ∑ _j : Fin n, ENNReal.ofReal
            (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
              + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) :=
            Finset.sum_le_sum fun j _ => hrow j
      _ = (n : ℝ≥0∞) * ENNReal.ofReal
          (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
            + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hNB : (n : ℝ≥0∞) * ENNReal.ofReal
      (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4))
      = ENNReal.ofReal ((n : ℝ)
        * (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
          + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  have hfin : (n : ℝ≥0∞) * ENNReal.ofReal
      (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) ≠ ∞ := by
    rw [hNB]
    exact ENNReal.ofReal_ne_top
  have hmark : ENNReal.ofReal ((n : ℝ) * ε)
        * (gaussianSampleLaw d n) {x | ENNReal.ofReal ((n : ℝ) * ε)
          ≤ ∑ j, ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L)}
      ≤ ∫⁻ x, (∑ j, ENNReal.ofReal
        (tailSquare (residual x (Sdel j x) j) L))
        ∂(gaussianSampleLaw d n) :=
    MeasureTheory.mul_meas_ge_le_lintegral hGsum _
  have hSnn : ∀ x : Sample d n,
      (0 : ℝ) ≤ ∑ j, tailSquare (residual x (Sdel j x) j) L :=
    fun x => Finset.sum_nonneg fun j _ => tailSquare_nonneg _ _
  have hset : {x : Sample d n | ε ≤ (∑ j, tailSquare (residual x (Sdel j x) j) L)
        / (n : ℝ)}
      = {x | ENNReal.ofReal ((n : ℝ) * ε)
        ≤ ∑ j, ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg
        (fun j _ => tailSquare_nonneg _ _),
      ENNReal.ofReal_le_ofReal_iff (hSnn x),
      le_div_iff₀ hnR, mul_comm ε (n : ℝ)]
  have hchain : ENNReal.ofReal ((n : ℝ) * ε)
        * (gaussianSampleLaw d n) {x | ENNReal.ofReal ((n : ℝ) * ε)
          ≤ ∑ j, ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L)}
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal
        (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
          + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) :=
    le_trans hmark (le_trans (le_of_eq hsum) hle)
  rw [hset]
  have h := ENNReal.toReal_mono hfin hchain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnε, hNB,
    ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) hB)] at h
  have h2 : ε * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
      ≤ ∑ j, ENNReal.ofReal (tailSquare (residual x (Sdel j x) j) L)}).toReal
      ≤ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
        + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) := by
    have h3 : (n : ℝ)
        * (ε * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
          ≤ ∑ j, ENNReal.ofReal
            (tailSquare (residual x (Sdel j x) j) L)}).toReal)
        ≤ (n : ℝ) * (2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
          + 2 * K ^ 2 * ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)) := by
      have heq : (n : ℝ)
          * (ε * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
            ≤ ∑ j, ENNReal.ofReal
              (tailSquare (residual x (Sdel j x) j) L)}).toReal)
          = ((n : ℝ) * ε)
            * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
              ≤ ∑ j, ENNReal.ofReal
                (tailSquare (residual x (Sdel j x) j) L)}).toReal := by ring
      rw [heq]
      exact h
    exact le_of_mul_le_mul_left h3 hnR
  exact (le_div_iff₀ hε).mpr (by linarith [h2])

/-- Huber L2 bulk transfer (checkpoint §6.4, deterministic, pointwise in `x`):
the full-selector mean-square splits into a Huber-controlled bulk
(`truncatedSquare_le_two_mul_huber`) plus the LOO tail-mean
(`loo_tailSquare_average`). -/
theorem loo_l2_transfer {d n : Nat} (x : Sample d n) (hn : 1 < n)
    {lo hi : Real} {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j))
    {M : Real} (hM1 : 1 ≤ M)
    (hM : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M) :
    (∑ j, (residual x Sstar j) ^ 2) / (n : ℝ)
      ≤ 2 * M * empiricalHuber (residual x Sstar)
        + (2 * ((∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
            / (n : ℝ))
          + 2 * (huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))) ^ 2) := by
  have hnR : (0 : ℝ) < n := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith [zero_lt_one (α := ℝ)]
  have hsplit : (∑ j, (residual x Sstar j) ^ 2)
      = (∑ j, truncatedSquare (residual x Sstar j) M)
        + (∑ j, tailSquare (residual x Sstar j) M) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact sq_eq_truncatedSquare_add_tailSquare _ _
  have hbulk : (∑ j, truncatedSquare (residual x Sstar j) M) / (n : ℝ)
      ≤ 2 * M * empiricalHuber (residual x Sstar) := by
    have hle : (∑ j, truncatedSquare (residual x Sstar j) M)
        ≤ ∑ j, 2 * M * huber (residual x Sstar j) :=
      Finset.sum_le_sum fun j _ => truncatedSquare_le_two_mul_huber _ hM1
    have hdiv := div_le_div_of_nonneg_right hle hnR.le
    have heq : (∑ j, 2 * M * huber (residual x Sstar j)) / (n : ℝ)
        = 2 * M * empiricalHuber (residual x Sstar) := by
      have hms : (∑ j, 2 * M * huber (residual x Sstar j))
          = (2 * M) * (∑ j, huber (residual x Sstar j)) := by
        rw [← Finset.mul_sum]
      rw [hms]
      unfold empiricalHuber empiricalAverage
      simp only [Fintype.card_fin]
      rw [mul_div_assoc]
    rwa [heq] at hdiv
  have htail := loo_tailSquare_average x hn hStar Sdel hDel hM
  rw [hsplit, add_div]
  exact add_le_add hbulk htail

/-- L∞ union-bound transfer (checkpoint §6.4): the deleted-residual sup-norm
tail via HW exponential tails + union bound (repo `rowNormSq_union_tail`
pattern), conditional on a uniform shift bound `K`. -/
theorem deletedLinf_union_tail {d n : Nat} (hd : 1 ≤ d)
    (Sdel : Fin n → Sample d n → Square d)
    {cHW : Real}
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {K Tlvl : Real} (hTK : 0 ≤ Tlvl - K)
    (hμ : ∀ j : Fin n, ∀ x, |deletedMeanShift d (Sdel j x)| ≤ K) :
    ((gaussianSampleLaw d n)
      (⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|})).toReal
      ≤ (n : ℝ) * (2 * Real.exp (-cHW
        * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
  have hbound_nn : (0 : ℝ) ≤ 2 * Real.exp (-cHW
      * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ))) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hsub : ∀ j : Fin n, {x : Sample d n | Tlvl < |residual x (Sdel j x) j|}
      ⊆ {x | Tlvl - K < |chaosZ (Sdel j) j x|} := by
    intro j x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hres := residual_eq_chaos_add_shift hd (Sdel j) j x
    have hab := abs_add_le
      (chaosZ (Sdel j) j x) (deletedMeanShift d (Sdel j x))
    have hμx := hμ j x
    rw [hres] at hx
    linarith [hx, hab, hμx]
  have hEj : ∀ j : Fin n,
      (gaussianSampleLaw d n) {x | Tlvl < |residual x (Sdel j x) j|}
        ≤ ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
    intro j
    have h1 : (gaussianSampleLaw d n) {x | Tlvl < |residual x (Sdel j x) j|}
        ≤ (gaussianSampleLaw d n)
          {x | Tlvl - K < |chaosZ (Sdel j) j x|} :=
      MeasureTheory.measure_mono (hsub j)
    have h2 : (gaussianSampleLaw d n)
          {x | Tlvl - K < |chaosZ (Sdel j) j x|}
        ≤ ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
      have hfin : (gaussianSampleLaw d n)
          {x | Tlvl - K < |chaosZ (Sdel j) j x|} ≠ ∞ :=
        (MeasureTheory.measure_lt_top _ _).ne
      calc (gaussianSampleLaw d n) {x | Tlvl - K < |chaosZ (Sdel j) j x|}
            = ENNReal.ofReal (((gaussianSampleLaw d n)
              {x | Tlvl - K < |chaosZ (Sdel j) j x|}).toReal) :=
              (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal (2 * Real.exp (-cHW
            * min ((Tlvl - K) ^ 2)
              ((Tlvl - K) * Real.sqrt (d : ℝ)))) :=
            ENNReal.ofReal_le_ofReal (hHW j (Tlvl - K) hTK)
    exact le_trans h1 h2
  have hunion : (gaussianSampleLaw d n)
        (⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|})
      ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)),
        ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
    have h1 : (gaussianSampleLaw d n)
          (⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|})
        ≤ ∑' j : Fin n,
          (gaussianSampleLaw d n)
            {x | Tlvl < |residual x (Sdel j x) j|} :=
      MeasureTheory.measure_iUnion_le _
    rw [tsum_fintype] at h1
    exact le_trans h1 (Finset.sum_le_sum fun j _ => hEj j)
  have hfin : (∑ j ∈ (Finset.univ : Finset (Fin n)),
      ENNReal.ofReal (2 * Real.exp (-cHW
        * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ))))) ≠ ∞ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hbound_nn)]
    exact ENNReal.ofReal_ne_top
  calc ((gaussianSampleLaw d n)
          (⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|})).toReal
      ≤ (∑ j ∈ (Finset.univ : Finset (Fin n)),
          ENNReal.ofReal (2 * Real.exp (-cHW
            * min ((Tlvl - K) ^ 2)
              ((Tlvl - K) * Real.sqrt (d : ℝ))))).toReal :=
        ENNReal.toReal_mono hfin hunion
    _ = ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2)
            ((Tlvl - K) * Real.sqrt (d : ℝ))))).toReal :=
        ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)
    _ = ∑ _j ∈ (Finset.univ : Finset (Fin n)),
        (2 * Real.exp (-cHW * min ((Tlvl - K) ^ 2)
          ((Tlvl - K) * Real.sqrt (d : ℝ)))) :=
        Finset.sum_congr rfl fun j _ =>
          ENNReal.toReal_ofReal hbound_nn
    _ = (n : ℝ) * (2 * Real.exp (-cHW * min ((Tlvl - K) ^ 2)
        ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### PHASE 5b-ix (g)-enablers: general mean-Markov, chaos corollaries -/

/-- General mean-over-`j` Markov assembly: for any nonnegative processes with
uniform per-row lintegral bounds, the mean exceeds `ε` with probability at
most `B/ε`. `deletedTailMean_markov` is the shift-process instance; the
chaos-only corollaries below feed the `huberResiduals_theorem` L2 route
(on-good pointwise domination + global chaos moments, no clamped shifts). -/
theorem lintegralMean_markov {d n : Nat} (hn : 0 < n)
    (f : Fin n → Sample d n → ℝ) (hf : ∀ j x, 0 ≤ f j x)
    (hmeas : ∀ j, Measurable fun x => ENNReal.ofReal (f j x))
    (B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ j, ∫⁻ x, ENNReal.ofReal (f j x) ∂(gaussianSampleLaw d n)
      ≤ ENNReal.ofReal B)
    {ε : Real} (hε : 0 < ε) :
    ((gaussianSampleLaw d n)
      {x | ε ≤ (∑ j, f j x) / (n : ℝ)}).toReal ≤ B / ε := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnε : (0 : ℝ) ≤ (n : ℝ) * ε := (mul_pos hnR hε).le
  have hGsum : Measurable fun x : Sample d n =>
      ∑ j, ENNReal.ofReal (f j x) :=
    Finset.measurable_sum _ fun j _ => hmeas j
  have hsum : ∫⁻ x, (∑ j, ENNReal.ofReal (f j x)) ∂(gaussianSampleLaw d n)
      = ∑ j, ∫⁻ x, ENNReal.ofReal (f j x) ∂(gaussianSampleLaw d n) :=
    MeasureTheory.lintegral_finsetSum _ fun j _ => hmeas j
  have hle : (∑ j : Fin n, ∫⁻ x, ENNReal.ofReal (f j x)
      ∂(gaussianSampleLaw d n))
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal B := by
    calc (∑ j : Fin n, ∫⁻ x, ENNReal.ofReal (f j x)
            ∂(gaussianSampleLaw d n))
          ≤ ∑ _j : Fin n, ENNReal.ofReal B :=
            Finset.sum_le_sum fun j _ => hrow j
      _ = (n : ℝ≥0∞) * ENNReal.ofReal B := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hNB : (n : ℝ≥0∞) * ENNReal.ofReal B
      = ENNReal.ofReal ((n : ℝ) * B) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  have hfin : (n : ℝ≥0∞) * ENNReal.ofReal B ≠ ∞ := by
    rw [hNB]
    exact ENNReal.ofReal_ne_top
  have hmark : ENNReal.ofReal ((n : ℝ) * ε)
        * (gaussianSampleLaw d n) {x | ENNReal.ofReal ((n : ℝ) * ε)
          ≤ ∑ j, ENNReal.ofReal (f j x)}
      ≤ ∫⁻ x, (∑ j, ENNReal.ofReal (f j x)) ∂(gaussianSampleLaw d n) :=
    MeasureTheory.mul_meas_ge_le_lintegral hGsum _
  have hSnn : ∀ x : Sample d n, (0 : ℝ) ≤ ∑ j, f j x :=
    fun x => Finset.sum_nonneg fun j _ => hf j x
  have hset : {x : Sample d n | ε ≤ (∑ j, f j x) / (n : ℝ)}
      = {x | ENNReal.ofReal ((n : ℝ) * ε)
        ≤ ∑ j, ENNReal.ofReal (f j x)} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hf j x),
      ENNReal.ofReal_le_ofReal_iff (hSnn x),
      le_div_iff₀ hnR, mul_comm ε (n : ℝ)]
  have hchain : ENNReal.ofReal ((n : ℝ) * ε)
        * (gaussianSampleLaw d n) {x | ENNReal.ofReal ((n : ℝ) * ε)
          ≤ ∑ j, ENNReal.ofReal (f j x)}
      ≤ (n : ℝ≥0∞) * ENNReal.ofReal B :=
    le_trans hmark (le_trans (le_of_eq hsum) hle)
  rw [hset]
  have h := ENNReal.toReal_mono hfin hchain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hnε, hNB,
    ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg n) hB)] at h
  have h2 : ε * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
      ≤ ∑ j, ENNReal.ofReal (f j x)}).toReal ≤ B := by
    have h3 : (n : ℝ)
        * (ε * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
          ≤ ∑ j, ENNReal.ofReal (f j x)}).toReal)
        ≤ (n : ℝ) * B := by
      have heq : (n : ℝ)
          * (ε * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
            ≤ ∑ j, ENNReal.ofReal (f j x)}).toReal)
          = ((n : ℝ) * ε)
            * ((gaussianSampleLaw d n) {x | ENNReal.ofReal (↑n * ε)
              ≤ ∑ j, ENNReal.ofReal (f j x)}).toReal := by ring
      rw [heq]
      exact h
    exact le_of_mul_le_mul_left h3 hnR
  exact (le_div_iff₀ hε).mpr (by linarith [h2])

/-- Chaos-only tail-mean Markov bound (no shifts). -/
theorem chaosTailMean_markov {d n : Nat} (hd : 1 ≤ d) (hn : 0 < n)
    (Sdel : Fin n → Sample d n → Square d)
    (hSdel : ∀ j, Measurable (Sdel j))
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {T : Real} (hT : 0 < T) {ε : Real} (hε : 0 < ε) :
    ((gaussianSampleLaw d n)
      {x | ε ≤ (∑ j, tailSquare (chaosZ (Sdel j) j x) T)
        / (n : ℝ)}).toReal
      ≤ ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2) / ε := by
  have hc2 : (0 : ℝ) < cHW ^ 2 := by positivity
  have hc4 : (0 : ℝ) < cHW ^ 4 := by positivity
  have hM4 : (0 : ℝ) ≤ 4 / cHW ^ 2 + 48 / cHW ^ 4 :=
    add_nonneg (div_nonneg (by norm_num) hc2.le)
      (div_nonneg (by norm_num) hc4.le)
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  exact lintegralMean_markov hn
    (fun j x => tailSquare (chaosZ (Sdel j) j x) T)
    (fun j x => tailSquare_nonneg _ _)
    (fun j => ENNReal.continuous_ofReal.measurable.comp
      (measurable_tailSquare_comp
        (measurable_chaosZ j (Sdel j) (hSdel j)) T))
    _ (div_nonneg hM4 hT2.le)
    (fun j => lintegral_tailSquare_le_fourth hd j (Sdel j) (hSdel j)
      hcHW (hHW j) hT)
    hε

/-- Chaos-only indicator-mean Markov bound (no shifts). -/
theorem chaosIndMean_markov {d n : Nat} (hd : 1 ≤ d) (hn : 0 < n)
    (Sdel : Fin n → Sample d n → Square d)
    (hSdel : ∀ j, Measurable (Sdel j))
    {cHW : Real} (hcHW : 0 < cHW)
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {T : Real} (hT : 0 < T) {ε : Real} (hε : 0 < ε) :
    ((gaussianSampleLaw d n)
      {x | ε ≤ (∑ j, (if T < |chaosZ (Sdel j) j x| then (1 : ℝ) else 0))
        / (n : ℝ)}).toReal
      ≤ ((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4) / ε := by
  have hc2 : (0 : ℝ) < cHW ^ 2 := by positivity
  have hc4 : (0 : ℝ) < cHW ^ 4 := by positivity
  have hM4 : (0 : ℝ) ≤ 4 / cHW ^ 2 + 48 / cHW ^ 4 :=
    add_nonneg (div_nonneg (by norm_num) hc2.le)
      (div_nonneg (by norm_num) hc4.le)
  have hT4 : (0 : ℝ) < T ^ 4 := by positivity
  exact lintegralMean_markov hn
    (fun j x => (if T < |chaosZ (Sdel j) j x| then (1 : ℝ) else 0))
    (fun j x => by split_ifs <;> norm_num)
    (fun j => ENNReal.continuous_ofReal.measurable.comp
      (measurable_tailInd (measurable_chaosZ j (Sdel j) (hSdel j)) T))
    _ (div_nonneg hM4 hT4.le)
    (fun j => lintegral_chaosInd_le_fourth hd j (Sdel j) (hSdel j)
      hcHW (hHW j) hT)
    hε

/-- Small-error value of the Huber inverse (for the vanishing LOO error
`e_d` in `huberResiduals_theorem`). -/
theorem huberInv_of_le_half {e : Real} (h : e ≤ 1 / 2) :
    huberInv e = Real.sqrt (2 * e) := by
  simp only [huberInv, ite_eq_left h]

/-- Pointwise LOO sup transfer: a large full residual forces a large deleted
residual (for the `huberResiduals_theorem` L∞ route). -/
theorem loo_row_sup_transfer {a b e T : Real} (h : |a| ≤ |b| + e)
    (hT : T < |a|) : T - e < |b| := by
  linarith [hT, h]

/-- Centered sum of squares is bounded by the uncentered one
(`huberResiduals_theorem` L2 route: variance ≤ second moment). -/
theorem center_sq_sum_le {n : Nat} (hn : 0 < n) (r : Vector n) :
    ∑ j, (center r j) ^ 2 ≤ ∑ j, (r j) ^ 2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hS : ∑ j, r j = (n : ℝ) * mean r := by
    unfold mean
    rw [mul_div_cancel₀ _ hnne]
  have hterm : ∀ j : Fin n, (center r j) ^ 2
      = (r j) ^ 2 - 2 * (mean r) * (r j) + (mean r) ^ 2 := by
    intro j
    show ((r j - mean r)) ^ 2 = _
    ring
  have h1 : (∑ j, (center r j) ^ 2)
      = (∑ j, (r j) ^ 2) - 2 * (mean r) * (∑ j, r j)
        + (n : ℝ) * (mean r) ^ 2 := by
    calc (∑ j, (center r j) ^ 2)
          = ∑ j, ((r j) ^ 2 - 2 * (mean r) * (r j)
            + (mean r) ^ 2) :=
            Finset.sum_congr rfl (fun j _ => hterm j)
      _ = (∑ j, (r j) ^ 2) - 2 * (mean r) * (∑ j, r j)
          + (n : ℝ) * (mean r) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              ← Finset.mul_sum]
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hS] at h1
  have hnn : (0 : ℝ) ≤ (n : ℝ) * (mean r) ^ 2 :=
    mul_nonneg hnR.le (sq_nonneg _)
  have h2 : (∑ j, (r j) ^ 2) - 2 * (mean r) * ((n : ℝ) * (mean r))
        + (n : ℝ) * (mean r) ^ 2 ≤ ∑ j, (r j) ^ 2 := by
    have heq : (∑ j, (r j) ^ 2) - 2 * (mean r) * ((n : ℝ) * (mean r))
          + (n : ℝ) * (mean r) ^ 2
        = (∑ j, (r j) ^ 2) - (n : ℝ) * (mean r) ^ 2 := by ring
    rw [heq]
    linarith [hnn]
  rwa [h1]

end GaussianEllipsoid

namespace GaussianEllipsoid

/-! ### L2 route for `huberResiduals_theorem` (task L2, phase 5b-ix(g))

Threshold `τ(d) = ε²d²/n(d)`; split by `loo_l2_transfer`; bulk to
BM-bad via `selector_huber_of_bmMinRisk`; tail to on-good chaos
domination via `tailSquare_chaos_le` plus `chaosTailMean_markov` /
`chaosIndMean_markov` with `T = M/2 - Kbar`; deterministic `2e²` via
`huberInv_of_le_half`; centering via `center_sq_sum_le`.
-/

/-- L2 threshold `τ(d) = ε²d²/n`. `ε < ‖center r‖₂/d` forces
`τ(d) ≤ (∑ rⱼ²)/n` (see `l2_tau_of_euclid_gt`). -/
def l2tau (eps : Real) (d n : Nat) : Real :=
  eps ^ 2 * (d : Real) ^ 2 / (n : Real)

theorem l2tau_pos {eps : Real} (he : 0 < eps) {d n : Nat}
    (hd : 0 < d) (hn : 0 < n) : 0 < l2tau eps d n := by
  unfold l2tau
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  positivity

/-- Centered Euclidean square bounded by the uncentered sum
(`euclidNorm_sq` + `center_sq_sum_le`). -/
theorem euclidNorm_center_sq_le {n : Nat} (hn : 0 < n) (r : Vector n) :
    (euclidNorm (center r)) ^ 2 ≤ ∑ j, (r j) ^ 2 := by
  rw [euclidNorm_sq]
  exact center_sq_sum_le hn r

/-- Threshold lemma: a large centered L2 norm forces a large
uncentered mean-square above `τ(d)`. -/
theorem l2_tau_of_euclid_gt {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    {eps : Real} (he : 0 < eps) (x : Sample d n) (Sstar : Square d)
    (h : eps < euclidNorm (center (residual x Sstar)) / (d : Real)) :
    l2tau eps d n ≤ (∑ j, (residual x Sstar j) ^ 2) / (n : Real) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcenter := euclidNorm_center_sq_le hn (residual x Sstar)
  have h1 : eps * (d : ℝ) < euclidNorm (center (residual x Sstar)) := by
    rwa [lt_div_iff₀ hdR] at h
  have hpos : (0 : ℝ) ≤ eps * (d : ℝ) := (mul_pos he hdR).le
  have h2 : (eps * (d : ℝ)) ^ 2
      < (euclidNorm (center (residual x Sstar))) ^ 2 :=
    pow_lt_pow_left₀ h1 hpos (by norm_num)
  have h4 : (eps * (d : ℝ)) ^ 2 ≤ ∑ j, (residual x Sstar j) ^ 2 :=
    le_trans h2.le hcenter
  have h5 : (eps * (d : ℝ)) ^ 2 / (n : ℝ)
      ≤ (∑ j, (residual x Sstar j) ^ 2) / (n : ℝ) :=
    div_le_div_of_nonneg_right h4 hnR.le
  have heq : l2tau eps d n = (eps * (d : ℝ)) ^ 2 / (n : ℝ) := by
    unfold l2tau
    ring
  rwa [heq]

/-- Set form of the threshold lemma (for `measure_mono`). -/
theorem l2_event_subset_tau {d n : Nat} (hd : 0 < d) (hn : 0 < n)
    {eps : Real} (he : 0 < eps) (Sstar : Sample d n → Square d) :
    {x | eps < euclidNorm (center (residual x (Sstar x))) / (d : Real)}
      ⊆ {x | l2tau eps d n
        ≤ (∑ j, (residual x (Sstar x) j) ^ 2) / (n : Real)} := by
  intro x hx
  exact l2_tau_of_euclid_gt hd hn he x (Sstar x) hx

/-- Pure three-way split of a sum bound. -/
theorem l2_split_three {tau b1 b2 b3 : Real}
    (h : tau ≤ b1 + (b2 + b3)) :
    tau / 3 ≤ b1 ∨ tau / 3 ≤ b2 ∨ tau / 3 ≤ b3 := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  linarith

/-- `loo_l2_transfer` followed by the three-way split: a large
mean-square forces a large bulk, tail, or deterministic term. -/
theorem l2_loo_split {d n : Nat} (x : Sample d n) (hn : 1 < n)
    {lo hi : Real} {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j))
    {M : Real} (hM1 : 1 ≤ M)
    (hM : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M)
    {tau : Real}
    (htau : tau ≤ (∑ j, (residual x Sstar j) ^ 2) / (n : Real)) :
    tau / 3 ≤ 2 * M * empiricalHuber (residual x Sstar)
      ∨ tau / 3 ≤ 2 * ((∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
        / (n : Real))
      ∨ tau / 3 ≤ 2 * (huberInv ((|lo| + |hi| + 1) ^ 2
        / (2 * (d : ℝ)))) ^ 2 := by
  have hloo := loo_l2_transfer x hn hStar Sdel hDel hM1 hM
  have hle : tau ≤ 2 * M * empiricalHuber (residual x Sstar)
      + (2 * ((∑ j, tailSquare (residual x (Sdel j) j) (M / 2))
        / (n : Real))
        + 2 * (huberInv ((|lo| + |hi| + 1) ^ 2
          / (2 * (d : ℝ)))) ^ 2) :=
    le_trans htau hloo
  exact l2_split_three hle

/-- Bulk term controlled by BM-bad via `selector_huber_of_bmMinRisk`. -/
theorem l2_bulk_of_bmMinRisk {d n : Nat} (x : Sample d n) (hn : 0 < n)
    {lo hi r epsp : Real} (hle : lo ≤ hi) {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar) (h1 : 1 ≤ r) (h2 : r ≤ 2)
    (h : bmMinRisk d n x lo hi r < epsp) {M : Real} (hM : 0 < M) :
    2 * M * empiricalHuber (residual x Sstar)
      < 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) := by
  have hHub := selector_huber_of_bmMinRisk x hn hle hStar h1 h2 h
  have hpos : (0 : Real) < 2 * M := by linarith
  exact mul_lt_mul_of_pos_left hHub hpos

/-- On-good pointwise tail domination by chaos-only processes
(`residual_eq_chaos_add_shift` + `tailSquare_chaos_le`, summed). -/
theorem l2_tail_chaos_domination {d n : Nat} (hd : 1 ≤ d)
    (Sdel : Fin n → Sample d n → Square d)
    (x : Sample d n) {Kbar M T : Real} (hT : T = M / 2 - Kbar)
    (hμ : ∀ j : Fin n, |deletedMeanShift d (Sdel j x)| ≤ Kbar) :
    ∑ j, tailSquare (residual x (Sdel j x) j) (M / 2)
      ≤ ∑ j, (2 * tailSquare (chaosZ (Sdel j) j x) T
        + 2 * Kbar ^ 2
          * (if T < |chaosZ (Sdel j) j x| then (1 : Real) else 0)) := by
  apply Finset.sum_le_sum
  intro j _
  have hres := residual_eq_chaos_add_shift hd (Sdel j) j x
  rw [hres]
  exact tailSquare_chaos_le (hμ j) hT

/-- Mean form of the chaos domination (divide by `n`). -/
theorem l2_tail_mean_chaos_le {d n : Nat} (hd : 1 ≤ d)
    (Sdel : Fin n → Sample d n → Square d)
    (x : Sample d n) {Kbar M T : Real} (hT : T = M / 2 - Kbar)
    (hμ : ∀ j : Fin n, |deletedMeanShift d (Sdel j x)| ≤ Kbar) :
    (∑ j, tailSquare (residual x (Sdel j x) j) (M / 2)) / (n : Real)
      ≤ (∑ j, (2 * tailSquare (chaosZ (Sdel j) j x) T
        + 2 * Kbar ^ 2
          * (if T < |chaosZ (Sdel j) j x| then (1 : Real) else 0)))
        / (n : Real) :=
  div_le_div_of_nonneg_right
    (l2_tail_chaos_domination hd Sdel x hT hμ) (Nat.cast_nonneg n)

/-- Chaos combo-mean splits into tail-mean plus indicator-mean. -/
theorem l2_chaos_mean_split {d n : Nat}
    (Sdel : Fin n → Sample d n → Square d)
    (x : Sample d n) {Kbar T : Real} :
    (∑ j, (2 * tailSquare (chaosZ (Sdel j) j x) T
        + 2 * Kbar ^ 2
          * (if T < |chaosZ (Sdel j) j x| then (1 : Real) else 0)))
      / (n : Real)
      = 2 * ((∑ j, tailSquare (chaosZ (Sdel j) j x) T) / (n : Real))
        + 2 * Kbar ^ 2 * ((∑ j, (if T < |chaosZ (Sdel j) j x|
          then (1 : Real) else 0)) / (n : Real)) := by
  rw [Finset.sum_add_distrib, add_div]
  congr 1
  · rw [← Finset.mul_sum, mul_div_assoc]
  · rw [← Finset.mul_sum, mul_div_assoc]

/-- Pure split of a chaos combo bound into tail-mean / indicator-mean
alternatives (feeds `chaosTailMean_markov` / `chaosIndMean_markov`). -/
theorem l2_chaos_split {delta A B Kbar : Real}
    (hK : 0 < Kbar)
    (hle : delta ≤ 2 * A + 2 * Kbar ^ 2 * B) :
    delta / 4 ≤ A ∨ delta / (4 * Kbar ^ 2) ≤ B := by
  have hK2 : (0 : Real) < Kbar ^ 2 := by positivity
  have h4K2 : (0 : Real) < 4 * Kbar ^ 2 := by positivity
  have htwo : delta / 2 ≤ 2 * A ∨ delta / 2 ≤ 2 * Kbar ^ 2 * B := by
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    linarith
  cases htwo with
  | inl hA =>
    left
    linarith
  | inr hB =>
    right
    apply (div_le_iff₀ h4K2).mpr
    have heq : B * (4 * Kbar ^ 2) = 2 * (2 * Kbar ^ 2 * B) := by ring
    rw [heq]
    linarith

/-- On-good tail-event inclusion into chaos-only events: on
`{∀ j, |shift| ≤ Kbar}`, a large deleted tail-mean forces a large
chaos tail-mean or chaos indicator-mean. Combine with
`MeasureTheory.measure_mono`, `measure_union_le`, `chaosTailMean_markov`,
`chaosIndMean_markov` for the probability bound. -/
theorem l2_tail_onGood_subset_chaos {d n : Nat} (hd : 1 ≤ d)
    (Sdel : Fin n → Sample d n → Square d)
    {Kbar M T delta : Real} (hT : T = M / 2 - Kbar)
    (hK : 0 < Kbar) :
    {x | (∀ j : Fin n, |deletedMeanShift d (Sdel j x)| ≤ Kbar)
        ∧ delta ≤ (∑ j, tailSquare (residual x (Sdel j x) j) (M / 2))
          / (n : Real)}
      ⊆ {x | delta / 4 ≤ (∑ j, tailSquare (chaosZ (Sdel j) j x) T)
          / (n : Real)}
        ∪ {x | delta / (4 * Kbar ^ 2)
          ≤ (∑ j, (if T < |chaosZ (Sdel j) j x| then (1 : Real) else 0))
            / (n : Real)} := by
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
  obtain ⟨hgood, htail⟩ := hx
  have hdom := l2_tail_mean_chaos_le hd Sdel x hT hgood
  have hsplit := l2_chaos_mean_split Sdel x (Kbar := Kbar) (T := T)
  have hle : delta ≤ 2 * ((∑ j, tailSquare (chaosZ (Sdel j) j x) T)
      / (n : Real))
      + 2 * Kbar ^ 2 * ((∑ j, (if T < |chaosZ (Sdel j) j x|
        then (1 : Real) else 0)) / (n : Real)) := by
    have h := le_trans htail hdom
    rwa [hsplit] at h
  exact l2_chaos_split hK hle

/-- Closed form of the deterministic Huber error via
`huberInv_of_le_half`. -/
theorem l2_huberInv_closed {C d : Real} (hd : 0 < d)
    (h : C / (2 * d) ≤ 1 / 2) :
    huberInv (C / (2 * d)) = Real.sqrt (C / d) := by
  have h2 : 2 * (C / (2 * d)) = C / d := by
    field_simp
  rw [huberInv_of_le_half h, h2]

/-- The `2e²` term equals `2C/d` on the small-error branch. -/
theorem l2_det_error_eq {C d : Real} (hd : 0 < d) (hC : 0 ≤ C)
    (h : C / (2 * d) ≤ 1 / 2) :
    2 * (huberInv (C / (2 * d))) ^ 2 = 2 * C / d := by
  rw [l2_huberInv_closed hd h, Real.sq_sqrt (div_nonneg hC hd.le)]
  ring

/-- Dual-mixed event splits into L∞ and L2 events. -/
theorem l2_dualMixed_event_subset {d n : Nat} {eta eps : Real}
    (Sstar : Sample d n → Square d) :
    {x | eps < dualMixed eta d n (center (residual x (Sstar x)))}
      ⊆ {x | eps < ‖center (residual x (Sstar x))‖
          / (eta * Real.sqrt (d : Real))}
        ∪ {x | eps < euclidNorm (center (residual x (Sstar x)))
          / (d : Real)} := by
  intro x hx
  simp only [dualMixed, Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
  exact lt_max_iff.mp hx

end GaussianEllipsoid

/-! ### g-glue: good-event instantiations for PHASE 5b-ix (g) -/

namespace GaussianEllipsoid

/-- Covariance good-event tail at `t = 1/4`, `v = 2d`: direct instance of
    `deletedCovariance_uniform_tail`. The threshold is `C(d)` (proved
    `→ 0` in `GGlue.tendsto_covThreshold`); the failure bound is
    `2exp(-d/2) + n·exp(-d/2)·(√2)^d` (both `→ 0` by
    `GGlue.tendsto_two_mul_exp_neg_half` and `GGlue.tendsto_chi_union`). -/
theorem cov_good_tail_quarter {d n : Nat} (hd : 0 < d) (hn : 1 < n)
    (hdn : (d : ℝ) ≤ (n : ℝ)) (hDS : davidsonSzarekCovariance) :
    ((gaussianSampleLaw d n)
      {x | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1))
        * (4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ))
        + (1 / ((n : ℝ) - 1)) * (1 + 2 * (d : ℝ))
        < matrixOpNorm (deletedCovariance x j - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2)
        + (n : ℝ)
          * (Real.exp (-(1 / 4) * (2 * (d : ℝ)))
            * (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d) := by
  exact deletedCovariance_uniform_tail hd hn hdn (t := 1 / 4) (v := 2 * (d : ℝ))
    (by norm_num) (by norm_num) (by positivity) hDS

/-- BM good event at `r = 1`: the `bmMinRisk < ε'` failure probability
    tends to zero, as a direct instance of the `BMminRisk` hypothesis. -/
theorem bm_good_event {n : ℕ → ℕ} {lo hi : ℝ} (hBM : BMminRisk n lo hi)
    {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun d : ℕ => ((gaussianSampleLaw d (n d))
      {x | ε < bmMinRisk d (n d) x lo hi 1}).toReal)
      Filter.atTop (nhds 0) :=
  hBM 1 (by norm_num) (by norm_num) ε hε

end GaussianEllipsoid

/-! ### g-Linf: L∞ route lemmas for `huberResiduals_theorem` (phase 5b-ix(g))

Center bound `‖center r‖ ≤ 2‖r‖`, LOO sup set-form, Hanson–Wright
level arithmetic beating `n ~ d²` rows, sup-norm union cover.
Probes verified: `pi_norm_le_iff_of_nonneg : 0 ≤ r → (‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r)`
(`Mathlib.Analysis.Normed.Group.Constructions`); `pi_norm_le_iff`
(unconditional) does NOT exist. -/

namespace GaussianEllipsoid

/-- Mean is sup-norm nonexpansive. -/
theorem mean_abs_le {n : Nat} (hn : 0 < n) (r : Vector n) :
    |mean r| ≤ ‖r‖ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hcoord : ∀ i : Fin n, |r i| ≤ ‖r‖ := by
    intro i
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm r i
  have hsum : |∑ i, r i| ≤ (n : ℝ) * ‖r‖ := by
    calc |∑ i, r i| ≤ ∑ i, |r i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖r‖ := Finset.sum_le_sum fun i _ => hcoord i
      _ = (n : ℝ) * ‖r‖ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hmean : |mean r| = |∑ i, r i| / (n : ℝ) := by
    unfold mean
    rw [abs_div, abs_of_pos hnR]
  rw [hmean, div_le_iff₀ hnR]
  calc |∑ i, r i| ≤ (n : ℝ) * ‖r‖ := hsum
    _ = ‖r‖ * (n : ℝ) := by ring

/-- Center bound: `‖center r‖ ≤ 2‖r‖`. -/
theorem center_pi_norm_le {n : Nat} (hn : 0 < n) (r : Vector n) :
    ‖center r‖ ≤ 2 * ‖r‖ := by
  have h2nn : (0 : ℝ) ≤ 2 * ‖r‖ :=
    mul_nonneg (by norm_num) (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg h2nn).mpr
  intro i
  show ‖center r i‖ ≤ 2 * ‖r‖
  have hci : center r i = r i - mean r := rfl
  rw [hci, Real.norm_eq_abs]
  have h1 : |r i| ≤ ‖r‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm r i
  have h2 : |mean r| ≤ ‖r‖ := mean_abs_le hn r
  calc |r i - mean r| ≤ |r i| + |mean r| := abs_sub _ _
    _ ≤ ‖r‖ + ‖r‖ := add_le_add h1 h2
    _ = 2 * ‖r‖ := by ring

/-- Set form of the LOO sup transfer (for the union glue). -/
theorem full_deleted_sup_subset {n : Nat} {A B : Fin n → Real} {e T : Real}
    (h : ∀ j, |A j| ≤ |B j| + e) :
    {j : Fin n | T < |A j|} ⊆ {j : Fin n | T - e < |B j|} := by
  intro j hj
  simp only [Set.mem_ofPred_eq] at hj ⊢
  exact loo_row_sup_transfer (h j) hj

/-- At shifted level `s := Tlvl - K ≥ √d`, the Hanson–Wright
exponent `min (s²) (s√d)` is at least `d`. -/
theorem hw_min_ge_of_level {d : Nat} (hd : 1 ≤ d) {s : Real}
    (hs : Real.sqrt (d : ℝ) ≤ s) :
    (d : ℝ) ≤ min (s ^ 2) (s * Real.sqrt (d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hdR : (0 : ℝ) ≤ d := hdpos.le
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt hdR
  have hnn : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  rw [le_min_iff]
  constructor
  · have h2 : Real.sqrt (d : ℝ) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ hnn hs 2
    rw [pow_two] at h2
    linarith [h2, hsq]
  · have hmul : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)
        ≤ s * Real.sqrt (d : ℝ) :=
      mul_le_mul_of_nonneg_right hs hnn
    linarith [hmul, hsq]

/-- Exp-tail monotonicity in the HW exponent. -/
theorem hw_exp_mono {cHW m D : Real} (hc : 0 < cHW) (h : D ≤ m) :
    2 * Real.exp (-cHW * m) ≤ 2 * Real.exp (-cHW * D) := by
  have h' : cHW * D ≤ cHW * m := mul_le_mul_of_nonneg_left h hc.le
  have hexp : Real.exp (-cHW * m) ≤ Real.exp (-cHW * D) := by
    apply Real.exp_le_exp.mpr
    linarith [h']
  exact mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- The `deletedLinf_union_tail` RHS at shifted level `s ≥ √d`
is dominated by `n·2exp(-cHW·d)`, beating `n ~ d²` rows. -/
theorem linf_union_beats_rows {d n : Nat} (hd : 1 ≤ d) {cHW s : Real}
    (hc : 0 < cHW) (hs : Real.sqrt (d : ℝ) ≤ s) :
    (n : ℝ) * (2 * Real.exp (-cHW * min (s ^ 2) (s * Real.sqrt (d : ℝ))))
      ≤ (n : ℝ) * (2 * Real.exp (-cHW * (d : ℝ))) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact hw_exp_mono hc (hw_min_ge_of_level hd hs)

/-- Level-choice wrapper in `deletedLinf_union_tail` form. -/
theorem linf_level_choice {d : Nat} (hd : 1 ≤ d) {T K : Real}
    (h : Real.sqrt (d : ℝ) + K ≤ T) :
    (d : ℝ) ≤ min ((T - K) ^ 2) ((T - K) * Real.sqrt (d : ℝ)) :=
  hw_min_ge_of_level hd (by linarith)

/-- Sup-norm level set is covered by coordinate level sets.
Used with `T := ε·η·√d` (the L∞ arm of `dualMixed`).
Needs `0 < n`: for `n = 0` and `T < 0` the inclusion is FALSE. -/
theorem sup_union_subset {X : Type*} {n : Nat} (hn : 0 < n)
    (e : X → (Fin n → ℝ)) (T : ℝ) :
    {x | T < ‖e x‖} ⊆ ⋃ j : Fin n, {x | T < |e x j|} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  by_contra hxU
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hxU
  rcases lt_or_ge T 0 with hneg | hT
  · have hj := hxU ⟨0, hn⟩
    have habs : (0 : ℝ) ≤ |e x ⟨0, hn⟩| := abs_nonneg _
    linarith [hj, habs, hneg]
  · have hle : ‖e x‖ ≤ T := by
      apply (pi_norm_le_iff_of_nonneg hT).mpr
      intro j
      have hj := hxU j
      rw [Real.norm_eq_abs]
      exact hj
    linarith [hx, hle]

end GaussianEllipsoid
/-! ### fin-master: BM-good shift instantiation for `huberResiduals_theorem`

Step "shift instantiation inline": on the BM-good event
(`bmMinRisk d n x lo hi 1 < ε'`), the deleted absolute-residual average
(the `ha` input of `deletedMeanShift_le`) is bounded by
`√(2R) + 2R` with `R = bmGoodR`, via `bmMinRisk_witness` +
`huber_le_rpow` at `r = 1` + `deleted_obj_le_bmWitness` +
`deleted_abs_le_of_huberAvg`. Combined with the covariance-good bound
(`matrixOpNorm (deletedCovariance x j - 1) ≤ C`), `onGood_shift_le`
gives the per-`x` shift bound the L2/L∞ arms consume on the good event.
-/

namespace GaussianEllipsoid

/-- BM-good radius: deleted Huber average bound on
`{bmMinRisk · lo hi 1 < ε'}`. -/
def bmGoodR (d n : Nat) (lo hi ε' : Real) : Real :=
  ((n : ℝ) / ((n : ℝ) - 1)) * ε'
    + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))

/-- On the BM-good event, the deleted Huber average is at most `bmGoodR`. -/
theorem bmGood_deletedHuberAvg_le {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) {lo hi ε' : Real} (hle : lo ≤ hi)
    {Sdel : Square d} (hDel : IsDeletedMinimizer lo hi x j Sdel)
    (hBM : bmMinRisk d n x lo hi 1 < ε') :
    (∑ i ∈ Finset.univ.erase j, huber (residual x Sdel i)) / ((n : ℝ) - 1)
      ≤ bmGoodR d n lo hi ε' := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  obtain ⟨Sbm, hSbm, hlt⟩ := bmMinRisk_witness x hn0 hle hBM
  have hHub : empiricalHuber (residual x Sbm) < ε' := by
    unfold empiricalHuber empiricalAverage
    simp only [Fintype.card_fin]
    have hsum : (∑ i, huber (residual x Sbm i)) / (n : ℝ)
        ≤ (∑ i, |residual x Sbm i| ^ (1 : ℝ)) / (n : ℝ) :=
      div_le_div_of_nonneg_right
        (Finset.sum_le_sum fun i _ =>
          huber_le_rpow le_rfl (by norm_num)) hnR.le
    have heq : (1 / (n : ℝ)) * (∑ i, |residual x Sbm i| ^ (1 : ℝ))
        = (∑ i, |residual x Sbm i| ^ (1 : ℝ)) / (n : ℝ) := by
      rw [mul_comm, mul_one_div]
    linarith [hsum, hlt, heq]
  have hobj := deleted_obj_le_bmWitness x j hn hDel hSbm
  have hR := ridgePenalty_le_of_mem_box hSbm
  have hRdel := ridgePenalty_nonneg (d := d) Sdel
  have havg : (∑ i ∈ Finset.univ.erase j, huber (residual x Sdel i))
      / ((n : ℝ) - 1) ≤ deletedHuberObjective x j Sdel := by
    unfold deletedHuberObjective
    linarith [hRdel]
  have hscale : ((n : ℝ) / ((n : ℝ) - 1))
      * empiricalHuber (residual x Sbm)
      < ((n : ℝ) / ((n : ℝ) - 1)) * ε' :=
    mul_lt_mul_of_pos_left hHub (div_pos hnR hn1)
  unfold bmGoodR
  linarith [havg, hobj, hR, hscale]

/-- On the BM-good event, the deleted absolute-residual average is at most
`√(2R) + 2R`. -/
theorem bmGood_deletedAbs_le {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) {lo hi ε' : Real} (hle : lo ≤ hi)
    {Sdel : Square d} (hDel : IsDeletedMinimizer lo hi x j Sdel)
    (hBM : bmMinRisk d n x lo hi 1 < ε') :
    (∑ i ∈ Finset.univ.erase j, |residual x Sdel i|) / ((n : ℝ) - 1)
      ≤ Real.sqrt (2 * bmGoodR d n lo hi ε')
        + 2 * bmGoodR d n lo hi ε' :=
  deleted_abs_le_of_huberAvg x j hn Sdel
    (bmGood_deletedHuberAvg_le x j hn hle hDel hBM)

/-- The `ha` side condition of `deletedMeanShift_le` on the BM-good event. -/
theorem bmGood_ha {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) {lo hi ε' : Real} (hle : lo ≤ hi)
    {Sdel : Square d} (hDel : IsDeletedMinimizer lo hi x j Sdel)
    (hBM : bmMinRisk d n x lo hi 1 < ε') :
    |(∑ i ∈ Finset.univ.erase j, residual x Sdel i) / ((n : ℝ) - 1)|
      ≤ Real.sqrt (2 * bmGoodR d n lo hi ε')
        + 2 * bmGoodR d n lo hi ε' := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h1n : (1 : ℝ) < n := by exact_mod_cast hn
    linarith
  have habs : |(∑ i ∈ Finset.univ.erase j, residual x Sdel i) / ((n : ℝ) - 1)|
      ≤ (∑ i ∈ Finset.univ.erase j, |residual x Sdel i|) / ((n : ℝ) - 1) := by
    rw [abs_div, abs_of_pos hn1]
    exact div_le_div_of_nonneg_right
      (Finset.abs_sum_le_sum_abs _ _) hn1.le
  exact le_trans habs
    (bmGood_deletedAbs_le x j hn hle hDel hBM)

/-- Combined on-good shift bound: covariance-good (`hC`) plus BM-good
(`hBM`) give `|shift| ≤ √d·hi·C + (√(2R) + 2R)` at `x`. -/
theorem onGood_shift_le {d n : Nat} (x : Sample d n) (j : Fin n)
    (hn : 1 < n) (hd : 0 < d) {lo hi : Real} (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    {Sdel : Square d} (hDel : IsDeletedMinimizer lo hi x j Sdel)
    {C ε' : Real}
    (hC : matrixOpNorm (deletedCovariance x j - 1) ≤ C)
    (hBM : bmMinRisk d n x lo hi 1 < ε') :
    |deletedMeanShift d Sdel|
      ≤ Real.sqrt (d : ℝ) * hi * C
        + (Real.sqrt (2 * bmGoodR d n lo hi ε')
          + 2 * bmGoodR d n lo hi ε') :=
  deletedMeanShift_le x j hn hd hlo hDel.1 hC
    (bmGood_ha x j hn hle hDel hBM)

end GaussianEllipsoid
/-! ### fin-master: scaled HW level arithmetic for the L∞ arm

`hw_min_ge_of_level` covers `s ≥ √d`, but the L∞ arm runs at level
`s = T/2 - e - K` with `T = ε·η·√d`, i.e. `s ≥ c·√d` for a fixed
`c = ε·η/4 > 0` eventually (deterministic error `e → 0`, shift `K`
fixed on the good event). The exponent `min (s²) (s√d)` is then at
least `min (c²) c · d`, still beating `n ~ d²` rows via
`GGlue.tendsto_n_mul_pow` with `ρ = exp (-cHW·min (c²) c) < 1`.
-/

namespace GaussianEllipsoid

/-- At scaled level `s ≥ c·√d` (`c > 0`), the Hanson–Wright exponent is
at least `min (c²) c · d`. -/
theorem hw_min_ge_of_scaled_level {d : Nat} (hd : 1 ≤ d) {s c : Real}
    (hc : 0 < c) (hs : c * Real.sqrt (d : ℝ) ≤ s) :
    min (c ^ 2) c * (d : ℝ)
      ≤ min (s ^ 2) (s * Real.sqrt (d : ℝ)) := by
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hdR : (0 : ℝ) ≤ d := hdpos.le
  have hsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt hdR
  have hsq2 : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR
  have hnn : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hcnn : (0 : ℝ) ≤ c * Real.sqrt (d : ℝ) :=
    mul_nonneg hc.le hnn
  rw [le_min_iff]
  constructor
  · calc min (c ^ 2) c * (d : ℝ)
        ≤ c ^ 2 * (d : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hdR
      _ = (c * Real.sqrt (d : ℝ)) ^ 2 := by
          rw [mul_pow, hsq2]
      _ ≤ s ^ 2 := pow_le_pow_left₀ hcnn hs 2
  · calc min (c ^ 2) c * (d : ℝ)
        ≤ c * (d : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hdR
      _ = c * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by rw [hsq]
      _ = c * Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) := by ring
      _ ≤ s * Real.sqrt (d : ℝ) :=
          mul_le_mul_of_nonneg_right hs hnn

/-- Scaled union-beats-rows: the HW union bound at level `s ≥ c√d` is
dominated by `n·2exp(-cHW·(min (c²) c · d))`. -/
theorem linf_union_beats_rows_general {d n : Nat} (hd : 1 ≤ d)
    {cHW s c : Real} (hcHW : 0 < cHW) (hc : 0 < c)
    (hs : c * Real.sqrt (d : ℝ) ≤ s) :
    (n : ℝ) * (2 * Real.exp (-cHW * min (s ^ 2) (s * Real.sqrt (d : ℝ))))
      ≤ (n : ℝ)
        * (2 * Real.exp (-cHW * (min (c ^ 2) c * (d : ℝ)))) := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact hw_exp_mono hcHW (hw_min_ge_of_scaled_level hd hc hs)

end GaussianEllipsoid
/-! ### fin2-glue: toReal union glue + sqrt-d*C(d) boundedness (fin §5 (a)+(b))

(a) `P(A∪B) ≤ P(A)+P(B)` for `gaussianSampleLaw` via
`measure_union_le` + `toReal_mono` + `toReal_add` (finiteness via
`measure_lt_top`); good/bad split `P(E) ≤ P(E∩good)+P(bad)`.
(b) `√d·C(d) → 4/√α₀` where `C(d)` is the `cov_good_tail_quarter`
threshold; main term via `tendsto_n_div_pred` + `tendsto_div_sqrt`,
vanishing pieces via `tendsto_sqrt_d_div_n` + `tendsto_d_div_pred`;
conclude `∀ᶠd, √d·C(d) ≤ 4/√α₀+1`.
-/

namespace GaussianEllipsoid

/-- Union bound in `toReal` for the sample law. -/
theorem gaussian_union_toReal_le {d n : Nat} (A B : Set (Sample d n)) :
    ((gaussianSampleLaw d n) (A ∪ B)).toReal
      ≤ ((gaussianSampleLaw d n) A).toReal + ((gaussianSampleLaw d n) B).toReal := by
  have hμ : (gaussianSampleLaw d n) (A ∪ B)
      ≤ (gaussianSampleLaw d n) A + (gaussianSampleLaw d n) B :=
    MeasureTheory.measure_union_le A B
  have hAfin : (gaussianSampleLaw d n) A ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  have hBfin : (gaussianSampleLaw d n) B ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  calc ((gaussianSampleLaw d n) (A ∪ B)).toReal
      ≤ ((gaussianSampleLaw d n) A + (gaussianSampleLaw d n) B).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) hμ
    _ = ((gaussianSampleLaw d n) A).toReal + ((gaussianSampleLaw d n) B).toReal :=
        ENNReal.toReal_add hAfin hBfin

/-- Good/bad split in `toReal`: `E ⊆ (E∩good) ∪ bad` gives the bound. -/
theorem gaussian_split_toReal_le {d n : Nat}
    (E good bad : Set (Sample d n)) (h : E ∩ goodᶜ ⊆ bad) :
    ((gaussianSampleLaw d n) E).toReal
      ≤ ((gaussianSampleLaw d n) (E ∩ good)).toReal
        + ((gaussianSampleLaw d n) bad).toReal := by
  have hsub : E ⊆ (E ∩ good) ∪ bad := by
    intro x hx
    simp only [Set.mem_union, Set.mem_inter_iff]
    by_cases hxg : x ∈ good
    · exact Or.inl ⟨hx, hxg⟩
    · exact Or.inr (h ⟨hx, hxg⟩)
  have hmono : (gaussianSampleLaw d n) E
      ≤ (gaussianSampleLaw d n) ((E ∩ good) ∪ bad) :=
    MeasureTheory.measure_mono hsub
  have hfin : (gaussianSampleLaw d n) ((E ∩ good) ∪ bad) ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  calc ((gaussianSampleLaw d n) E).toReal
      ≤ ((gaussianSampleLaw d n) ((E ∩ good) ∪ bad)).toReal :=
        ENNReal.toReal_mono hfin hmono
    _ ≤ ((gaussianSampleLaw d n) (E ∩ good)).toReal
          + ((gaussianSampleLaw d n) bad).toReal :=
        gaussian_union_toReal_le _ _

/-- Covariance-good threshold `C(d)` from `cov_good_tail_quarter`. -/
def covC (n : ℕ → ℕ) (d : ℕ) : ℝ :=
  (n d : ℝ) / ((n d : ℝ) - 1)
      * (4 * Real.sqrt ((d : ℝ) / (n d : ℝ)) + 4 * (d : ℝ) / (n d : ℝ))
    + (1 / ((n d : ℝ) - 1)) * (1 + 2 * (d : ℝ))

/-- `√d·C(d) → 4/√α₀`: main term `√d·(n/(n-1))·4√(d/n)` plus vanishing
pieces. -/
theorem tendsto_sqrt_mul_covC {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Filter.Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀)) :
    Filter.Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) * covC n d)
      Filter.atTop (nhds (4 / Real.sqrt α₀)) := by
  have hNdiv := GGlue.tendsto_n_div_pred hα hlim
  have hDsqrt := GGlue.tendsto_div_sqrt hα hn hlim
  have hSsqrt := GGlue.tendsto_sqrt_d_div_n hα hn hlim
  have hDpred := GGlue.tendsto_d_div_pred hα hn hlim
  have hgood := GGlue.eventually_good_index hα hn hlim
  have h4 : Filter.Tendsto (fun d : ℕ => 4 * ((d : ℝ) / Real.sqrt (n d : ℝ)))
      Filter.atTop (nhds (4 * (1 / Real.sqrt α₀))) :=
    Filter.Tendsto.const_mul 4 hDsqrt
  have hMain : Filter.Tendsto
      (fun d : ℕ => (n d : ℝ) / ((n d : ℝ) - 1)
        * (4 * ((d : ℝ) / Real.sqrt (n d : ℝ))))
      Filter.atTop (nhds (4 / Real.sqrt α₀)) := by
    have hmul := hNdiv.mul h4
    have heq : (1 : ℝ) * (4 * (1 / Real.sqrt α₀)) = 4 / Real.sqrt α₀ := by ring
    rw [heq] at hmul
    exact hmul
  have hP : Filter.Tendsto
      (fun d : ℕ => ((d : ℝ) / Real.sqrt (n d : ℝ))
        * Real.sqrt ((d : ℝ) / (n d : ℝ)))
      Filter.atTop (nhds 0) := by
    have hmul := hDsqrt.mul hSsqrt
    rw [mul_zero] at hmul
    exact hmul
  have hTU : Filter.Tendsto
      (fun d : ℕ => 6 * ((n d : ℝ) / ((n d : ℝ) - 1))
        * (((d : ℝ) / Real.sqrt (n d : ℝ))
          * Real.sqrt ((d : ℝ) / (n d : ℝ))))
      Filter.atTop (nhds 0) := by
    have h61 : Filter.Tendsto (fun d : ℕ => 6 * ((n d : ℝ) / ((n d : ℝ) - 1)))
        Filter.atTop (nhds (6 * 1)) :=
      Filter.Tendsto.const_mul 6 hNdiv
    have hmul := h61.mul hP
    rw [mul_zero] at hmul
    exact hmul
  have hV : Filter.Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) / ((n d : ℝ) - 1))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hDpred
    · filter_upwards [hgood] with d hd
      obtain ⟨_, hn1, _⟩ := hd
      have hpos : (0 : ℝ) < (n d : ℝ) - 1 := by
        have h1n : (1 : ℝ) < (n d : ℝ) := by exact_mod_cast hn1
        linarith
      exact div_nonneg (Real.sqrt_nonneg _) hpos.le
    · filter_upwards [hgood] with d hd
      obtain ⟨hd1, hn1, _⟩ := hd
      have hpos : (0 : ℝ) < (n d : ℝ) - 1 := by
        have h1n : (1 : ℝ) < (n d : ℝ) := by exact_mod_cast hn1
        linarith
      have hle : Real.sqrt (d : ℝ) ≤ (d : ℝ) := by
        have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
        have h1d : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
        have hsq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
          calc (d : ℝ) = (d : ℝ) * 1 := (mul_one _).symm
            _ ≤ (d : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_left h1d hdR
            _ = (d : ℝ) ^ 2 := (pow_two _).symm
        rw [Real.sqrt_le_iff]
        exact ⟨hdR, hsq⟩
      exact div_le_div_of_nonneg_right hle hpos.le
  have hSum : Filter.Tendsto
      (fun d : ℕ => (n d : ℝ) / ((n d : ℝ) - 1)
          * (4 * ((d : ℝ) / Real.sqrt (n d : ℝ)))
        + 6 * ((n d : ℝ) / ((n d : ℝ) - 1))
          * (((d : ℝ) / Real.sqrt (n d : ℝ))
            * Real.sqrt ((d : ℝ) / (n d : ℝ)))
        + Real.sqrt (d : ℝ) / ((n d : ℝ) - 1))
      Filter.atTop (nhds (4 / Real.sqrt α₀)) := by
    have hadd := (hMain.add hTU).add hV
    have heq : 4 / Real.sqrt α₀ + 0 + 0 = 4 / Real.sqrt α₀ := by ring
    rw [heq] at hadd
    exact hadd
  refine Filter.Tendsto.congr' ?_ hSum
  filter_upwards [hgood] with d hd
  obtain ⟨_, hn1, _⟩ := hd
  have hn0 : 0 < n d := by omega
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hnR : (0 : ℝ) < (n d : ℝ) := Nat.cast_pos.mpr hn0
  have h1n : (1 : ℝ) < (n d : ℝ) := by exact_mod_cast hn1
  have hpred : (0 : ℝ) < (n d : ℝ) - 1 := by linarith
  have hdiv : Real.sqrt ((d : ℝ) / (n d : ℝ))
      = Real.sqrt (d : ℝ) / Real.sqrt (n d : ℝ) :=
    Real.sqrt_div hdR _
  have hsqn2 : Real.sqrt (n d : ℝ) ^ 2 = (n d : ℝ) := Real.sq_sqrt hnR.le
  have hsqd2 : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt hdR
  have hne : Real.sqrt (n d : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnR)
  have hnen : (n d : ℝ) ≠ 0 := ne_of_gt hnR
  have hpred_ne : (n d : ℝ) - 1 ≠ 0 := ne_of_gt hpred
  show (n d : ℝ) / ((n d : ℝ) - 1) * (4 * ((d : ℝ) / Real.sqrt (n d : ℝ)))
      + 6 * ((n d : ℝ) / ((n d : ℝ) - 1))
        * (((d : ℝ) / Real.sqrt (n d : ℝ))
          * Real.sqrt ((d : ℝ) / (n d : ℝ)))
      + Real.sqrt (d : ℝ) / ((n d : ℝ) - 1)
    = Real.sqrt (d : ℝ) * covC n d
  unfold covC
  rw [hdiv]
  field_simp
  linear_combination (-4 * Real.sqrt (n d : ℝ) * (n d : ℝ)) * hsqd2
    + (-6 * Real.sqrt (d : ℝ) * (d : ℝ)) * hsqn2

/-- Eventual boundedness: `√d·C(d) ≤ 4/√α₀+1`. -/
theorem eventually_sqrt_mul_covC_le {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Filter.Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      Real.sqrt (d : ℝ) * covC n d ≤ 4 / Real.sqrt α₀ + 1 := by
  have hT := tendsto_sqrt_mul_covC hα hn hlim
  exact hT.eventually
    (eventually_le_nhds
      (show (4 / Real.sqrt α₀) < 4 / Real.sqrt α₀ + 1 by linarith))

end GaussianEllipsoid
/-! ### fin2-L2: closed L2 probability assembly for `huberResiduals_theorem`

Per-`(d, M, Kbar, epsp)` bound for the L2 arm of `l2_dualMixed_event_subset`.
Route: `l2_event_subset_tau` (via `l2_tau_of_euclid_gt`) → `l2_loo_split`;
bulk arm → BM-bad contrapositive (`l2_bulk_subset_bmBad` via
`l2_bulk_of_bmMinRisk`); deterministic `2e²` arm → empty (`l2_det_error_eq`);
tail arm → off-good mass plus on-good chaos events
(`l2_tail_onGood_subset_chaos` with shifts from `onGood_shift_le`) →
`chaosTailMean_markov` / `chaosIndMean_markov`, with the `hansonWrightChaos`
tails converted to `chaosZ` form by defeq (`l2_hw_chaosZ`).
-/

namespace GaussianEllipsoid

/-- `hansonWrightChaos`-output tails match `chaosZ` by definition
(`chaosZ` unfolds to exactly the displayed quadratic expression). -/
theorem l2_hw_chaosZ {d n : Nat} (Sdel : Fin n → Sample d n → Square d)
    {cHW : Real}
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |((quadratic ((Sdel j) x) (x j) - ((Sdel j) x).trace)
          / Real.sqrt (d : ℝ))|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ)))) :
    ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n) {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))) := by
  intro j t ht
  show ((gaussianSampleLaw d n)
      {x | t < |((quadratic ((Sdel j) x) (x j) - ((Sdel j) x).trace)
        / Real.sqrt (d : ℝ))|}).toReal
      ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ)))
  exact hHW j t ht

/-- toReal union bound (the `deletedCovariance_uniform_tail:1505-1524`
pattern, factored out). -/
theorem l2_toReal_union_le {d n : Nat} (A B : Set (Sample d n)) :
    ((gaussianSampleLaw d n) (A ∪ B)).toReal
      ≤ ((gaussianSampleLaw d n) A).toReal
        + ((gaussianSampleLaw d n) B).toReal := by
  have hA : (gaussianSampleLaw d n) A ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  have hB : (gaussianSampleLaw d n) B ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  calc ((gaussianSampleLaw d n) (A ∪ B)).toReal
      ≤ ((gaussianSampleLaw d n) A + (gaussianSampleLaw d n) B).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
          (MeasureTheory.measure_union_le A B)
    _ = ((gaussianSampleLaw d n) A).toReal
          + ((gaussianSampleLaw d n) B).toReal :=
        ENNReal.toReal_add hA hB

/-- Bulk contrapositive: when the BM-good bulk bound sits below `τ/3`,
a large bulk forces BM-bad (`l2_bulk_of_bmMinRisk` at `r = 1`). -/
theorem l2_bulk_subset_bmBad {d n : Nat} (hn : 0 < n)
    {lo hi epsp M tau : Real} (hle : lo ≤ hi) (hM : 0 < M)
    (Sstar : Sample d n → Square d)
    (hStar : ∀ x, IsHuberMinimizer lo hi x (Sstar x))
    (hbulk : 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
      ≤ tau / 3) :
    {x | tau / 3 ≤ 2 * M * empiricalHuber (residual x (Sstar x))}
      ⊆ {x | epsp ≤ bmMinRisk d n x lo hi 1} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  by_contra hcon
  have hgood : bmMinRisk d n x lo hi 1 < epsp := not_le.mp hcon
  have h := l2_bulk_of_bmMinRisk x hn hle (hStar x) (r := 1)
    le_rfl (by norm_num) hgood hM
  linarith [hx, h, hbulk]

/-- L2 event inclusion into bad sets plus on-good chaos events.
`hKle` instantiates `onGood_shift_le` uniformly (`Kbar` is `x`-free);
`hbulk` selects `ε'`; `hsmall`/`hdet` empty the deterministic arm. -/
theorem l2_event_subset_bad_chaos {d n : Nat} (hd : 1 ≤ d) (hn : 1 < n)
    {lo hi eps epsp C M Kbar T : Real}
    (he : 0 < eps) (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    (hK : 0 < Kbar) (hT : T = M / 2 - Kbar)
    (hM1 : 1 ≤ M)
    (hM : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M)
    (Sstar : Sample d n → Square d)
    (hStar : ∀ x, IsHuberMinimizer lo hi x (Sstar x))
    (Sdel : Fin n → Sample d n → Square d)
    (hDel : ∀ x j, IsDeletedMinimizer lo hi x j (Sdel j x))
    (hKle : Real.sqrt (d : ℝ) * hi * C
      + (Real.sqrt (2 * bmGoodR d n lo hi epsp)
        + 2 * bmGoodR d n lo hi epsp) ≤ Kbar)
    (hbulk : 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
      ≤ l2tau eps d n / 3)
    (hsmall : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) ≤ 1 / 2)
    (hdet : 2 * (|lo| + |hi| + 1) ^ 2 / (d : ℝ) < l2tau eps d n / 3) :
    {x | eps < euclidNorm (center (residual x (Sstar x))) / (d : ℝ)}
      ⊆ ({x | epsp ≤ bmMinRisk d n x lo hi 1}
        ∪ {x | ∃ j : Fin n, C < matrixOpNorm (deletedCovariance x j - 1)})
        ∪ ({x | l2tau eps d n / 6 / 4
            ≤ (∑ j, tailSquare (chaosZ (Sdel j) j x) T) / (n : ℝ)}
          ∪ {x | l2tau eps d n / 6 / (4 * Kbar ^ 2)
            ≤ (∑ j, (if T < |chaosZ (Sdel j) j x| then (1 : ℝ) else 0))
              / (n : ℝ)}) := by
  have hd0 : 0 < d := by omega
  have hn0 : 0 < n := by omega
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd0
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx
  have htau : l2tau eps d n
      ≤ (∑ j, (residual x (Sstar x) j) ^ 2) / (n : ℝ) :=
    l2_tau_of_euclid_gt hd0 hn0 he x (Sstar x) hx
  have hsplit := l2_loo_split x hn (hStar x) (fun j => Sdel j x)
    (fun j => hDel x j) hM1 hM htau
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  rcases hsplit with hbulk_mem | htail_mem | hdet_mem
  · exact Or.inl (Or.inl
      ((l2_bulk_subset_bmBad hn0 hle hMpos Sstar hStar hbulk) hbulk_mem))
  · have htail' : l2tau eps d n / 3 ≤ 2 *
        ((∑ j, tailSquare (residual x (Sdel j x) j) (M / 2)) / (n : ℝ)) :=
        htail_mem
    by_cases hBM : bmMinRisk d n x lo hi 1 < epsp
    · by_cases hCall : ∀ j : Fin n,
        matrixOpNorm (deletedCovariance x j - 1) ≤ C
      · have hμ : ∀ j : Fin n,
            |deletedMeanShift d (Sdel j x)| ≤ Kbar := fun j =>
          le_trans (onGood_shift_le x j hn hd0 hlo hle (hDel x j)
            (hCall j) hBM) hKle
        have hdelta : l2tau eps d n / 6
            ≤ (∑ j, tailSquare (residual x (Sdel j x) j) (M / 2))
              / (n : ℝ) := by linarith [htail']
        have hmem := l2_tail_onGood_subset_chaos hd Sdel
          (Kbar := Kbar) (M := M) (T := T)
          (delta := l2tau eps d n / 6) hT hK ⟨hμ, hdelta⟩
        simp only [Set.mem_union, Set.mem_ofPred_eq] at hmem
        exact Or.inr hmem
      · obtain ⟨j, hj⟩ := not_forall.mp hCall
        exact Or.inl (Or.inr ⟨j, not_le.mp hj⟩)
    · exact Or.inl (Or.inl (not_lt.mp hBM))
  · exfalso
    have hC0 : (0 : ℝ) ≤ (|lo| + |hi| + 1) ^ 2 := by positivity
    rw [l2_det_error_eq hdR hC0 hsmall] at hdet_mem
    linarith [hdet_mem, hdet]

/-- Closed per-`(d, M, Kbar, ε')` L2 probability bound: the L2 arm is at
most BM-bad mass plus covariance-bad mass plus the two chaos Markov
terms (fixed `T = M/2 - Kbar`). -/
theorem l2_prob_le {d n : Nat} (hd : 1 ≤ d) (hn : 1 < n)
    {lo hi eps epsp C M Kbar T cHW : Real}
    (he : 0 < eps) (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    (hK : 0 < Kbar) (hT : T = M / 2 - Kbar) (hTpos : 0 < T)
    (hcHW : 0 < cHW)
    (hM1 : 1 ≤ M)
    (hM : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M)
    (Sstar : Sample d n → Square d)
    (hStar : ∀ x, IsHuberMinimizer lo hi x (Sstar x))
    (Sdel : Fin n → Sample d n → Square d)
    (hSdel : ∀ j, Measurable (Sdel j))
    (hDel : ∀ x j, IsDeletedMinimizer lo hi x j (Sdel j x))
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |((quadratic ((Sdel j) x) (x j) - ((Sdel j) x).trace)
          / Real.sqrt (d : ℝ))|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    (hKle : Real.sqrt (d : ℝ) * hi * C
      + (Real.sqrt (2 * bmGoodR d n lo hi epsp)
        + 2 * bmGoodR d n lo hi epsp) ≤ Kbar)
    (hbulk : 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
      ≤ l2tau eps d n / 3)
    (hsmall : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) ≤ 1 / 2)
    (hdet : 2 * (|lo| + |hi| + 1) ^ 2 / (d : ℝ) < l2tau eps d n / 3) :
    ((gaussianSampleLaw d n)
      {x | eps < euclidNorm (center (residual x (Sstar x))) / (d : ℝ)}).toReal
      ≤ ((gaussianSampleLaw d n)
          {x | epsp ≤ bmMinRisk d n x lo hi 1}).toReal
        + ((gaussianSampleLaw d n)
          {x | ∃ j : Fin n, C < matrixOpNorm (deletedCovariance x j - 1)}).toReal
        + ((((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 2)
            / (l2tau eps d n / 6 / 4))
          + (((4 / cHW ^ 2 + 48 / cHW ^ 4) / T ^ 4)
            / (l2tau eps d n / 6 / (4 * Kbar ^ 2)))) := by
  have hd0 : 0 < d := by omega
  have hn0 : 0 < n := by omega
  have htau_pos : 0 < l2tau eps d n := l2tau_pos he hd0 hn0
  have htau6 : (0 : ℝ) < l2tau eps d n / 6 := by linarith
  have heps1 : (0 : ℝ) < l2tau eps d n / 6 / 4 := by linarith
  have hK2 : (0 : ℝ) < Kbar ^ 2 := pow_pos hK 2
  have hK2pos : (0 : ℝ) < 4 * Kbar ^ 2 := mul_pos (by norm_num) hK2
  have heps2 : (0 : ℝ) < l2tau eps d n / 6 / (4 * Kbar ^ 2) :=
    div_pos htau6 hK2pos
  have hHWz := l2_hw_chaosZ Sdel hHW
  have hTail := chaosTailMean_markov hd hn0 Sdel hSdel hcHW hHWz hTpos heps1
  have hInd := chaosIndMean_markov hd hn0 Sdel hSdel hcHW hHWz hTpos heps2
  have hsub := l2_event_subset_bad_chaos hd hn he hlo hle hK hT hM1 hM
    Sstar hStar Sdel hDel hKle hbulk hsmall hdet
  have hfin : (gaussianSampleLaw d n)
      (({x : Sample d n | epsp ≤ bmMinRisk d n x lo hi 1}
        ∪ {x | ∃ j : Fin n, C < matrixOpNorm (deletedCovariance x j - 1)})
        ∪ ({x : Sample d n | l2tau eps d n / 6 / 4
          ≤ (∑ j, tailSquare (chaosZ (Sdel j) j x) T) / (n : ℝ)}
        ∪ {x | l2tau eps d n / 6 / (4 * Kbar ^ 2)
          ≤ (∑ j, (if T < |chaosZ (Sdel j) j x| then (1 : ℝ) else 0))
            / (n : ℝ)})) ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  have h1 := ENNReal.toReal_mono hfin (MeasureTheory.measure_mono hsub)
  have h2 := l2_toReal_union_le
    ({x : Sample d n | epsp ≤ bmMinRisk d n x lo hi 1}
      ∪ {x | ∃ j : Fin n, C < matrixOpNorm (deletedCovariance x j - 1)})
    ({x : Sample d n | l2tau eps d n / 6 / 4
        ≤ (∑ j, tailSquare (chaosZ (Sdel j) j x) T) / (n : ℝ)}
      ∪ {x | l2tau eps d n / 6 / (4 * Kbar ^ 2)
        ≤ (∑ j, (if T < |chaosZ (Sdel j) j x| then (1 : ℝ) else 0))
          / (n : ℝ)})
  have h3 := l2_toReal_union_le
    {x : Sample d n | epsp ≤ bmMinRisk d n x lo hi 1}
    {x | ∃ j : Fin n, C < matrixOpNorm (deletedCovariance x j - 1)}
  have h4 := l2_toReal_union_le
    {x : Sample d n | l2tau eps d n / 6 / 4
      ≤ (∑ j, tailSquare (chaosZ (Sdel j) j x) T) / (n : ℝ)}
    {x | l2tau eps d n / 6 / (4 * Kbar ^ 2)
      ≤ (∑ j, (if T < |chaosZ (Sdel j) j x| then (1 : ℝ) else 0)) / (n : ℝ)}
  linarith [h1, h2, h3, h4, hTail, hInd]

end GaussianEllipsoid
/-! ### fin2-Linf: L∞ probability assembly for `huberResiduals_theorem` (task (d))

Closed per-`(d, c, K)` on-good bound at `T = eps*eta*√d`:
Linf arm → center (`center_pi_norm_le`) → sup union (`sup_union_subset`)
→ LOO (`loo_abs_comparison` + `full_deleted_sup_subset`)
→ on-good chaos (`linf_onGood_union_tail`, inlining the
`deletedLinf_union_tail` pattern restricted to `Good` — that lemma's
global `hμ` does NOT apply; shift bound holds only on `Good` via
`onGood_shift_le`) → scaled level (`linf_union_beats_rows_general`)
→ tendsto form (`GGlue.tendsto_n_mul_pow`).
-/

namespace GaussianEllipsoid

/-- L∞ arm: `eps < ‖center‖/(eta*√d)` forces `T < ‖center‖`
with `T = eps*eta*√d`. -/
theorem linf_arm_subset {d n : Nat} (hd : 1 ≤ d) {eta eps : Real}
    (hη : 0 < eta) (Sstar : Sample d n → Square d) :
    {x : Sample d n | eps
        < ‖center (residual x (Sstar x))‖ / (eta * Real.sqrt (d : ℝ))}
      ⊆ {x | eps * eta * Real.sqrt (d : ℝ)
        < ‖center (residual x (Sstar x))‖} := by
  have hdR : (0 : ℝ) < d := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd
  have hsq : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
  have hpos : (0 : ℝ) < eta * Real.sqrt (d : ℝ) := mul_pos hη hsq
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have h := (lt_div_iff₀ hpos).mp hx
  have heq : eps * (eta * Real.sqrt (d : ℝ))
      = eps * eta * Real.sqrt (d : ℝ) := by ring
  rw [heq] at h
  exact h

/-- Center bound as a set inclusion:
`{T < ‖center r‖} ⊆ {T/2 < ‖r‖}` via `center_pi_norm_le`. -/
theorem linf_center_subset {X : Type*} {n : Nat} (hn : 0 < n)
    (r : X → Vector n) (T : Real) :
    {x | T < ‖center (r x)‖} ⊆ {x | T / 2 < ‖r x‖} := by
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hle := center_pi_norm_le hn (r x)
  linarith [hx, hle]

/-- Per-`x` LOO row transfer via `full_deleted_sup_subset`
instantiated with `loo_abs_comparison`. -/
theorem linf_loo_row_subset {d n : Nat} (hn : 1 < n) {lo hi : Real}
    (x : Sample d n) {Sstar : Square d}
    (hStar : IsHuberMinimizer lo hi x Sstar)
    (Sdel : Fin n → Square d)
    (hDel : ∀ j, IsDeletedMinimizer lo hi x j (Sdel j)) (T2 : Real) :
    {j : Fin n | T2 < |residual x Sstar j|}
      ⊆ {j : Fin n | T2 - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
        < |residual x (Sdel j) j|} :=
  full_deleted_sup_subset (fun j => loo_abs_comparison x j hn hStar (hDel j))

/-- Union form over `x`: large full residuals force large deleted
residuals (via the per-`x` row inclusion above). -/
theorem linf_loo_union_subset {d n : Nat} (hn : 1 < n) {lo hi : Real}
    (Sstar : Sample d n → Square d)
    (hStar : ∀ x, IsHuberMinimizer lo hi x (Sstar x))
    (Sdel : Fin n → Sample d n → Square d)
    (hDel : ∀ j x, IsDeletedMinimizer lo hi x j (Sdel j x)) (T2 : Real) :
    (⋃ j : Fin n, {x : Sample d n | T2 < |residual x (Sstar x) j|})
      ⊆ ⋃ j : Fin n, {x : Sample d n |
        T2 - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
          < |residual x (Sdel j x) j|} := by
  intro x hx
  rw [Set.mem_iUnion] at hx ⊢
  obtain ⟨j, hj⟩ := hx
  have hrow := linf_loo_row_subset hn x (hStar x)
    (fun k => Sdel k x) (fun k => hDel k x) T2
  exact ⟨j, hrow hj⟩

/-- On-good shift bound from `onGood_shift_le`
(covariance-good `hC` plus BM-good `hBM` at `x`). -/
theorem linf_shift_on_good {d n : Nat} (hn : 1 < n) (hd : 0 < d)
    {lo hi C ε' : Real} (hlo : 0 ≤ lo) (hle : lo ≤ hi)
    (Sdel : Fin n → Sample d n → Square d)
    (hDel : ∀ j x, IsDeletedMinimizer lo hi x j (Sdel j x))
    (Good : Set (Sample d n))
    (hC : ∀ x ∈ Good, ∀ j : Fin n,
      matrixOpNorm (deletedCovariance x j - 1) ≤ C)
    (hBM : ∀ x ∈ Good, bmMinRisk d n x lo hi 1 < ε') :
    ∀ x ∈ Good, ∀ j : Fin n,
      |deletedMeanShift d (Sdel j x)|
        ≤ Real.sqrt (d : ℝ) * hi * C
          + (Real.sqrt (2 * bmGoodR d n lo hi ε')
            + 2 * bmGoodR d n lo hi ε') := by
  intro x hxG j
  exact onGood_shift_le x j hn hd hlo hle (hDel j x) (hC x hxG j) (hBM x hxG)

/-- On-good L∞ union tail: the `deletedLinf_union_tail` pattern (per-row
`hHW` chaos tails + union bound) restricted to `Good`. That lemma's
global `hμ` does NOT apply — the shift bound `K` holds only on `Good`
(discharged by `linf_shift_on_good`). -/
theorem linf_onGood_union_tail {d n : Nat} (hd : 1 ≤ d)
    (Sdel : Fin n → Sample d n → Square d)
    {cHW : Real}
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    {K Tlvl : Real} (hTK : 0 ≤ Tlvl - K)
    (Good : Set (Sample d n))
    (hμ : ∀ x ∈ Good, ∀ j : Fin n,
      |deletedMeanShift d (Sdel j x)| ≤ K) :
    ((gaussianSampleLaw d n)
      ((⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|}) ∩ Good)).toReal
      ≤ (n : ℝ) * (2 * Real.exp (-cHW
        * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
  have hbound_nn : (0 : ℝ) ≤ 2 * Real.exp (-cHW
      * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ))) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hsub : (⋃ j : Fin n,
        {x : Sample d n | Tlvl < |residual x (Sdel j x) j|}) ∩ Good
      ⊆ ⋃ j : Fin n, {x | Tlvl - K < |chaosZ (Sdel j) j x|} := by
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨⟨j, hj⟩, hxG⟩ := hx
    refine ⟨j, ?_⟩
    have hres := residual_eq_chaos_add_shift hd (Sdel j) j x
    have hab := abs_add_le
      (chaosZ (Sdel j) j x) (deletedMeanShift d (Sdel j x))
    have hμx := hμ x hxG j
    rw [hres] at hj
    linarith [hj, hab, hμx]
  have hEj : ∀ j : Fin n,
      (gaussianSampleLaw d n) {x | Tlvl - K < |chaosZ (Sdel j) j x|}
        ≤ ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
    intro j
    have hfin : (gaussianSampleLaw d n)
        {x | Tlvl - K < |chaosZ (Sdel j) j x|} ≠ ∞ :=
      (MeasureTheory.measure_lt_top _ _).ne
    calc (gaussianSampleLaw d n) {x | Tlvl - K < |chaosZ (Sdel j) j x|}
          = ENNReal.ofReal (((gaussianSampleLaw d n)
            {x | Tlvl - K < |chaosZ (Sdel j) j x|}).toReal) :=
            (ENNReal.ofReal_toReal hfin).symm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) :=
          ENNReal.ofReal_le_ofReal (hHW j (Tlvl - K) hTK)
  have hunion : (gaussianSampleLaw d n)
        (⋃ j : Fin n, {x | Tlvl - K < |chaosZ (Sdel j) j x|})
      ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)),
        ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
    have h1 : (gaussianSampleLaw d n)
          (⋃ j : Fin n, {x | Tlvl - K < |chaosZ (Sdel j) j x|})
        ≤ ∑' j : Fin n,
          (gaussianSampleLaw d n)
            {x | Tlvl - K < |chaosZ (Sdel j) j x|} :=
      MeasureTheory.measure_iUnion_le _
    rw [tsum_fintype] at h1
    exact le_trans h1 (Finset.sum_le_sum fun j _ => hEj j)
  have hfin : (∑ j ∈ (Finset.univ : Finset (Fin n)),
      ENNReal.ofReal (2 * Real.exp (-cHW
        * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ))))) ≠ ∞ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hbound_nn)]
    exact ENNReal.ofReal_ne_top
  have hmono : (gaussianSampleLaw d n)
        ((⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|}) ∩ Good)
      ≤ (gaussianSampleLaw d n)
        (⋃ j : Fin n, {x | Tlvl - K < |chaosZ (Sdel j) j x|}) :=
    MeasureTheory.measure_mono hsub
  have hchain : (gaussianSampleLaw d n)
        ((⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|}) ∩ Good)
      ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)),
        ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2) ((Tlvl - K) * Real.sqrt (d : ℝ)))) :=
    le_trans hmono hunion
  calc ((gaussianSampleLaw d n)
          ((⋃ j : Fin n, {x | Tlvl < |residual x (Sdel j x) j|}) ∩ Good)).toReal
      ≤ (∑ j ∈ (Finset.univ : Finset (Fin n)),
          ENNReal.ofReal (2 * Real.exp (-cHW
            * min ((Tlvl - K) ^ 2)
              ((Tlvl - K) * Real.sqrt (d : ℝ))))).toReal :=
        ENNReal.toReal_mono hfin hchain
    _ = ∑ j ∈ (Finset.univ : Finset (Fin n)),
        (ENNReal.ofReal (2 * Real.exp (-cHW
          * min ((Tlvl - K) ^ 2)
            ((Tlvl - K) * Real.sqrt (d : ℝ))))).toReal :=
        ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)
    _ = ∑ _j ∈ (Finset.univ : Finset (Fin n)),
        (2 * Real.exp (-cHW * min ((Tlvl - K) ^ 2)
          ((Tlvl - K) * Real.sqrt (d : ℝ)))) :=
        Finset.sum_congr rfl fun j _ =>
          ENNReal.toReal_ofReal hbound_nn
    _ = (n : ℝ) * (2 * Real.exp (-cHW * min ((Tlvl - K) ^ 2)
        ((Tlvl - K) * Real.sqrt (d : ℝ)))) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Closed per-`(d, c, K)` L∞ on-good bound at `T = eps*eta*√d`:
Linf arm → center (`center_pi_norm_le`) → sup union
(`sup_union_subset`) → LOO (`linf_loo_union_subset`) → on-good chaos
(`linf_onGood_union_tail`) → scaled level
(`linf_union_beats_rows_general`). The chaos level is
`s = T/2 - e - K` with `e → 0` deterministic; `hs` is the
`s ≥ c√d` eventual input from the final assembly. -/
theorem linf_good_event_le {d n : Nat} (hd : 1 ≤ d) (hn : 1 < n)
    {lo hi eta eps cHW K c : Real} (hη : 0 < eta)
    (hcHW : 0 < cHW) (hc : 0 < c)
    (Sstar : Sample d n → Square d)
    (hStar : ∀ x, IsHuberMinimizer lo hi x (Sstar x))
    (Sdel : Fin n → Sample d n → Square d)
    (hDel : ∀ j x, IsDeletedMinimizer lo hi x j (Sdel j x))
    (hHW : ∀ j : Fin n, ∀ t : Real, 0 ≤ t →
      ((gaussianSampleLaw d n)
        {x | t < |chaosZ (Sdel j) j x|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))))
    (Good : Set (Sample d n))
    (hμ : ∀ x ∈ Good, ∀ j : Fin n,
      |deletedMeanShift d (Sdel j x)| ≤ K)
    (hs : c * Real.sqrt (d : ℝ)
      ≤ (eps * eta * Real.sqrt (d : ℝ)) / 2
        - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) - K) :
    ((gaussianSampleLaw d n)
      ({x : Sample d n | eps
        < ‖center (residual x (Sstar x))‖ / (eta * Real.sqrt (d : ℝ))}
        ∩ Good)).toReal
      ≤ (n : ℝ)
        * (2 * Real.exp (-cHW * (min (c ^ 2) c * (d : ℝ)))) := by
  have hn0 : 0 < n := by omega
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hE1 := linf_arm_subset hd hη Sstar (eps := eps)
  have hE2 := linf_center_subset (X := Sample d n) hn0
    (fun x => residual x (Sstar x)) (eps * eta * Real.sqrt (d : ℝ))
  have hE3 := sup_union_subset hn0
    (fun x : Sample d n => residual x (Sstar x))
    ((eps * eta * Real.sqrt (d : ℝ)) / 2)
  have hE4 := linf_loo_union_subset hn Sstar hStar Sdel hDel
    ((eps * eta * Real.sqrt (d : ℝ)) / 2)
  have hcap : ({x : Sample d n | eps
          < ‖center (residual x (Sstar x))‖ / (eta * Real.sqrt (d : ℝ))}
        ∩ Good)
      ⊆ ((⋃ j : Fin n, {x : Sample d n |
          (eps * eta * Real.sqrt (d : ℝ)) / 2
            - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
            < |residual x (Sdel j x) j|}) ∩ Good) := by
    intro x hx
    constructor
    · apply hE4
      apply hE3
      apply hE2
      apply hE1
      exact hx.1
    · exact hx.2
  have hmono : (gaussianSampleLaw d n)
        ({x : Sample d n | eps
          < ‖center (residual x (Sstar x))‖ / (eta * Real.sqrt (d : ℝ))}
        ∩ Good)
      ≤ (gaussianSampleLaw d n)
        ((⋃ j : Fin n, {x : Sample d n |
          (eps * eta * Real.sqrt (d : ℝ)) / 2
            - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
            < |residual x (Sdel j x) j|}) ∩ Good) :=
    MeasureTheory.measure_mono hcap
  have hfin : (gaussianSampleLaw d n)
        ((⋃ j : Fin n, {x : Sample d n |
          (eps * eta * Real.sqrt (d : ℝ)) / 2
            - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
            < |residual x (Sdel j x) j|}) ∩ Good) ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  have hle := ENNReal.toReal_mono hfin hmono
  have hTK : 0 ≤ ((eps * eta * Real.sqrt (d : ℝ)) / 2
      - huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))) - K := by
    have h0 : (0 : ℝ) ≤ c * Real.sqrt (d : ℝ) :=
      mul_nonneg hc.le hsqnn
    linarith [hs, h0]
  have htail := linf_onGood_union_tail hd Sdel hHW hTK Good hμ
  have hbeat := linf_union_beats_rows_general (n := n) hd hcHW hc hs
  exact le_trans (le_trans hle htail) hbeat

/-- Tendsto form: `n·2exp(-cHW·min(c²,c)·d) → 0` as `2·(n·ρ^d)`
with `ρ = exp(-cHW·min(c²,c)) ∈ [0,1)`,
via `←Real.exp_nat_mul` + `GGlue.tendsto_n_mul_pow`. -/
theorem linf_tendsto_union_bound {nn : ℕ → ℕ} {α₀ cHW c : Real}
    (hlim : Filter.Tendsto (fun d : ℕ => (nn d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀))
    (hcHW : 0 < cHW) (hc : 0 < c) :
    Filter.Tendsto
      (fun d : ℕ => (nn d : ℝ)
        * (2 * Real.exp (-cHW * (min (c ^ 2) c * (d : ℝ)))))
      Filter.atTop (nhds 0) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by
    rw [pow_two]
    exact mul_pos hc hc
  have hmin : (0 : ℝ) < min (c ^ 2) c :=
    lt_min_iff.mpr ⟨hc2, hc⟩
  have hexp_neg : -cHW * min (c ^ 2) c < 0 := by
    have h := mul_pos hcHW hmin
    linarith [h]
  have hρ1 : Real.exp (-cHW * min (c ^ 2) c) < 1 :=
    Real.exp_lt_one_iff.mpr hexp_neg
  have hρ0 : (0 : ℝ) ≤ Real.exp (-cHW * min (c ^ 2) c) :=
    (Real.exp_pos _).le
  have hmain := GGlue.tendsto_n_mul_pow hlim hρ0 hρ1
  have hmul := hmain.const_mul 2
  rw [mul_zero] at hmul
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards with d
  show 2 * ((nn d : ℝ) * Real.exp (-cHW * min (c ^ 2) c) ^ d)
    = (nn d : ℝ) * (2 * Real.exp (-cHW * (min (c ^ 2) c * (d : ℝ))))
  have hexp : Real.exp (-cHW * (min (c ^ 2) c * (d : ℝ)))
      = Real.exp (-cHW * min (c ^ 2) c) ^ d := by
    have heq : -cHW * (min (c ^ 2) c * (d : ℝ))
        = (d : ℝ) * (-cHW * min (c ^ 2) c) := by ring
    rw [heq, Real.exp_nat_mul]
  rw [hexp]
  ring

end GaussianEllipsoid
/-! ### fin-final: `huberResiduals_theorem` assembly (fin §5 (e))

Final `∀ σ>0, ∀ᶠ d` assembly following fin-master §3 constant order.
Helpers: `l2tau` tendsto, `C/d` tendsto, `√d → ∞`, `huberInv` tendsto.
Main: `huberResiduals_theorem` with EXACT g-wire binder order.
-/

namespace GaussianEllipsoid

/-- `C/d → 0` for any fixed `C` (via `1/d → 0` + const_mul). -/
theorem fin_C_div_tendsto (C : ℝ) :
    Filter.Tendsto (fun d : ℕ => C / (d : ℝ)) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h2 := h1.const_mul C
  rw [mul_zero] at h2
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards [Filter.eventually_ge_atTop 1] with d hd
  have hd0 : (d : ℝ) ≠ 0 := by
    have hne : d ≠ 0 := by omega
    exact_mod_cast hne
  field_simp

/-- `l2tau eps d (n d) → eps^2/α₀` (via `d^2/n → α₀⁻¹` + const_mul). -/
theorem fin_l2tau_tendsto {n : ℕ → ℕ} {α₀ eps : ℝ} (hα : 0 < α₀)
    (hlim : Filter.Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀)) :
    Filter.Tendsto (fun d : ℕ => l2tau eps d (n d)) Filter.atTop
      (nhds (eps ^ 2 / α₀)) := by
  have hsq := GGlue.tendsto_sq_div_n hα hlim
  have hmul := hsq.const_mul (eps ^ 2)
  have heq : eps ^ 2 * α₀⁻¹ = eps ^ 2 / α₀ := by
    rw [div_eq_mul_inv]
  rw [heq] at hmul
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards with d
  unfold l2tau
  ring

/-- `√d → ∞` (via nat-cast atTop + sqrt atTop). -/
theorem fin_sqrt_atTop :
    Filter.Tendsto (fun d : ℕ => Real.sqrt (d : ℝ)) Filter.atTop Filter.atTop := by
  have hnat : Filter.Tendsto (fun d : ℕ => (d : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  exact Real.tendsto_sqrt_atTop.comp hnat

/-- `C0/(2d) → 0` for any fixed `C0` (via `C/d` + congr). -/
theorem fin_C_half_tendsto (C0 : ℝ) :
    Filter.Tendsto (fun d : ℕ => C0 / (2 * (d : ℝ))) Filter.atTop (nhds 0) := by
  have hgen := fin_C_div_tendsto (C0 / 2)
  refine Filter.Tendsto.congr' ?_ hgen
  filter_upwards [Filter.eventually_ge_atTop 1] with d hd
  have hd0 : (d : ℝ) ≠ 0 := by
    have hne : d ≠ 0 := by omega
    exact_mod_cast hne
  field_simp

/-- `huberInv(C0/(2d)) → 0` (eventually `= √(C0/d)` + sqrt tendsto). -/
theorem fin_huberInv_tendsto (C0 : ℝ) :
    Filter.Tendsto (fun d : ℕ => huberInv (C0 / (2 * (d : ℝ)))) Filter.atTop
      (nhds 0) := by
  have hC0d : Filter.Tendsto (fun d : ℕ => C0 / (d : ℝ)) Filter.atTop (nhds 0) :=
    fin_C_div_tendsto C0
  have hsqrt := hC0d.sqrt
  rw [Real.sqrt_zero] at hsqrt
  have hC0half : Filter.Tendsto (fun d : ℕ => C0 / (2 * (d : ℝ))) Filter.atTop
      (nhds 0) :=
    fin_C_half_tendsto C0
  have hsmall : ∀ᶠ d : ℕ in Filter.atTop, C0 / (2 * (d : ℝ)) ≤ 1 / 2 :=
    hC0half.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine Filter.Tendsto.congr' ?_ hsqrt
  filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with d hdsmall hd1
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd1
  have hclosed := l2_huberInv_closed hdR hdsmall (C := C0)
  rw [hclosed]

/-- Chaos tail term `M4/T^2/(τ/24) ≤ σ/8` from `T^2 ≥ 384*M4/(τ_inf*σ)`
and `τ ≥ τ_inf/2` (generic, to keep `nlinarith` out of the main `set` context). -/
theorem fin_chaos1_le (M4 T tau tau_inf σ : ℝ)
    (hT : 0 < T) (htau : 0 < tau)
    (htauinf : 0 < tau_inf) (hσ : 0 < σ)
    (hX1 : 384 * M4 / (tau_inf * σ) ≤ T ^ 2)
    (htau_ge : tau_inf / 2 ≤ tau) :
    ((M4 / T ^ 2) / (tau / 6 / 4)) ≤ σ / 8 := by
  have hT2 : 0 < T ^ 2 := pow_pos hT 2
  have hpos : 0 < tau_inf * σ := mul_pos htauinf hσ
  have h1 : 384 * M4 ≤ T ^ 2 * (tau_inf * σ) := by
    rwa [div_le_iff₀ hpos] at hX1
  have htau_le : tau_inf ≤ 2 * tau := by linarith [htau_ge]
  have hT2_ne : T ^ 2 ≠ 0 := ne_of_gt hT2
  have htau_ne : tau ≠ 0 := ne_of_gt htau
  have hT2s : 0 < T ^ 2 * σ := mul_pos hT2 hσ
  have h2tau : 0 ≤ 2 * tau - tau_inf := by linarith [htau_le]
  have hprod : 0 ≤ (2 * tau - tau_inf) * (T ^ 2 * σ) :=
    mul_nonneg h2tau hT2s.le
  field_simp
  nlinarith [h1, htau_le, hT2, htau, htauinf, hσ, hprod,
    mul_pos hT2 htau, mul_pos htauinf hσ, mul_pos hT2 hσ]

/-- Chaos indicator term `M4/T^4/(τ/(24*Kbar^2)) ≤ σ/8` (generic). -/
theorem fin_chaos2_le (M4 T tau tau_inf σ Kbar : ℝ)
    (hT : 0 < T) (htau : 0 < tau)
    (htauinf : 0 < tau_inf) (hσ : 0 < σ) (hK : 0 < Kbar)
    (hX2 : 384 * M4 * Kbar ^ 2 / (tau_inf * σ) ≤ T ^ 4)
    (htau_ge : tau_inf / 2 ≤ tau) :
    ((M4 / T ^ 4) / (tau / 6 / (4 * Kbar ^ 2))) ≤ σ / 8 := by
  have hT4 : 0 < T ^ 4 := pow_pos hT 4
  have hK2 : 0 < Kbar ^ 2 := pow_pos hK 2
  have hpos : 0 < tau_inf * σ := mul_pos htauinf hσ
  have h1 : 384 * M4 * Kbar ^ 2 ≤ T ^ 4 * (tau_inf * σ) := by
    rwa [div_le_iff₀ hpos] at hX2
  have htau_le : tau_inf ≤ 2 * tau := by linarith [htau_ge]
  have hT4_ne : T ^ 4 ≠ 0 := ne_of_gt hT4
  have htau_ne : tau ≠ 0 := ne_of_gt htau
  have hK2_ne : Kbar ^ 2 ≠ 0 := ne_of_gt hK2
  have hT4s : 0 < T ^ 4 * σ := mul_pos hT4 hσ
  have h2tau : 0 ≤ 2 * tau - tau_inf := by linarith [htau_le]
  have hprod : 0 ≤ (2 * tau - tau_inf) * (T ^ 4 * σ) :=
    mul_nonneg h2tau hT4s.le
  field_simp
  nlinarith [h1, htau_le, hT4, htau, htauinf, hσ, hK2, hprod,
    mul_pos hT4 htau, mul_pos htauinf hσ, mul_pos hT4 hσ]

end GaussianEllipsoid
/-! ### fin-final main: `huberResiduals_theorem` -/

namespace GaussianEllipsoid

/-- Section 4 conclusion (main-proposition-3-1) in dual-norm form:
the dual mixed norm of every Huber minimizer's centered residuals
tends to zero in probability. Conditional on the three Section 4
externals as `Prop` premises; `BMminRisk` threads through the
`HuberResiduals` binder `hBMmin` (supplied by `bmApproximateFitting`
at the assembly level). -/
theorem huberResiduals_theorem
    (hDS : davidsonSzarekCovariance)
    (hDel : deletedSelectorMeasurable)
    (hHW : hansonWrightChaos) : HuberResiduals := by
  intro n α₀ hn hconv hα0 hα4 lo hi hlo hlohi hBMmin Sstar hSspec η hη ε hε
  obtain ⟨cHW, hcHW, hHW_all⟩ := hHW lo hi hlo hlohi
  have hSel : ∀ d : ℕ, ∀ j : Fin (n d), ∃ Sdel : Sample d (n d) → Square d,
      Measurable Sdel ∧ (∀ x, IsDeletedMinimizer lo hi x j (Sdel x)) ∧
      ∀ x y : Sample d (n d), (∀ i, i ≠ j → x i = y i) → Sdel x = Sdel y :=
    fun d j => hDel d (n d) lo hi hlo hlohi j
  choose Sdel hSdel using hSel
  have hSdel_meas : ∀ d : ℕ, ∀ j : Fin (n d), Measurable (Sdel d j) :=
    fun d j => (hSdel d j).1
  have hSdel_min : ∀ d : ℕ, ∀ j : Fin (n d), ∀ x,
      IsDeletedMinimizer lo hi x j (Sdel d j x) :=
    fun d j x => (hSdel d j).2.1 x
  have hSdel_loc : ∀ d : ℕ, ∀ j : Fin (n d), ∀ x y : Sample d (n d),
      (∀ i, i ≠ j → x i = y i) → Sdel d j x = Sdel d j y :=
    fun d j x y h => (hSdel d j).2.2 x y h
  have hbox : ∀ d : ℕ, ∀ j : Fin (n d), ∀ x,
      Sdel d j x ∈ spectralBox d lo hi :=
    fun d j x => (hSdel_min d j x).1
  have hHW_raw : ∀ d : ℕ, ∀ j : Fin (n d), ∀ t : ℝ, 0 ≤ t →
      ((gaussianSampleLaw d (n d))
        {x | t < |((quadratic ((Sdel d j) x) (x j) - ((Sdel d j) x).trace)
          / Real.sqrt (d : ℝ))|}).toReal
        ≤ 2 * Real.exp (-cHW * min (t ^ 2) (t * Real.sqrt (d : ℝ))) := by
    intro d j t ht
    exact hHW_all d (n d) j (Sdel d j) (hSdel_meas d j) (hbox d j)
      (hSdel_loc d j) t ht
  apply GGlue.tendsto_zero_of_eventually_le
  · intro d
    exact ENNReal.toReal_nonneg
  · intro σ hσ
    -- Constants (fin-master §3 order)
    set C0 : ℝ := (|lo| + |hi| + 1) ^ 2 with hC0_def
    have hC0_nonneg : 0 ≤ C0 := by
      rw [hC0_def]
      positivity
    set tau_inf : ℝ := ε ^ 2 / α₀ with htauinf_def
    have htauinf_pos : 0 < tau_inf := by
      rw [htauinf_def]
      exact div_pos (pow_pos hε 2) hα0
    have hhi_pos : 0 < hi := lt_of_lt_of_le hlo hlohi
    have hsqrt_a0_pos : 0 < Real.sqrt α₀ := Real.sqrt_pos.mpr hα0
    set Kbar : ℝ := hi * (4 / Real.sqrt α₀ + 1) + (Real.sqrt 2 + 2) + 1 with hKbar_def
    have hKbar_pos : 0 < Kbar := by
      rw [hKbar_def]
      have h1 : 0 < (4 : ℝ) / Real.sqrt α₀ + 1 := by
        have hdiv : 0 < (4 : ℝ) / Real.sqrt α₀ :=
          div_pos (by norm_num) hsqrt_a0_pos
        linarith
      have h2 : 0 < hi * (4 / Real.sqrt α₀ + 1) := mul_pos hhi_pos h1
      have h3 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      linarith
    set M4 : ℝ := 4 / cHW ^ 2 + 48 / cHW ^ 4 with hM4_def
    have hM4_pos : 0 < M4 := by
      rw [hM4_def]
      have hc2 : 0 < cHW ^ 2 := pow_pos hcHW 2
      have hc4 : 0 < cHW ^ 4 := pow_pos hcHW 4
      have h1 : 0 < (4 : ℝ) / cHW ^ 2 := div_pos (by norm_num) hc2
      have h2 : 0 < (48 : ℝ) / cHW ^ 4 := div_pos (by norm_num) hc4
      linarith
    set X1 : ℝ := 384 * M4 / (tau_inf * σ) with hX1_def
    set X2 : ℝ := 384 * M4 * Kbar ^ 2 / (tau_inf * σ) with hX2_def
    have hX1_pos : 0 < X1 := by
      rw [hX1_def]
      exact div_pos (mul_pos (by norm_num) hM4_pos) (mul_pos htauinf_pos hσ)
    have hX2_pos : 0 < X2 := by
      rw [hX2_def]
      have hnum : 0 < 384 * M4 * Kbar ^ 2 := by
        have hk2 : 0 < Kbar ^ 2 := pow_pos hKbar_pos 2
        have h384 : 0 < (384 : ℝ) * M4 := mul_pos (by norm_num) hM4_pos
        exact mul_pos h384 hk2
      exact div_pos hnum (mul_pos htauinf_pos hσ)
    set Tneed : ℝ := max 1 (max X1 X2) with hTneed_def
    have hTneed_ge1 : 1 ≤ Tneed := by
      rw [hTneed_def]
      exact le_max_left _ _
    have hX1_le_Tneed : X1 ≤ Tneed := by
      rw [hTneed_def]
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    have hX2_le_Tneed : X2 ≤ Tneed := by
      rw [hTneed_def]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    set M : ℝ := 2 * Kbar + 2 * Tneed + 2 with hM_def
    have hM_pos : 0 < M := by
      rw [hM_def]
      linarith [hKbar_pos, hTneed_ge1]
    have hM1 : 1 ≤ M := by
      rw [hM_def]
      linarith [hKbar_pos, hTneed_ge1]
    set T : ℝ := M / 2 - Kbar with hT_def
    have hT_eq : T = M / 2 - Kbar := rfl
    have hT_val : T = Tneed + 1 := by
      rw [hT_def, hM_def]
      ring
    have hTpos : 0 < T := by
      rw [hT_val]
      linarith [hTneed_ge1]
    have hT_ge1 : 1 ≤ T := by
      rw [hT_val]
      linarith [hTneed_ge1]
    have hT_ge_X1 : X1 ≤ T := by
      rw [hT_val]
      have hle : Tneed ≤ Tneed + 1 := by linarith
      exact le_trans hX1_le_Tneed hle
    have hT_ge_X2 : X2 ≤ T := by
      rw [hT_val]
      have hle : Tneed ≤ Tneed + 1 := by linarith
      exact le_trans hX2_le_Tneed hle
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    set epsp : ℝ := min (1 / 2) (tau_inf / (24 * M)) with hepsp_def
    have h24M_pos : 0 < (24 : ℝ) * M := mul_pos (by norm_num) hM_pos
    have htauM_pos : 0 < tau_inf / (24 * M) := div_pos htauinf_pos h24M_pos
    have hepsp_pos : 0 < epsp := by
      rw [hepsp_def]
      exact lt_min_iff.mpr ⟨by norm_num, htauM_pos⟩
    have hepsp_le_half : epsp ≤ 1 / 2 := by
      rw [hepsp_def]
      exact min_le_left _ _
    have hepsp_le_tau : epsp ≤ tau_inf / (24 * M) := by
      rw [hepsp_def]
      exact min_le_right _ _
    set cLinf : ℝ := ε * η / 4 with hcLinf_def
    have hcLinf_pos : 0 < cLinf := by
      rw [hcLinf_def]
      exact div_pos (mul_pos hε hη) (by norm_num)
    -- Tendstos and eventuals
    have h_tau_tendsto : Filter.Tendsto (fun d : ℕ => l2tau ε d (n d))
        Filter.atTop (nhds tau_inf) :=
      fin_l2tau_tendsto hα0 hconv
    have h_tau_ge : ∀ᶠ d : ℕ in Filter.atTop, tau_inf / 2 ≤ l2tau ε d (n d) :=
      h_tau_tendsto.eventually
        (eventually_ge_nhds (by linarith [htauinf_pos] : tau_inf / 2 < tau_inf))
    have h_good_idx := GGlue.eventually_good_index hα0 hn hconv
    have h_sqrt_cov := eventually_sqrt_mul_covC_le hα0 hn hconv
    have h_n_div_tendsto := GGlue.tendsto_n_div_pred hα0 hconv
    have h_n_div_le : ∀ᶠ d : ℕ in Filter.atTop,
        (n d : ℝ) / ((n d : ℝ) - 1) ≤ 3 / 2 :=
      h_n_div_tendsto.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 3 / 2))
    have hC0half_tendsto := fin_C_half_tendsto C0
    have h_C0_quarter : ∀ᶠ d : ℕ in Filter.atTop, C0 / (2 * (d : ℝ)) ≤ 1 / 4 :=
      hC0half_tendsto.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
    have h_C0_tau : ∀ᶠ d : ℕ in Filter.atTop,
        C0 / (2 * (d : ℝ)) ≤ tau_inf / (24 * M) :=
      hC0half_tendsto.eventually (eventually_le_nhds htauM_pos)
    have h_2C0_tendsto : Filter.Tendsto (fun d : ℕ => 2 * C0 / (d : ℝ))
        Filter.atTop (nhds 0) := by
      have hgen := fin_C_div_tendsto (2 * C0)
      refine Filter.Tendsto.congr' ?_ hgen
      filter_upwards with d
      ring
    have htau12_pos : 0 < tau_inf / 12 := div_pos htauinf_pos (by norm_num)
    have h_2C0_le : ∀ᶠ d : ℕ in Filter.atTop, 2 * C0 / (d : ℝ) ≤ tau_inf / 12 :=
      h_2C0_tendsto.eventually (eventually_le_nhds htau12_pos)
    have h_e_tendsto := fin_huberInv_tendsto C0
    have h_e_le1 : ∀ᶠ d : ℕ in Filter.atTop,
        huberInv (C0 / (2 * (d : ℝ))) ≤ 1 :=
      h_e_tendsto.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
    have h_2e_tendsto := h_e_tendsto.const_mul 2
    rw [mul_zero] at h_2e_tendsto
    have h_2e_leM : ∀ᶠ d : ℕ in Filter.atTop,
        2 * huberInv (C0 / (2 * (d : ℝ))) ≤ M :=
      h_2e_tendsto.eventually (eventually_le_nhds hM_pos)
    have h_union_tendsto := linf_tendsto_union_bound hconv hcHW hcLinf_pos
    have hσ8_pos : 0 < σ / 8 := div_pos hσ (by norm_num)
    have h_union_le : ∀ᶠ d : ℕ in Filter.atTop,
        (n d : ℝ) * (2 * Real.exp (-cHW * (min (cLinf ^ 2) cLinf * (d : ℝ))))
          ≤ σ / 8 :=
      h_union_tendsto.eventually (eventually_le_nhds hσ8_pos)
    have hepsp_half_pos : 0 < epsp / 2 := div_pos hepsp_pos (by norm_num)
    have h_bm_tendsto := bm_good_event hBMmin hepsp_half_pos
    have h_bm_le : ∀ᶠ d : ℕ in Filter.atTop,
        ((gaussianSampleLaw d (n d))
          {x | epsp / 2 < bmMinRisk d (n d) x lo hi 1}).toReal ≤ σ / 8 :=
      h_bm_tendsto.eventually (eventually_le_nhds hσ8_pos)
    have h_cov_first := GGlue.tendsto_two_mul_exp_neg_half
    have h_cov_second := GGlue.tendsto_chi_union hα0 hn hconv
    have h_cov_tendsto := h_cov_first.add h_cov_second
    rw [add_zero] at h_cov_tendsto
    have h_cov_le : ∀ᶠ d : ℕ in Filter.atTop,
        (2 * Real.exp (-(d : ℝ) / 2) + (n d : ℝ) *
          (Real.exp (-(1 / 4) * (2 * (d : ℝ))) *
            (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d)) ≤ σ / 8 :=
      h_cov_tendsto.eventually (eventually_le_nhds hσ8_pos)
    have heta4_pos : 0 < ε * η / 4 := div_pos (mul_pos hε hη) (by norm_num)
    have h_sqrt_mul_atTop : Filter.Tendsto (fun d : ℕ => (ε * η / 4) * Real.sqrt (d : ℝ))
        Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop heta4_pos fin_sqrt_atTop
    have h_hs_ge : ∀ᶠ d : ℕ in Filter.atTop,
        1 + Kbar ≤ (ε * η / 4) * Real.sqrt (d : ℝ) :=
      h_sqrt_mul_atTop.eventually (Filter.eventually_ge_atTop (1 + Kbar))
    filter_upwards [h_good_idx, h_sqrt_cov, h_tau_ge, h_n_div_le, h_C0_quarter,
      h_C0_tau, h_2C0_le, h_e_le1, h_2e_leM, h_union_le, h_bm_le, h_cov_le,
      h_hs_ge] with d hd_good hd_sqrt hd_tau hd_ndiv hd_C0q hd_C0tau hd_2C0
      hd_e1 hd_2e hd_union hd_bm hd_cov hd_hs
    obtain ⟨hd1, hn1, hdn⟩ := hd_good
    have hd0 : 0 < d := by omega
    have hn0 : 0 < n d := by omega
    have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd0
    have hnR : (0 : ℝ) < (n d : ℝ) := Nat.cast_pos.mpr hn0
    have hC0q_exp : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) ≤ 1 / 4 := by
      have h := hd_C0q
      rwa [hC0_def] at h
    have hC0tau_exp : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) ≤ tau_inf / (24 * M) := by
      have h := hd_C0tau
      rwa [hC0_def] at h
    have h2C0_exp : 2 * (|lo| + |hi| + 1) ^ 2 / (d : ℝ) ≤ tau_inf / 12 := by
      have h := hd_2C0
      have heq : (2 : ℝ) * C0 / (d : ℝ) = 2 * (|lo| + |hi| + 1) ^ 2 / (d : ℝ) := by
        rw [hC0_def]
      rwa [heq] at h
    have he1_exp : huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ 1 := by
      have h := hd_e1
      rwa [hC0_def] at h
    have h2e_exp : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M := by
      have h := hd_2e
      rwa [hC0_def] at h
    have hsmall : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) ≤ 1 / 2 := by
      linarith [hC0q_exp]
    have hM_loo : 2 * huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) ≤ M :=
      h2e_exp
    have hR_le1 : bmGoodR d (n d) lo hi epsp ≤ 1 := by
      unfold bmGoodR
      have hepsp_nn : 0 ≤ epsp := le_of_lt hepsp_pos
      have h1 : ((n d : ℝ) / ((n d : ℝ) - 1)) * epsp ≤ (3 / 2) * epsp :=
        mul_le_mul_of_nonneg_right hd_ndiv hepsp_nn
      have h2 : (3 / 2 : ℝ) * epsp ≤ 3 / 4 := by
        have h3 : (3 / 2 : ℝ) * epsp ≤ (3 / 2) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hepsp_le_half (by norm_num)
        linarith [h3]
      have hC0_le : (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) ≤ 1 / 4 := hC0q_exp
      linarith [h1, h2, hC0_le]
    have hR_nn : 0 ≤ bmGoodR d (n d) lo hi epsp := by
      unfold bmGoodR
      have hn1R : (1 : ℝ) < (n d : ℝ) := by exact_mod_cast hn1
      have hpos : 0 < (n d : ℝ) / ((n d : ℝ) - 1) := by
        apply div_pos hnR
        linarith
      have h1 : 0 ≤ ((n d : ℝ) / ((n d : ℝ) - 1)) * epsp :=
        mul_nonneg hpos.le (le_of_lt hepsp_pos)
      have h2 : 0 ≤ (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)) := by
        apply div_nonneg (sq_nonneg _)
        linarith [hdR]
      linarith [h1, h2]
    have hKle : Real.sqrt (d : ℝ) * hi * covC n d +
        (Real.sqrt (2 * bmGoodR d (n d) lo hi epsp) +
          2 * bmGoodR d (n d) lo hi epsp) ≤ Kbar := by
      have hsqrt_le : Real.sqrt (d : ℝ) * covC n d ≤ 4 / Real.sqrt α₀ + 1 :=
        hd_sqrt
      have hhi_nn : 0 ≤ hi := le_of_lt hhi_pos
      have hmain : Real.sqrt (d : ℝ) * hi * covC n d ≤ hi * (4 / Real.sqrt α₀ + 1) := by
        have heq : Real.sqrt (d : ℝ) * hi * covC n d =
            hi * (Real.sqrt (d : ℝ) * covC n d) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left hsqrt_le hhi_nn
      have h2R_le : 2 * bmGoodR d (n d) lo hi epsp ≤ 2 := by
        linarith [hR_le1]
      have hsqrt_le2 : Real.sqrt (2 * bmGoodR d (n d) lo hi epsp) ≤ Real.sqrt 2 :=
        Real.sqrt_le_sqrt h2R_le
      have h2R_le2 : 2 * bmGoodR d (n d) lo hi epsp ≤ 2 := h2R_le
      have hsecond : Real.sqrt (2 * bmGoodR d (n d) lo hi epsp) +
          2 * bmGoodR d (n d) lo hi epsp ≤ Real.sqrt 2 + 2 :=
        add_le_add hsqrt_le2 h2R_le2
      rw [hKbar_def]
      linarith [hmain, hsecond]
    have htau_pos : 0 < l2tau ε d (n d) := l2tau_pos hε hd0 hn0
    have hbulk : 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
        ≤ l2tau ε d (n d) / 3 := by
      have h1 : epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))
          ≤ tau_inf / (24 * M) + tau_inf / (24 * M) :=
        add_le_add hepsp_le_tau hC0tau_exp
      have h2 : tau_inf / (24 * M) + tau_inf / (24 * M) = tau_inf / (12 * M) := by
        field_simp
        ring
      have h3 : 2 * M * (tau_inf / (12 * M)) = tau_inf / 6 := by
        field_simp
        ring
      have h4 : 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
          ≤ tau_inf / 6 := by
        have hle : 2 * M * (epsp + (|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ)))
            ≤ 2 * M * (tau_inf / (12 * M)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith [hM_pos] : (0 : ℝ) ≤ 2 * M)
          linarith [h1, h2]
        linarith [hle, h3]
      have h5 : tau_inf / 6 ≤ l2tau ε d (n d) / 3 := by
        linarith [hd_tau]
      linarith [h4, h5]
    have hdet : 2 * (|lo| + |hi| + 1) ^ 2 / (d : ℝ) < l2tau ε d (n d) / 3 := by
      have h1 : tau_inf / 12 < tau_inf / 6 := by linarith [htauinf_pos]
      have h2 : tau_inf / 6 ≤ l2tau ε d (n d) / 3 := by linarith [hd_tau]
      have h3 : tau_inf / 12 < l2tau ε d (n d) / 3 := lt_of_lt_of_le h1 h2
      have h4 : 2 * (|lo| + |hi| + 1) ^ 2 / (d : ℝ) ≤ tau_inf / 12 := h2C0_exp
      exact lt_of_le_of_lt h4 h3
    -- L2 arm via l2_prob_le
    have hL2 := l2_prob_le hd1 hn1 hε (le_of_lt hlo) hlohi hKbar_pos hT_eq hTpos
      hcHW hM1 hM_loo (Sstar d) (hSspec d) (Sdel d) (hSdel_meas d)
      (fun x j => hSdel_min d j x) (hHW_raw d) hKle hbulk hsmall hdet
    have hbm_subset : {x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1}
        ⊆ {x | epsp / 2 < bmMinRisk d (n d) x lo hi 1} := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      have hhalf : epsp / 2 < epsp := by linarith [hepsp_pos]
      exact lt_of_lt_of_le hhalf hx
    have hbm_mono : (gaussianSampleLaw d (n d))
          {x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1}
        ≤ (gaussianSampleLaw d (n d))
          {x | epsp / 2 < bmMinRisk d (n d) x lo hi 1} :=
      MeasureTheory.measure_mono hbm_subset
    have hbm_fin : (gaussianSampleLaw d (n d))
          {x : Sample d (n d) | epsp / 2 < bmMinRisk d (n d) x lo hi 1} ≠ ∞ :=
      (MeasureTheory.measure_lt_top _ _).ne
    have hbm_toReal : ((gaussianSampleLaw d (n d))
          {x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1}).toReal
        ≤ ((gaussianSampleLaw d (n d))
          {x | epsp / 2 < bmMinRisk d (n d) x lo hi 1}).toReal :=
      ENNReal.toReal_mono hbm_fin hbm_mono
    have hbm_le8 : ((gaussianSampleLaw d (n d))
          {x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1}).toReal
        ≤ σ / 8 :=
      le_trans hbm_toReal hd_bm
    have hcov_bound : ((gaussianSampleLaw d (n d))
          {x | ∃ j : Fin (n d), covC n d <
            matrixOpNorm (deletedCovariance x j - 1)}).toReal
        ≤ 2 * Real.exp (-(d : ℝ) / 2) + (n d : ℝ) *
          (Real.exp (-(1 / 4) * (2 * (d : ℝ))) *
            (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d) :=
      cov_good_tail_quarter hd0 hn1 hdn hDS
    have hcov_le8 : ((gaussianSampleLaw d (n d))
          {x | ∃ j : Fin (n d), covC n d <
            matrixOpNorm (deletedCovariance x j - 1)}).toReal ≤ σ / 8 :=
      le_trans hcov_bound hd_cov
    have hT_sq_ge : T ≤ T ^ 2 := by
      calc T = T * 1 := (mul_one _).symm
        _ ≤ T * T := mul_le_mul_of_nonneg_left hT_ge1 hTpos.le
        _ = T ^ 2 := (pow_two _).symm
    have hT2_ge1 : (1 : ℝ) ≤ T ^ 2 := by
      calc (1 : ℝ) = 1 ^ 2 := (one_pow _).symm
        _ ≤ T ^ 2 := pow_le_pow_left₀ (by norm_num) hT_ge1 2
    have hT24_le : T ^ 2 ≤ T ^ 4 := by
      have h1 : T ^ 2 * 1 ≤ T ^ 2 * T ^ 2 :=
        mul_le_mul_of_nonneg_left hT2_ge1 (sq_nonneg _)
      have h2 : T ^ 2 * T ^ 2 = T ^ 4 := by
        rw [← pow_add]
      have h3 : T ^ 2 * 1 = T ^ 2 := mul_one _
      linarith [h1, h2, h3]
    have hT_le_T4 : T ≤ T ^ 4 := le_trans hT_sq_ge hT24_le
    have hX1_le_T2 : X1 ≤ T ^ 2 := le_trans hT_ge_X1 hT_sq_ge
    have hX2_le_T4 : X2 ≤ T ^ 4 := le_trans hT_ge_X2 hT_le_T4
    rw [← hM4_def] at hL2
    rw [hX1_def] at hX1_le_T2
    rw [hX2_def] at hX2_le_T4
    have hterm1 : ((M4 / T ^ 2) / (l2tau ε d (n d) / 6 / 4)) ≤ σ / 8 :=
      fin_chaos1_le M4 T (l2tau ε d (n d)) tau_inf σ hTpos htau_pos
        htauinf_pos hσ hX1_le_T2 hd_tau
    have hterm2 : ((M4 / T ^ 4) / (l2tau ε d (n d) / 6 / (4 * Kbar ^ 2)))
        ≤ σ / 8 :=
      fin_chaos2_le M4 T (l2tau ε d (n d)) tau_inf σ Kbar hTpos htau_pos
        htauinf_pos hσ hKbar_pos hX2_le_T4 hd_tau
    have hL2_le : ((gaussianSampleLaw d (n d))
          {x | ε < euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)}).toReal
        ≤ σ / 2 := by
      linarith [hL2, hbm_le8, hcov_le8, hterm1, hterm2]
    -- Linf arm via linf_good_event_le
    set Good : Set (Sample d (n d)) :=
      {x | bmMinRisk d (n d) x lo hi 1 < epsp} ∩
      {x | ∀ j : Fin (n d), matrixOpNorm (deletedCovariance x j - 1) ≤ covC n d}
      with hGood_def
    have hC : ∀ x ∈ Good, ∀ j : Fin (n d),
        matrixOpNorm (deletedCovariance x j - 1) ≤ covC n d := by
      intro x hxG j
      have h := hxG.2
      exact h j
    have hBM : ∀ x ∈ Good, bmMinRisk d (n d) x lo hi 1 < epsp := by
      intro x hxG
      exact hxG.1
    have hshift := linf_shift_on_good hn1 hd0 (le_of_lt hlo) hlohi (Sdel d)
      (fun j x => hSdel_min d j x) Good hC hBM
    have hμ : ∀ x ∈ Good, ∀ j : Fin (n d),
        |deletedMeanShift d (Sdel d j x)| ≤ Kbar := by
      intro x hxG j
      exact le_trans (hshift x hxG j) hKle
    have h1_hs : huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) + Kbar
        ≤ (ε * η / 4) * Real.sqrt (d : ℝ) := by
      linarith [he1_exp, hd_hs]
    have heq1_hs : cLinf * Real.sqrt (d : ℝ)
        = (ε * η / 4) * Real.sqrt (d : ℝ) := by
      rw [hcLinf_def]
    have heq2_hs : (ε * η * Real.sqrt (d : ℝ)) / 2
        = 2 * ((ε * η / 4) * Real.sqrt (d : ℝ)) := by
      ring
    have hs : cLinf * Real.sqrt (d : ℝ)
        ≤ (ε * η * Real.sqrt (d : ℝ)) / 2 -
          huberInv ((|lo| + |hi| + 1) ^ 2 / (2 * (d : ℝ))) - Kbar := by
      linarith [h1_hs, heq1_hs, heq2_hs]
    have hHW_z := l2_hw_chaosZ (Sdel d) (hHW_raw d)
    have hLinf_good := linf_good_event_le hd1 hn1 hη hcHW hcLinf_pos (Sstar d)
      (hSspec d) (Sdel d) (fun j x => hSdel_min d j x) hHW_z Good hμ hs
    have hLinf_good_le8 : ((gaussianSampleLaw d (n d))
          ({x : Sample d (n d) | ε <
            ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}
          ∩ Good)).toReal ≤ σ / 8 :=
      le_trans hLinf_good hd_union
    have hsplit_subset : ({x : Sample d (n d) | ε <
            ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}
          ∩ Goodᶜ)
        ⊆ ({x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1} ∪
          {x | ∃ j : Fin (n d), covC n d <
            matrixOpNorm (deletedCovariance x j - 1)}) := by
      intro x hx
      simp only [hGood_def, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_union, Set.mem_ofPred_eq] at hx ⊢
      obtain ⟨_, hxG⟩ := hx
      by_cases hleft : bmMinRisk d (n d) x lo hi 1 < epsp
      · have hnot : ¬∀ j : Fin (n d),
            matrixOpNorm (deletedCovariance x j - 1) ≤ covC n d := by
          intro hall
          exact hxG ⟨hleft, hall⟩
        obtain ⟨j, hj⟩ := not_forall.mp hnot
        exact Or.inr ⟨j, not_le.mp hj⟩
      · exact Or.inl (not_lt.mp hleft)
    have hLinf_split := gaussian_split_toReal_le
      ({x : Sample d (n d) | ε <
        ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))})
      Good
      ({x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1} ∪
        {x | ∃ j : Fin (n d), covC n d <
          matrixOpNorm (deletedCovariance x j - 1)})
      hsplit_subset
    have hbad_le := gaussian_union_toReal_le
      ({x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1})
      ({x : Sample d (n d) | ∃ j : Fin (n d), covC n d <
        matrixOpNorm (deletedCovariance x j - 1)})
    have hLinf_le : ((gaussianSampleLaw d (n d))
          {x : Sample d (n d) | ε <
            ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}).toReal
        ≤ 3 * σ / 8 := by
      linarith [hLinf_split, hLinf_good_le8, hbad_le, hbm_le8, hcov_le8]
    have hdual_subset : {x : Sample d (n d) | ε <
          dualMixed η d (n d) (center (residual x (Sstar d x)))}
        ⊆ {x : Sample d (n d) | ε <
            ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}
          ∪ {x : Sample d (n d) | ε <
            euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)} :=
      l2_dualMixed_event_subset (Sstar d)
    have hdual_mono : (gaussianSampleLaw d (n d))
          {x : Sample d (n d) | ε <
            dualMixed η d (n d) (center (residual x (Sstar d x)))}
        ≤ (gaussianSampleLaw d (n d))
          ({x : Sample d (n d) | ε <
              ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}
            ∪ {x : Sample d (n d) | ε <
              euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)}) :=
      MeasureTheory.measure_mono hdual_subset
    have hdual_fin : (gaussianSampleLaw d (n d))
          ({x : Sample d (n d) | ε <
              ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}
            ∪ {x : Sample d (n d) | ε <
              euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)}) ≠ ∞ :=
      (MeasureTheory.measure_lt_top _ _).ne
    have hdual_toReal : ((gaussianSampleLaw d (n d))
          {x : Sample d (n d) | ε <
            dualMixed η d (n d) (center (residual x (Sstar d x)))}).toReal
        ≤ ((gaussianSampleLaw d (n d))
          ({x : Sample d (n d) | ε <
              ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}
            ∪ {x : Sample d (n d) | ε <
              euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)})).toReal :=
      ENNReal.toReal_mono hdual_fin hdual_mono
    have hdual_union := gaussian_union_toReal_le
      ({x : Sample d (n d) | ε <
        ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))})
      ({x : Sample d (n d) | ε <
        euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)})
    have hdual_le : ((gaussianSampleLaw d (n d))
          {x : Sample d (n d) | ε <
            dualMixed η d (n d) (center (residual x (Sstar d x)))}).toReal
        ≤ ((gaussianSampleLaw d (n d))
            {x : Sample d (n d) | ε <
              ‖center (residual x (Sstar d x))‖ / (η * Real.sqrt (d : ℝ))}).toReal
          + ((gaussianSampleLaw d (n d))
            {x : Sample d (n d) | ε <
              euclidNorm (center (residual x (Sstar d x))) / (d : ℝ)}).toReal :=
      le_trans hdual_toReal hdual_union
    linarith [hdual_le, hLinf_le, hL2_le, hσ]

end GaussianEllipsoid
