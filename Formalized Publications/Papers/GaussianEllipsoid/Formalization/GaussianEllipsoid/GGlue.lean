/- Good-events + tendsto glue for PHASE 5b-ix (g).
   Mathlib-only (no repo import): eventual index bounds, failure-prob
   tendsto lemmas, d/sqrt(n) limit, Metric forall-sigma criterion.
   Pinned toolchain: Lean 4.34.0-rc2, mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Order.Field

noncomputable section

open Filter Topology

namespace GGlue

/-- Eventual quadratic upper bound on `n` from `n/d^2 → α₀`.
    Feeds `n·ρ^d → 0` via `squeeze_zero'`. -/
theorem eventual_n_le_of_tendsto {n : ℕ → ℕ} {α₀ : ℝ}
    (h : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    ∀ᶠ d : ℕ in atTop, (n d : ℝ) ≤ (α₀ + 1) * (d : ℝ) ^ 2 := by
  have hle : ∀ᶠ d : ℕ in atTop, (n d : ℝ) / (d : ℝ) ^ 2 ≤ α₀ + 1 :=
    h.eventually (eventually_le_nhds (by linarith : α₀ < α₀ + 1))
  have h1 : ∀ᶠ d : ℕ in atTop, 1 ≤ d := eventually_ge_atTop 1
  filter_upwards [hle, h1] with d hd1 hd2
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd2
  have hsq : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  exact (div_le_iff₀ hsq).mp hd1

/-- The Davidson–Szarek failure probability `2exp(-d/2) → 0`. -/
theorem tendsto_two_mul_exp_neg_half :
    Tendsto (fun d : ℕ => 2 * Real.exp (-(d : ℝ) / 2)) atTop (nhds 0) := by
  have hnat : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hhalf : Tendsto (fun d : ℕ => (d : ℝ) / 2) atTop atTop := by
    have h2 := hnat.atTop_mul_const (show (0 : ℝ) < 1 / 2 by norm_num)
    refine Tendsto.congr' ?_ h2
    filter_upwards with d
    show (d : ℝ) * (1 / 2) = (d : ℝ) / 2
    exact mul_one_div _ _
  have hcomp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
  have hmul := hcomp.const_mul 2
  rw [mul_zero] at hmul
  refine Tendsto.congr' ?_ hmul
  filter_upwards with d
  show 2 * Real.exp (-((d : ℝ) / 2)) = 2 * Real.exp (-(d : ℝ) / 2)
  congr 1
  congr 1
  exact (neg_div 2 ((d : ℝ))).symm

/-- Forall-sigma criterion: nonnegative `P_d` with `∀ σ>0, ∀ᶠ d, P_d ≤ σ`
    tends to `0`. This is the `Metric.tendsto_atTop`/`Metric.tendsto_nhds`
    form used to assemble the (g) failure probabilities. -/
theorem tendsto_zero_of_eventually_le {P : ℕ → ℝ}
    (hP : ∀ d : ℕ, 0 ≤ P d)
    (h : ∀ σ : ℝ, 0 < σ → ∀ᶠ d : ℕ in atTop, P d ≤ σ) :
    Tendsto P atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hσ := h (ε / 2) (by linarith)
  filter_upwards [hσ] with d hd
  rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (hP d)]
  linarith

/-- Helper: `d^2 * ρ^d → 0` for `0 < ρ < 1`, via
    `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` composed with
    `β * d → atTop` where `β = -log ρ`. -/
theorem tendsto_sq_mul_pow {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun d : ℕ => (d : ℝ) ^ 2 * ρ ^ d) atTop (nhds 0) := by
  have hlog : Real.log ρ < 0 := (Real.log_neg_iff hρ0).mpr hρ1
  have hβ : (0 : ℝ) < -Real.log ρ := by linarith
  set β : ℝ := -Real.log ρ with hβdef
  have hρeq : ρ = Real.exp (-β) := by
    rw [hβdef, neg_neg, Real.exp_log hρ0]
  have hnat : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinner : Tendsto (fun d : ℕ => β * (d : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hβ hnat
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hcomp := hbase.comp hinner
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβne
  have hscale := hcomp.const_mul ((β ^ 2)⁻¹)
  rw [mul_zero] at hscale
  have hexp : ∀ d : ℕ, (Real.exp (-β)) ^ d = Real.exp (-(β * (d : ℝ))) := by
    intro d
    rw [← Real.exp_nat_mul]
    congr 1
    rw [mul_neg, mul_comm ((d : ℝ)) β]
  have hsq : ∀ d : ℕ, (β * (d : ℝ)) ^ 2 = β ^ 2 * (d : ℝ) ^ 2 := by
    intro d
    exact mul_pow _ _ _
  refine Tendsto.congr' ?_ hscale
  filter_upwards with d
  show (β ^ 2)⁻¹ * (((β * (d : ℝ)) ^ 2) * Real.exp (-(β * (d : ℝ))))
    = (d : ℝ) ^ 2 * ρ ^ d
  rw [hρeq, hexp, hsq]
  field_simp

/-- `n·ρ^d → 0` for `0 ≤ ρ < 1` when `n/d^2 → α₀`
    (eventual `n ≤ (α₀+1)d^2` + squeeze). Covers the chi-square
    union term `n·exp(-d/2)·(√2)^d` after rewriting as `n·ρ^d`. -/
theorem tendsto_n_mul_pow {n : ℕ → ℕ} {α₀ ρ : ℝ}
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀))
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun d : ℕ => (n d : ℝ) * ρ ^ d) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hρ0 with rfl | hρpos
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with d hd
    show (0 : ℝ) = (n d : ℝ) * (0 : ℝ) ^ d
    rw [zero_pow (by omega : d ≠ 0), mul_zero]
  · have hle := eventual_n_le_of_tendsto hlim
    have hmain := tendsto_sq_mul_pow hρpos hρ1
    have hg : Tendsto (fun d : ℕ => (α₀ + 1) * ((d : ℝ) ^ 2 * ρ ^ d)) atTop
        (nhds 0) := by
      have h2 := hmain.const_mul (α₀ + 1)
      rw [mul_zero] at h2
      exact h2
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards with d
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hρ0 _)
    · filter_upwards [hle] with d hd
      calc (n d : ℝ) * ρ ^ d ≤ ((α₀ + 1) * (d : ℝ) ^ 2) * ρ ^ d :=
            mul_le_mul_of_nonneg_right hd (pow_nonneg hρ0 _)
        _ = (α₀ + 1) * ((d : ℝ) ^ 2 * ρ ^ d) := by ring

/-- `n → ∞` when `n/d^2 → α₀ > 0` (via `(α₀/2)d^2 → ∞`). -/
theorem tendsto_n_atTop {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (n d : ℝ)) atTop atTop := by
  have hge : ∀ᶠ d : ℕ in atTop, α₀ / 2 ≤ (n d : ℝ) / (d : ℝ) ^ 2 :=
    hlim.eventually (eventually_ge_nhds (by linarith : α₀ / 2 < α₀))
  have h1 : ∀ᶠ d : ℕ in atTop, 1 ≤ d := eventually_ge_atTop 1
  have hnat : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 2 ≠ 0)
  have hsq : Tendsto (fun d : ℕ => (d : ℝ) ^ 2) atTop atTop :=
    hpow.comp hnat
  have hquad : Tendsto (fun d : ℕ => (α₀ / 2) * (d : ℝ) ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by linarith : (0 : ℝ) < α₀ / 2) hsq
  refine tendsto_atTop_mono' atTop ?_ hquad
  filter_upwards [hge, h1] with d hdge hd1
  have hdR : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one hd1
  have hsqpos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  exact (le_div_iff₀ hsqpos).mp hdge

/-- `d/√n → 1/√α₀` when `n/d^2 → α₀ > 0` (via inversion + `√·`
    continuity; the pointwise identities hold even at `d = 0`). -/
theorem tendsto_div_sqrt {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (_hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (d : ℝ) / Real.sqrt (n d : ℝ)) atTop
      (nhds (1 / Real.sqrt α₀)) := by
  have hαne : α₀ ≠ 0 := ne_of_gt hα
  have hinv : Tendsto (fun d : ℕ => (d : ℝ) ^ 2 / (n d : ℝ)) atTop
      (nhds α₀⁻¹) := by
    have h1 := hlim.inv₀ hαne
    refine Tendsto.congr' ?_ h1
    filter_upwards with d
    show ((n d : ℝ) / (d : ℝ) ^ 2)⁻¹ = (d : ℝ) ^ 2 / (n d : ℝ)
    exact inv_div _ _
  have hsqrt := hinv.sqrt
  have hlim_eq : Real.sqrt α₀⁻¹ = 1 / Real.sqrt α₀ := by
    rw [Real.sqrt_inv, inv_eq_one_div]
  rw [hlim_eq] at hsqrt
  refine Tendsto.congr' ?_ hsqrt
  filter_upwards with d
  show Real.sqrt ((d : ℝ) ^ 2 / (n d : ℝ)) = (d : ℝ) / Real.sqrt (n d : ℝ)
  rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

/-- Eventual good-index conjunction: `1 ≤ d`, `1 < n d`, `d ≤ n d`.
    Flags the `d ≥ 1` vs `d ≥ 2` threshold: pointwise lemmas need
    `1 ≤ d` (for `√d ≠ 0`), `1 < n` (deleted objects),
    `d ≤ n` (Davidson–Szarek); all hold eventually under
    `n/d^2 → α₀ > 0`, so the final assembly uses eventual
    hypotheses rather than a global `d ≥ 2`. -/
theorem eventually_good_index {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (_hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    ∀ᶠ d : ℕ in atTop, 1 ≤ d ∧ 1 < n d ∧ (d : ℝ) ≤ (n d : ℝ) := by
  have h1 : ∀ᶠ d : ℕ in atTop, 1 ≤ d := eventually_ge_atTop 1
  have hnat := tendsto_n_atTop hα hlim
  have hn1 : ∀ᶠ d : ℕ in atTop, 1 < n d := by
    have hev : ∀ᶠ d : ℕ in atTop, (1 : ℝ) < (n d : ℝ) :=
      hnat.eventually (eventually_gt_atTop 1)
    filter_upwards [hev] with d hd
    exact_mod_cast hd
  have hdn : ∀ᶠ d : ℕ in atTop, (d : ℝ) ≤ (n d : ℝ) := by
    have hge : ∀ᶠ d : ℕ in atTop, α₀ / 2 ≤ (n d : ℝ) / (d : ℝ) ^ 2 :=
      hlim.eventually (eventually_ge_nhds (by linarith : α₀ / 2 < α₀))
    have hbig : ∀ᶠ d : ℕ in atTop, (d : ℝ) ≤ (α₀ / 2) * (d : ℝ) ^ 2 := by
      obtain ⟨N, hN⟩ := exists_nat_ge (2 / α₀)
      filter_upwards [eventually_ge_atTop N] with d hd
      have hdN : (N : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have h2α : (2 / α₀) ≤ (d : ℝ) := le_trans hN hdN
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have h1 : (1 : ℝ) ≤ (α₀ / 2) * (d : ℝ) := by
        have h2 : (2 : ℝ) ≤ (d : ℝ) * α₀ := (div_le_iff₀ hα).mp h2α
        linarith
      calc (d : ℝ) = (d : ℝ) * 1 := (mul_one _).symm
        _ ≤ (d : ℝ) * ((α₀ / 2) * (d : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hd0
        _ = (α₀ / 2) * (d : ℝ) ^ 2 := by ring
    filter_upwards [hge, h1, hbig] with d hdge hd1 hdbig
    have hdR : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hd1
    have hsqpos : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have hle : (α₀ / 2) * (d : ℝ) ^ 2 ≤ (n d : ℝ) :=
      (le_div_iff₀ hsqpos).mp hdge
    exact le_trans hdbig hle
  exact h1.and (hn1.and hdn)

/-- `d^2/n → α₀⁻¹` when `n/d^2 → α₀ > 0`. -/
theorem tendsto_sq_div_n {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (d : ℝ) ^ 2 / (n d : ℝ)) atTop (nhds α₀⁻¹) := by
  have h1 := hlim.inv₀ (ne_of_gt hα)
  refine Tendsto.congr' ?_ h1
  filter_upwards with d
  show ((n d : ℝ) / (d : ℝ) ^ 2)⁻¹ = (d : ℝ) ^ 2 / (n d : ℝ)
  exact inv_div _ _

/-- `d/n → 0` when `n/d^2 → α₀ > 0` (via `(d^2/n)·(1/d)`). -/
theorem tendsto_d_div_n {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (d : ℝ) / (n d : ℝ)) atTop (nhds 0) := by
  have hsq := tendsto_sq_div_n hα hlim
  have h1d : Tendsto (fun d : ℕ => (1 : ℝ) / (d : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hmul := hsq.mul h1d
  rw [mul_zero] at hmul
  refine Tendsto.congr' ?_ hmul
  filter_upwards [eventually_ge_atTop 1] with d hd
  show (d : ℝ) ^ 2 / (n d : ℝ) * (1 / (d : ℝ)) = (d : ℝ) / (n d : ℝ)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hnR : (n d : ℝ) ≠ 0 := by exact_mod_cast (hn d).ne'
  field_simp

/-- `√(d/n) → 0` when `n/d^2 → α₀ > 0`. -/
theorem tendsto_sqrt_d_div_n {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => Real.sqrt ((d : ℝ) / (n d : ℝ))) atTop (nhds 0) := by
  have h := (tendsto_d_div_n hα hn hlim).sqrt
  rw [Real.sqrt_zero] at h
  exact h

/-- `n - 1 → ∞` when `n/d^2 → α₀ > 0`. -/
theorem tendsto_pred_atTop {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (n d : ℝ) - 1) atTop atTop := by
  have hnat := tendsto_n_atTop hα hlim
  have hhalf : Tendsto (fun d : ℕ => (n d : ℝ) / 2) atTop atTop := by
    have h2 := hnat.atTop_mul_const (show (0 : ℝ) < 1 / 2 by norm_num)
    refine Tendsto.congr' ?_ h2
    filter_upwards with d
    show (n d : ℝ) * (1 / 2) = (n d : ℝ) / 2
    exact mul_one_div _ _
  have h2 : ∀ᶠ d : ℕ in atTop, (2 : ℝ) ≤ (n d : ℝ) :=
    hnat.eventually (eventually_ge_atTop 2)
  refine tendsto_atTop_mono' atTop ?_ hhalf
  filter_upwards [h2] with d hd
  show (n d : ℝ) / 2 ≤ (n d : ℝ) - 1
  linarith

/-- `1/(n-1) → 0` when `n/d^2 → α₀ > 0`. -/
theorem tendsto_one_div_pred {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (1 : ℝ) / ((n d : ℝ) - 1)) atTop (nhds 0) :=
  (tendsto_pred_atTop hα hlim).const_div_atTop 1

/-- `n/(n-1) → 1` when `n/d^2 → α₀ > 0`. -/
theorem tendsto_n_div_pred {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (n d : ℝ) / ((n d : ℝ) - 1)) atTop (nhds 1) := by
  have hnat := tendsto_n_atTop hα hlim
  have hsub := tendsto_pred_atTop hα hlim
  have h1 : Tendsto (fun d : ℕ => (1 : ℝ) / ((n d : ℝ) - 1)) atTop (nhds 0) :=
    hsub.const_div_atTop 1
  have hadd : Tendsto (fun d : ℕ => (1 : ℝ) + 1 / ((n d : ℝ) - 1)) atTop
      (nhds 1) := by
    have h2 : Tendsto (fun d : ℕ => (1 : ℝ) + 1 / ((n d : ℝ) - 1)) atTop
        (nhds (1 + 0)) :=
      tendsto_const_nhds.add h1
    rwa [add_zero] at h2
  have h2 : ∀ᶠ d : ℕ in atTop, (2 : ℝ) ≤ (n d : ℝ) :=
    hnat.eventually (eventually_ge_atTop 2)
  refine Tendsto.congr' ?_ hadd
  filter_upwards [h2] with d hd
  show (1 : ℝ) + 1 / ((n d : ℝ) - 1) = (n d : ℝ) / ((n d : ℝ) - 1)
  have hne : (n d : ℝ) - 1 ≠ 0 := by
    have hpos : (0 : ℝ) < (n d : ℝ) - 1 := by linarith
    exact ne_of_gt hpos
  have heq : (n d : ℝ) / ((n d : ℝ) - 1)
      = (((n d : ℝ) - 1) + 1) / ((n d : ℝ) - 1) := by
    rw [sub_add_cancel]
  rw [heq, add_div, div_self hne]

/-- `d/(n-1) → 0` when `n/d^2 → α₀ > 0` (via `(d/n)·(n/(n-1))`). -/
theorem tendsto_d_div_pred {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (d : ℝ) / ((n d : ℝ) - 1)) atTop (nhds 0) := by
  have hmul := (tendsto_d_div_n hα hn hlim).mul (tendsto_n_div_pred hα hlim)
  rw [zero_mul] at hmul
  have hpos : ∀ᶠ d : ℕ in atTop, (0 : ℝ) < (n d : ℝ) - 1 :=
    (tendsto_pred_atTop hα hlim).eventually (eventually_gt_atTop 0)
  refine Tendsto.congr' ?_ hmul
  filter_upwards [hpos] with d hd
  show (d : ℝ) / (n d : ℝ) * ((n d : ℝ) / ((n d : ℝ) - 1))
    = (d : ℝ) / ((n d : ℝ) - 1)
  have h1 : (n d : ℝ) - 1 ≠ 0 := ne_of_gt hd
  have h2 : (n d : ℝ) ≠ 0 := by exact_mod_cast (hn d).ne'
  field_simp

/-- The covariance-good-event threshold `C(d) → 0`: the
    `deletedCovariance_uniform_tail` bound at `t = 1/4`, `v = 2d`.
    First summand `(n/(n-1))·(4√(d/n) + 4d/n) → 1·0`;
    second `(1/(n-1))·(1+2d) → 0`. -/
theorem tendsto_covThreshold {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (n d : ℝ) / ((n d : ℝ) - 1)
        * (4 * Real.sqrt ((d : ℝ) / (n d : ℝ)) + 4 * ((d : ℝ) / (n d : ℝ)))
        + (1 / ((n d : ℝ) - 1)) * (1 + 2 * (d : ℝ))) atTop (nhds 0) := by
  have hdn0 := tendsto_d_div_n hα hn hlim
  have hsdn0 := tendsto_sqrt_d_div_n hα hn hlim
  have hA : Tendsto (fun d : ℕ => 4 * Real.sqrt ((d : ℝ) / (n d : ℝ))
      + 4 * ((d : ℝ) / (n d : ℝ))) atTop (nhds 0) := by
    have h2a := hsdn0.const_mul 4
    have h2b := hdn0.const_mul 4
    have h2 := h2a.add h2b
    rw [mul_zero, add_zero] at h2
    exact h2
  have hB := tendsto_n_div_pred hα hlim
  have hfirst : Tendsto (fun d : ℕ => (n d : ℝ) / ((n d : ℝ) - 1)
      * (4 * Real.sqrt ((d : ℝ) / (n d : ℝ)) + 4 * ((d : ℝ) / (n d : ℝ))))
      atTop (nhds 0) := by
    have h2 := hB.mul hA
    rw [one_mul] at h2
    exact h2
  have hsecond : Tendsto (fun d : ℕ => (1 / ((n d : ℝ) - 1))
      * (1 + 2 * (d : ℝ))) atTop (nhds 0) := by
    have h2d := (tendsto_d_div_pred hα hn hlim).const_mul 2
    rw [mul_zero] at h2d
    have hsum := (tendsto_one_div_pred hα hlim).add h2d
    rw [add_zero] at hsum
    have hpos : ∀ᶠ d : ℕ in atTop, (0 : ℝ) < (n d : ℝ) - 1 :=
      (tendsto_pred_atTop hα hlim).eventually (eventually_gt_atTop 0)
    refine Tendsto.congr' ?_ hsum
    filter_upwards [hpos] with d hd
    show 1 / ((n d : ℝ) - 1) + 2 * ((d : ℝ) / ((n d : ℝ) - 1))
      = (1 / ((n d : ℝ) - 1)) * (1 + 2 * (d : ℝ))
    have hne : (n d : ℝ) - 1 ≠ 0 := ne_of_gt hd
    field_simp
  have hsum := hfirst.add hsecond
  rw [add_zero] at hsum
  exact hsum

/-- `1/√(1-2·(1/4)) = √2` (chi-square factor at `t = 1/4`). -/
theorem chi_factor_quarter : (1 : ℝ) / Real.sqrt (1 - 2 * (1 / 4)) = Real.sqrt 2 := by
  have h : (1 : ℝ) - 2 * (1 / 4) = 1 / 2 := by ring
  rw [h]
  have h2 : Real.sqrt ((1 : ℝ) / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num), Real.sqrt_one]
  rw [h2, one_div, one_div, inv_inv]

/-- The chi-square union base `ρ = √2·exp(-1/2)` lies in `(0,1)`:
    `√2 < 3/2` and `exp(1/2) ≥ 1 + 1/2 = 3/2`. -/
theorem chi_base_mem {ρ : ℝ} (hρ : ρ = Real.sqrt 2 * Real.exp (-1 / 2)) :
    0 < ρ ∧ ρ < 1 := by
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hexp_pos : (0 : ℝ) < Real.exp (-1 / 2) := Real.exp_pos _
  have hsqrt2_lt : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num
  have hexp_ge : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
    have h := Real.add_one_le_exp (1 / 2)
    linarith [h]
  have hneg : (-1 / 2 : ℝ) = -(1 / 2) := by ring
  have hexp_inv : Real.exp (-1 / 2) = (Real.exp (1 / 2))⁻¹ := by
    rw [hneg]
    exact Real.exp_neg _
  have hexp_pos2 : (0 : ℝ) < Real.exp (1 / 2) := Real.exp_pos _
  constructor
  · rw [hρ]
    exact mul_pos hsqrt2_pos hexp_pos
  · rw [hρ, hexp_inv]
    have hlt : Real.sqrt 2 < Real.exp (1 / 2) := lt_of_lt_of_le hsqrt2_lt hexp_ge
    calc Real.sqrt 2 * (Real.exp (1 / 2))⁻¹
        < Real.exp (1 / 2) * (Real.exp (1 / 2))⁻¹ :=
          mul_lt_mul_of_pos_right hlt (inv_pos.mpr hexp_pos2)
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hexp_pos2)

/-- The `deletedCovariance_uniform_tail` chi-square failure term at
    `t = 1/4`, `v = 2d` tends to zero (as `n·ρ^d`). -/
theorem tendsto_chi_union {n : ℕ → ℕ} {α₀ : ℝ} (_hα : 0 < α₀)
    (_hn : ∀ d : ℕ, 0 < n d)
    (hlim : Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2) atTop (nhds α₀)) :
    Tendsto (fun d : ℕ => (n d : ℝ) * (Real.exp (-(1 / 4) * (2 * (d : ℝ)))
      * (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d)) atTop (nhds 0) := by
  set ρ : ℝ := Real.sqrt 2 * Real.exp (-1 / 2) with hρdef
  have hmem := chi_base_mem hρdef
  have hmain := tendsto_n_mul_pow hlim hmem.1.le hmem.2
  refine Tendsto.congr' ?_ hmain
  filter_upwards with d
  show (n d : ℝ) * ρ ^ d = (n d : ℝ) * (Real.exp (-(1 / 4) * (2 * (d : ℝ)))
    * (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d)
  congr 1
  rw [hρdef, mul_pow, chi_factor_quarter]
  have hexp1 : (Real.exp (-1 / 2)) ^ d = Real.exp (-(1 / 4) * (2 * (d : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp1]
  exact mul_comm _ _

end GGlue
