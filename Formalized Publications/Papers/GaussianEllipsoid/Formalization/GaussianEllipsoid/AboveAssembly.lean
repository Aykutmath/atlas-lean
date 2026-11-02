/-
Above-threshold assembly (paper Sections 2 and 16): the conditional
above-threshold theorem.

The assembly takes a single explicit premise, the Section 16 uniform
conic bound. Everything else — the A0 reduction to a floored aspect
ratio, the exponential-decay limit, and the probability assembly — is
proved.
Mathematical source: paper.tex, Sections 2 and 16.
-/
import GaussianEllipsoid.AboveObjects
import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.Reductions
import GaussianEllipsoid.PaperMain
import Mathlib.Order.Filter.AtTopBot.Field

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace GaussianEllipsoid

/-! ### Exponential decay of the failure bound -/

/-- `exp(-C d²) → 0` for positive `C`. -/
theorem tendsto_exp_neg_sq {C : ℝ} (hC : 0 < C) :
    Filter.Tendsto (fun d : Nat => Real.exp (-C * (d : ℝ) ^ 2))
      Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => -C * x ^ 2)
      Filter.atTop Filter.atBot :=
    Filter.tendsto_neg_const_mul_pow_atTop two_ne_zero
      (neg_lt_zero.mpr hC)
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  have h3 := Real.tendsto_exp_atBot.comp h2
  apply h3.congr
  intro d
  simp [Function.comp_apply, neg_mul]

/-! ### Floored aspect-ratio sequence (A0, above direction) -/

/-- The reduced sequence `n'(d) = ⌊α₀d²⌋₊`. -/
def reduceAbove (α₀ : ℝ) (d : Nat) : Nat := ⌊α₀ * (d : ℝ) ^ 2⌋₊

/-- Bridge between the `ENNReal` dimension ratio and the real aspect
ratio, upper-bound form. -/
theorem dimensionRatio_gt_ofReal {n' : Nat → Nat} {α₀ : ℝ} {d : Nat}
    (hd : 1 ≤ d) (hα₀ : 0 < α₀) :
    ENNReal.ofReal α₀ < dimensionRatio n' d
      ↔ α₀ < ((n' d : ℝ) / (d : ℝ) ^ 2) := by
  unfold dimensionRatio
  have hdN : d ≠ 0 := by omega
  have hdsq0 : ((d : ENNReal) ^ 2) ≠ 0 := by
    rw [← Nat.cast_pow]
    exact_mod_cast pow_ne_zero 2 hdN
  have hdsqT : ((d : ENNReal) ^ 2) ≠ ⊤ := by
    rw [← Nat.cast_pow]
    exact ENNReal.natCast_ne_top _
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hdsq0) (Or.inl hdsqT)]
  have hcast : ((n' d : Nat) : ENNReal) = ENNReal.ofReal (n' d : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  have hdsq : ((d : ENNReal) ^ 2) = ENNReal.ofReal ((d : ℝ) ^ 2) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow]
    exact (ENNReal.ofReal_natCast _).symm
  have hnn : 0 ≤ α₀ * (d : ℝ) ^ 2 :=
    mul_nonneg (le_of_lt hα₀) (sq_nonneg _)
  rw [hcast, hdsq, ← ENNReal.ofReal_mul (le_of_lt hα₀),
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn]
  have hdsqR : (0 : ℝ) < (d : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < d)) 2
  exact (lt_div_iff₀ hdsqR).symm

/-- Above a strict ratio bound, the reduction is eventually dominated by
the original sequence. -/
theorem eventually_le_reduceAbove {n : Nat → Nat} {α₀ : ℝ}
    (hlim : ENNReal.ofReal α₀
      < Filter.liminf (dimensionRatio n) Filter.atTop)
    (hα₀ : 0 < α₀) :
    ∀ᶠ (d : Nat) in Filter.atTop, reduceAbove α₀ d ≤ n d := by
  have hev : ∀ᶠ d in Filter.atTop,
      ENNReal.ofReal α₀ < dimensionRatio n d :=
    Filter.eventually_lt_of_lt_liminf hlim
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with d hdim hd
  rw [dimensionRatio_gt_ofReal hd hα₀] at hdim
  have hdsq : (0 : ℝ) < (d : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < d)) 2
  have hlt : α₀ * (d : ℝ) ^ 2 < (n d : ℝ) :=
    (lt_div_iff₀ hdsq).mp hdim
  have hle : ((reduceAbove α₀ d : Nat) : ℝ) ≤ (n d : ℝ) := by
    have h1 : ((⌊α₀ * (d : ℝ) ^ 2⌋₊ : Nat) : ℝ) ≤ α₀ * (d : ℝ) ^ 2 :=
      Nat.floor_le (mul_nonneg (le_of_lt hα₀) (sq_nonneg _))
    unfold reduceAbove
    linarith
  exact_mod_cast hle

/-- The reduced sequence eventually lies in any strictly smaller aspect
interval. -/
theorem reduceAbove_aspect {α₀ αm : ℝ} (_hα₀ : 1 / 4 < α₀)
    (hαm : 1 / 4 < αm) (hm : αm < α₀) :
    ∀ᶠ (d : Nat) in Filter.atTop,
      αm * (d : ℝ) ^ 2 ≤ ((reduceAbove α₀ d : Nat) : ℝ)
        ∧ ((reduceAbove α₀ d : Nat) : ℝ) ≤ α₀ * (d : ℝ) ^ 2 := by
  have hgap : 0 < α₀ - αm := by linarith
  set N₀ : Nat := ⌈1 / (α₀ - αm)⌉₊ + 1 with hNdef
  have hN : (1 : ℝ) / (α₀ - αm) < (N₀ : ℝ) := by
    have h1 : (1 : ℝ) / (α₀ - αm) ≤ (⌈1 / (α₀ - αm)⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h2 : (⌈1 / (α₀ - αm)⌉₊ : ℝ) < (N₀ : ℝ) := by
      rw [hNdef]
      push_cast
      linarith
    linarith
  filter_upwards [Filter.eventually_ge_atTop N₀] with d hd
  have hd1 : (1 : ℝ) ≤ d := by
    have hN1 : (1 : ℝ) ≤ N₀ := by
      have h1N : 1 ≤ N₀ := by
        rw [hNdef]
        exact Nat.le_add_left 1 _
      exact_mod_cast h1N
    have hdd : (N₀ : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hd
    linarith
  have hdsqd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hd1)]
  have hdsqN : (1 : ℝ) / (α₀ - αm) < (d : ℝ) ^ 2 := by
    have hdd : (N₀ : ℝ) ≤ (d : ℝ) := Nat.cast_le.mpr hd
    linarith [hN, hdsqd, hdd]
  have hupper : ((reduceAbove α₀ d : Nat) : ℝ) ≤ α₀ * (d : ℝ) ^ 2 := by
    unfold reduceAbove
    exact Nat.floor_le (mul_nonneg (by linarith) (sq_nonneg _))
  have hlower : αm * (d : ℝ) ^ 2 ≤ ((reduceAbove α₀ d : Nat) : ℝ) := by
    have hfl : α₀ * (d : ℝ) ^ 2 - 1 < ((⌊α₀ * (d : ℝ) ^ 2⌋₊ : Nat) : ℝ) := by
      have h := Nat.lt_floor_add_one (α₀ * (d : ℝ) ^ 2)
      linarith
    have hgap2 : (1 : ℝ) ≤ (α₀ - αm) * (d : ℝ) ^ 2 := by
      have hmul : (α₀ - αm) * ((1 : ℝ) / (α₀ - αm))
          < (α₀ - αm) * (d : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_left hdsqN hgap
      rw [mul_one_div_cancel (ne_of_gt hgap)] at hmul
      linarith
    unfold reduceAbove
    nlinarith [hfl, hgap2]
  exact ⟨hlower, hupper⟩

/-! ### Aspect interpolation and the conditional theorem -/

/-- Between `1/4` and the liminf ratio, room for the conic interval:
there are `αm < α₀` with `1/4 < αm` and `ofReal α₀` still below the
liminf. The infinite-liminf case takes fixed constants. -/
theorem exists_aspect_pair {n : Nat → Nat}
    (hlim : (1 / 4 : ENNReal)
      < Filter.liminf (dimensionRatio n) Filter.atTop) :
    ∃ αm α₀ : ℝ, 1 / 4 < αm ∧ αm < α₀ ∧
      ENNReal.ofReal α₀ < Filter.liminf (dimensionRatio n) Filter.atTop := by
  by_cases hfin : Filter.liminf (dimensionRatio n) Filter.atTop ≠ ⊤
  · set L : ℝ := (Filter.liminf (dimensionRatio n) Filter.atTop).toReal
      with hLdef
    have hL4 : 1 / 4 < L := by
      have h14 : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4) :=
        ennreal_quarter_eq_ofReal
      have hback : ENNReal.ofReal L
          = Filter.liminf (dimensionRatio n) Filter.atTop :=
        ENNReal.ofReal_toReal hfin
      rw [h14, ← hback] at hlim
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (by norm_num : (0 : ℝ) ≤ 1 / 4)).mp hlim
    have hLnn : 0 ≤ L := ENNReal.toReal_nonneg
    refine ⟨(1 / 4 + L) / 2, ((1 / 4 + L) / 2 + L) / 2, by linarith,
      by linarith, ?_⟩
    have hback : ENNReal.ofReal L
        = Filter.liminf (dimensionRatio n) Filter.atTop :=
      ENNReal.ofReal_toReal hfin
    rw [← hback]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (by linarith : (0 : ℝ) ≤ ((1 / 4 + L) / 2 + L) / 2)).mpr
    linarith
  · push Not at hfin
    exact ⟨3 / 8, 1 / 2, by norm_num, by norm_num, by
      rw [hfin]; exact ENNReal.ofReal_lt_top⟩

/-- The above-threshold direction, conditional on the single Section 16
interface premise (the uniform conic bound). -/
theorem above_threshold_conditional
    (hConic : UniformConicBound) : AboveThresholdStatement := by
  intro n _ hlim
  obtain ⟨αm, α₀, hαm4, hm, hα₀lim⟩ := exists_aspect_pair hlim
  have hα₀ : 0 < α₀ := by linarith
  have hα04 : 1 / 4 < α₀ := by linarith
  obtain ⟨c, C, hc, hC, hevC⟩ := hConic αm α₀ hαm4 hm.le
  have hdom := eventually_le_reduceAbove hα₀lim hα₀
  have hasp := reduceAbove_aspect hα04 hαm4 hm
  have hexpT := tendsto_exp_neg_sq hC
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hexp : ∀ᶠ (d : Nat) in Filter.atTop,
      Real.exp (-C * (d : ℝ) ^ 2) < ε := by
    have h := Metric.tendsto_nhds.mp hexpT ε hε
    filter_upwards [h] with d hd
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (Real.exp_pos _).le] at hd
    exact hd
  filter_upwards [hdom, hasp, hexp, hevC, Filter.eventually_ge_atTop 1]
    with d hdom hasp hexp hCd hd1
  have hd : 0 < d := by omega
  have hn'd : 0 < reduceAbove α₀ d := by
    have hpos : (0 : ℝ) < ((reduceAbove α₀ d : Nat) : ℝ) := by
      have hsq : (0 : ℝ) < (d : ℝ) ^ 2 :=
        pow_pos (Nat.cast_pos.mpr hd) 2
      have hαm0 : (0 : ℝ) < αm := by linarith
      have h1 : (0 : ℝ) < αm * (d : ℝ) ^ 2 := mul_pos hαm0 hsq
      linarith [hasp.1]
    exact_mod_cast hpos
  have hmono := measure_fit_mono (d := d)
    (m := reduceAbove α₀ d) (n := n d) hdom
  have hsub := fit_subset_conic (d := d) (n := reduceAbove α₀ d)
    (c := c) hd hn'd hc
  have hconic := hCd (reduceAbove α₀ d) hasp.1 hasp.2
  have hchain : fitProbability d (n d)
      ≤ Real.exp (-C * (d : ℝ) ^ 2) := by
    unfold fitProbability fitEvent
    have h1 := ENNReal.toReal_mono (sampleLaw_ne_top _) hmono
    have h2 := ENNReal.toReal_mono (sampleLaw_ne_top _)
      (measure_mono hsub)
    exact le_trans (le_trans h1 h2) hconic
  have hPnn : 0 ≤ fitProbability d (n d) := ENNReal.toReal_nonneg
  show dist (fitProbability d (n d)) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hPnn]
  linarith [hchain, hexp]

end GaussianEllipsoid
