/-
Below-threshold assembly (paper Sections 2 and 12): the conditional
below-threshold theorem.

The assembly takes four explicit premises: the Section 11 mixed-norm
bound, the Section 4 Huber residuals, the Section 12 quotient bridge,
and the external Bandeira-Maillard premise. Huber selector existence
(Section 4 compactness) is discharged in `SelectorExists`.
Everything else — the B0 enlargement, the aspect-ratio convergence, the
pathwise exactification, and the probability-limit assembly — is proved.
Mathematical source: paper.tex, Sections 2 and 12.
-/
import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.Reductions
import GaussianEllipsoid.PaperMain
import GaussianEllipsoid.SelectorExists
import Mathlib.Order.Filter.AtTopBot.Ring

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace GaussianEllipsoid

/-! ### Enlarged aspect-ratio sequence (B0, below direction) -/

/-- The enlarged sequence `n'(d) = ⌈α₀d²⌉₊ + 1`, converging in ratio to `α₀`. -/
def enlargeBelow (α₀ : ℝ) (d : Nat) : Nat := ⌈α₀ * (d : ℝ) ^ 2⌉₊ + 1

theorem enlargeBelow_pos (α₀ : ℝ) (d : Nat) : 0 < enlargeBelow α₀ d :=
  Nat.succ_pos _

/-- `2 / d² → 0`. -/
theorem tendsto_two_div_sq :
    Filter.Tendsto (fun d : Nat => (2 : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun d : Nat => (d : ℝ) ^ 2)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
  have hinv := hpow.inv_tendsto_atTop
  have hmul := hinv.const_mul 2
  rw [mul_zero] at hmul
  have heq : (fun d : Nat => (2 : ℝ) / (d : ℝ) ^ 2)
      = fun d : Nat => 2 * (((d : ℝ) ^ 2)⁻¹) := by
    funext d
    rw [div_eq_mul_inv]
  rw [heq]
  exact hmul

/-- The enlarged sequence has aspect ratio converging to `α₀`. -/
theorem enlargeBelow_ratio_tendsto {α₀ : ℝ} (hα₀ : 0 ≤ α₀) :
    Filter.Tendsto (fun d => ((enlargeBelow α₀ d : ℝ) / (d : ℝ) ^ 2))
      Filter.atTop (nhds α₀) := by
  have htop : Filter.Tendsto (fun d : Nat => α₀ + (2 : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀) := by
    have h := tendsto_two_div_sq.const_add α₀
    rw [add_zero] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with d hd
    show α₀ ≤ ((enlargeBelow α₀ d : ℝ) / (d : ℝ) ^ 2)
    have hdsq : (0 : ℝ) < (d : ℝ) ^ 2 :=
      pow_pos (Nat.cast_pos.mpr (by omega : 0 < d)) 2
    rw [le_div_iff₀ hdsq]
    have hceil : α₀ * (d : ℝ) ^ 2 ≤ (⌈α₀ * (d : ℝ) ^ 2⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hcast : ((⌈α₀ * (d : ℝ) ^ 2⌉₊ : Nat) : ℝ)
        ≤ ((enlargeBelow α₀ d : Nat) : ℝ) := by
      unfold enlargeBelow
      exact_mod_cast Nat.le_succ _
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with d hd
    show ((enlargeBelow α₀ d : ℝ) / (d : ℝ) ^ 2) ≤ α₀ + (2 : ℝ) / (d : ℝ) ^ 2
    have hd0 : (d : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega : d ≠ 0)
    have hdsq : (0 : ℝ) < (d : ℝ) ^ 2 :=
      pow_pos (Nat.cast_pos.mpr (by omega : 0 < d)) 2
    have hxnn : 0 ≤ α₀ * (d : ℝ) ^ 2 :=
      mul_nonneg hα₀ (le_of_lt hdsq)
    have hceil : (⌈α₀ * (d : ℝ) ^ 2⌉₊ : ℝ) < α₀ * (d : ℝ) ^ 2 + 1 :=
      Nat.ceil_lt_add_one hxnn
    have hN : ((enlargeBelow α₀ d : Nat) : ℝ) < α₀ * (d : ℝ) ^ 2 + 2 := by
      unfold enlargeBelow
      push_cast
      linarith
    have hdiv : ((enlargeBelow α₀ d : ℝ) / (d : ℝ) ^ 2)
        < (α₀ * (d : ℝ) ^ 2 + 2) / (d : ℝ) ^ 2 :=
      div_lt_div_of_pos_right hN hdsq
    have heq : (α₀ * (d : ℝ) ^ 2 + 2) / (d : ℝ) ^ 2
        = α₀ + (2 : ℝ) / (d : ℝ) ^ 2 := by
      field_simp
    rw [heq] at hdiv
    exact le_of_lt hdiv

/-- Below a strict ratio bound, the original sequence is eventually
dominated by the enlargement. -/
theorem eventually_le_enlargeBelow {n : Nat → Nat} {α₀ : ℝ}
    (hlim : Filter.limsup (dimensionRatio n) Filter.atTop
      < ENNReal.ofReal α₀)
    (hα₀ : 0 < α₀) :
    ∀ᶠ d in Filter.atTop, n d ≤ enlargeBelow α₀ d := by
  have hev : ∀ᶠ d in Filter.atTop,
      dimensionRatio n d < ENNReal.ofReal α₀ :=
    Filter.eventually_lt_of_limsup_lt hlim
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with d hdim hd
  rw [dimensionRatio_lt_ofReal hd hα₀] at hdim
  have hdsq : (0 : ℝ) < (d : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < d)) 2
  have hlt : (n d : ℝ) < α₀ * (d : ℝ) ^ 2 :=
    (div_lt_iff₀ hdsq).mp hdim
  show n d ≤ ⌈α₀ * (d : ℝ) ^ 2⌉₊ + 1
  have hle : (n d : ℝ) ≤ (((⌈α₀ * (d : ℝ) ^ 2⌉₊ + 1 : Nat)) : ℝ) := by
    have h1 : (n d : ℝ) < (⌈α₀ * (d : ℝ) ^ 2⌉₊ : ℝ) :=
      lt_of_lt_of_le hlt (Nat.le_ceil _)
    have h2 : ((⌈α₀ * (d : ℝ) ^ 2⌉₊ : Nat) : ℝ)
        ≤ ((((⌈α₀ * (d : ℝ) ^ 2⌉₊ + 1 : Nat))) : ℝ) :=
      Nat.cast_le.mpr (Nat.le_succ _)
    linarith
  exact_mod_cast hle

/-- The enlarged sequence stays below the threshold. -/
theorem enlargeBelow_limsup {α₀ : ℝ} (hα₀ : 0 ≤ α₀) (hlt : α₀ < 1 / 4) :
    Filter.limsup (dimensionRatio (enlargeBelow α₀)) Filter.atTop
      < (1 / 4 : ENNReal) := by
  have hconv := enlargeBelow_ratio_tendsto hα₀
  set β := (α₀ + 1 / 4) / 2 with hβdef
  have hαβ : α₀ < β := by rw [hβdef]; linarith
  have hβ4 : β < 1 / 4 := by rw [hβdef]; linarith
  have hβ0 : 0 < β := lt_of_le_of_lt hα₀ hαβ
  have hev : ∀ᶠ d in Filter.atTop,
      dimensionRatio (enlargeBelow α₀) d ≤ ENNReal.ofReal β := by
    have htend : ∀ᶠ d in Filter.atTop,
        ((enlargeBelow α₀ d : ℝ) / (d : ℝ) ^ 2) < β :=
      hconv.eventually (gt_mem_nhds hαβ)
    filter_upwards [htend, Filter.eventually_ge_atTop 1] with d hdb hd
    exact le_of_lt ((dimensionRatio_lt_ofReal hd hβ0).mpr hdb)
  have hle : Filter.limsup (dimensionRatio (enlargeBelow α₀)) Filter.atTop
      ≤ ENNReal.ofReal β :=
    limsup_le_of_eventually_le' hev
  have hβ4e : ENNReal.ofReal β < (1 / 4 : ENNReal) := by
    rw [ennreal_quarter_eq_ofReal, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    exact hβ4
  exact lt_of_le_of_lt hle hβ4e

/-! ### Pathwise exactification on good events -/

/-- The centered measurements vanish at zero. -/
theorem measurementT_zero {d n : Nat} (x : Sample d n) :
    measurementT x 0 = 0 := by
  have h := measurementT_add x (0 : Square d) (0 : Square d)
  rw [add_zero] at h
  have h3 : measurementT x 0 + measurementT x 0
      = measurementT x 0 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel_iff.mp h3

/-- The centered measurements commute with negation. -/
theorem measurementT_neg {d n : Nat} (x : Sample d n) (S : Square d) :
    measurementT x (-S) = -measurementT x S := by
  have h := measurementT_add x S (-S)
  rw [add_neg_cancel, measurementT_zero] at h
  apply eq_neg_of_add_eq_zero_left
  rw [add_comm]
  exact h.symm

/-- Every Huber minimizer is symmetric. -/
theorem huberMinimizer_isSymm {d n : Nat} {lo hi : ℝ} {x : Sample d n}
    {S : Square d} (h : IsHuberMinimizer lo hi x S) : S.IsSymm := by
  obtain ⟨hmem, -⟩ := h
  have hpsd : (S - lo • (1 : Square d)).PosSemidef ∧
      ((hi • (1 : Square d)) - S).PosSemidef := hmem
  have hsub : (S - lo • (1 : Square d)).IsSymm :=
    ((posSemidef_iff_coordinates _).mp hpsd.1).1
  have h1 : (lo • (1 : Square d)).IsSymm := Matrix.isSymm_one.smul lo
  have hadd := hsub.add h1
  rwa [sub_add_cancel] at hadd

/-- On a good sample — small quotient residual and a nonzero observation —
a positive definite fit exists. This is the paper's Section 12
exactification: correct the Huber selector by an almost-minimizer `H`
with `‖H‖_op < λ₋/2`, then rescale. -/
theorem hasStrictFit_of_good {d n' : Nat} {lo hi : ℝ}
    {x : Sample d n'} {Sstar : Square d}
    (hd : 0 < d) (hn : 0 < n')
    (hSspec : IsHuberMinimizer lo hi x Sstar)
    (hκ : kappa d n' x Sstar < lo / 2)
    (hlo : 0 < lo)
    (hex : ∃ i, x i ≠ 0) :
    HasStrictFit x := by
  have hSspec2 := hSspec
  obtain ⟨hmem, -⟩ := hSspec
  have hpsd : (Sstar - lo • (1 : Square d)).PosSemidef := hmem.1
  have hSsym : Sstar.IsSymm := huberMinimizer_isSymm hSspec2
  have hTeq : measurementT x Sstar = center (residual x Sstar) :=
    measurementT_eq_center_residual hd hn x Sstar
  have hfib : ∃ H : Square d, H.IsSymm
      ∧ measurementT x H = -center (residual x Sstar)
      ∧ matrixOpNorm H < lo / 2 := by
    have hne : {r : Real | ∃ H : Square d,
        H.IsSymm ∧ measurementT x H = -center (residual x Sstar)
          ∧ matrixOpNorm H = r}.Nonempty := by
      refine ⟨matrixOpNorm (-Sstar), -Sstar, hSsym.neg, ?_, rfl⟩
      rw [measurementT_neg, hTeq]
    have hbdd : BddBelow {r : Real | ∃ H : Square d,
        H.IsSymm ∧ measurementT x H = -center (residual x Sstar)
          ∧ matrixOpNorm H = r} := by
      refine ⟨0, ?_⟩
      rintro r ⟨H, -, -, rfl⟩
      exact matrixOpNorm_nonneg H
    obtain ⟨r, hrmem, hrlt⟩ := exists_lt_of_csInf_lt hne hκ
    obtain ⟨H, hHsymm, hHT, hHop⟩ := hrmem
    exact ⟨H, hHsymm, hHT, by linarith⟩
  obtain ⟨H, hHsymm, hHT, hHlt⟩ := hfib
  have hQ : (Sstar + H).PosDef :=
    posDef_add_of_opNorm_lt hpsd hHsymm hHlt hlo
  have hTQ : measurementT x (Sstar + H) = 0 := by
    rw [measurementT_add, hTeq, hHT, add_neg_cancel]
  have hcenter : center (measurementA x (Sstar + H)) = 0 := by
    have hsq : Real.sqrt (d : Real) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd)
    funext i
    have hi := congrFun hTQ i
    unfold measurementT at hi
    simp only [Pi.zero_apply] at hi
    have hdiv := (div_eq_zero_iff).mp hi
    cases hdiv with
    | inl h => exact h
    | inr h => exact absurd h hsq
  obtain ⟨i, hi⟩ := hex
  obtain ⟨c, -, hfit⟩ :=
    strictFit_rescaling_of_centered_kernel hd hn hQ i hi hcenter
  exact ⟨_, hfit⟩

/-! ### Probability assembly and the conditional theorem -/

/-- The below-threshold direction, conditional on the four interface
premises (Sections 4, 11, 12, and Bandeira-Maillard). -/
theorem below_threshold_conditional
    (hMixed : MixedNormBound) (hHuber : HuberResiduals)
    (hQuot : QuotientBridge)
    (hBM : bmApproximateFitting) : BelowThresholdStatement := by
  intro n hn0 hlim
  have hlimfin : Filter.limsup (dimensionRatio n) Filter.atTop ≠ ⊤ :=
    ne_of_lt (lt_of_lt_of_le hlim le_top)
  set L : ℝ := (Filter.limsup (dimensionRatio n) Filter.atTop).toReal
    with hLdef
  have hLnn : 0 ≤ L := ENNReal.toReal_nonneg
  have hL4 : L < 1 / 4 := by
    have h14 : ((1 / 4 : ENNReal)).toReal = 1 / 4 := by
      rw [ennreal_quarter_eq_ofReal, ENNReal.toReal_ofReal (by norm_num)]
    have h14T : (1 / 4 : ENNReal) ≠ ⊤ := by
      rw [ennreal_quarter_eq_ofReal]
      exact ENNReal.ofReal_ne_top
    have hlt := (ENNReal.toReal_lt_toReal hlimfin h14T).mpr hlim
    rwa [h14] at hlt
  set α₀ := (L + 1 / 4) / 2 with hαdef
  have hα0 : 0 < α₀ := by rw [hαdef]; linarith
  have hα4 : α₀ < 1 / 4 := by rw [hαdef]; linarith
  have hαnn : 0 ≤ α₀ := le_of_lt hα0
  have hlimα : Filter.limsup (dimensionRatio n) Filter.atTop
      < ENNReal.ofReal α₀ := by
    have hback : ENNReal.ofReal L
        = Filter.limsup (dimensionRatio n) Filter.atTop :=
      ENNReal.ofReal_toReal hlimfin
    rw [← hback, ENNReal.ofReal_lt_ofReal_iff hα0, hαdef]
    linarith
  have hn'pos : ∀ d, 0 < enlargeBelow α₀ d := enlargeBelow_pos α₀
  have hconv := enlargeBelow_ratio_tendsto hαnn
  have hlim' := enlargeBelow_limsup hαnn hα4
  obtain ⟨lo, hi, hlo, hlohi, hBMmin⟩ :=
    hBM (enlargeBelow α₀) hn'pos hlim'
  have hchoice : ∀ d (x : Sample d (enlargeBelow α₀ d)),
      ∃ S, IsHuberMinimizer lo hi x S :=
    fun d x => huberMinimizerExists_theorem d (enlargeBelow α₀ d)
      lo hi hlo hlohi x
  choose Sstar hSspec using hchoice
  rw [Metric.tendsto_nhds]
  intro ε hε
  set δ := ε / 4 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨η, c, G, hBody⟩ := hMixed (enlargeBelow α₀) hn'pos hlim' δ hδ
  have hBody2 := hBody
  obtain ⟨hη0, -, hc0, hGlim, -⟩ := hBody
  have hQ := hQuot (enlargeBelow α₀) δ η c G Sstar hBody2
  set t := c * (lo / 2) with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    exact mul_pos hc0 (by linarith)
  have hHub := hHuber (enlargeBelow α₀) α₀ hn'pos hconv hα0 hα4
    lo hi hlo hlohi hBMmin Sstar hSspec η hη0 (t / 2) (by linarith)
  have hhev : ∀ᶠ d in Filter.atTop,
      ((gaussianSampleLaw d (enlargeBelow α₀ d))
        {x | t / 2 < dualMixed η d (enlargeBelow α₀ d)
          (center (residual x (Sstar d x)))}).toReal < ε / 2 :=
    hHub.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 2))
  have hgev : ∀ᶠ d in Filter.atTop,
      ((gaussianSampleLaw d (enlargeBelow α₀ d)) (G d)ᶜ).toReal < ε / 2 := by
    have hlt : Filter.limsup (fun d =>
        ((gaussianSampleLaw d (enlargeBelow α₀ d)) (G d)ᶜ).toReal)
        Filter.atTop < ε / 2 :=
      lt_of_le_of_lt hGlim (by rw [hδdef]; linarith)
    refine Filter.eventually_lt_of_limsup_lt hlt ?_
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with d
    have h2 := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤)
      (prob_le_one (μ := gaussianSampleLaw d (enlargeBelow α₀ d))
        (s := (G d)ᶜ))
    rwa [ENNReal.toReal_one] at h2
  have hle := eventually_le_enlargeBelow hlimα hα0
  filter_upwards [hhev, hgev, hle, Filter.eventually_ge_atTop 1]
    with d hhd hgd hnd hd1
  have hd : 0 < d := by omega
  have hn' : 0 < enlargeBelow α₀ d := hn'pos d
  have hcover : {x : Sample d (enlargeBelow α₀ d) | ¬HasStrictFit x}
      ⊆ (G d)ᶜ ∪ {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
          (center (residual x (Sstar d x)))}
        ∪ {x | ∀ i, x i = 0} := by
    intro x hx
    by_cases hxG : x ∈ G d
    · by_cases hxd : t ≤ dualMixed η d (enlargeBelow α₀ d)
        (center (residual x (Sstar d x)))
      · exact Or.inl (Or.inr hxd)
      · by_cases hxz : ∃ i, x i ≠ 0
        · have hκ : kappa d (enlargeBelow α₀ d) x (Sstar d x) < lo / 2 := by
            have hqb := hQ d x hxG
            have hlt : dualMixed η d (enlargeBelow α₀ d)
                (center (residual x (Sstar d x))) < t :=
              lt_of_not_ge hxd
            have hmul : c⁻¹ * dualMixed η d (enlargeBelow α₀ d)
                (center (residual x (Sstar d x))) < c⁻¹ * t :=
              mul_lt_mul_of_pos_left hlt (inv_pos.mpr hc0)
            have heq : c⁻¹ * t = lo / 2 := by
              rw [htdef, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc0),
                one_mul]
            linarith
          have hfit := hasStrictFit_of_good hd hn' (hSspec d x) hκ hlo hxz
          exact absurd hfit hx
        · have hall : ∀ i, x i = 0 := by
            by_contra hall2
            push Not at hall2
            exact hxz hall2
          exact Or.inr hall
    · exact Or.inl (Or.inl hxG)
  have hsub : {x : Sample d (enlargeBelow α₀ d) | t ≤ dualMixed η d
        (enlargeBelow α₀ d) (center (residual x (Sstar d x)))}
      ⊆ {x | t / 2 < dualMixed η d (enlargeBelow α₀ d)
        (center (residual x (Sstar d x)))} := by
    intro x hx
    show t / 2 < _
    have hx' : t ≤ dualMixed η d (enlargeBelow α₀ d)
        (center (residual x (Sstar d x))) := hx
    linarith
  have hazero : gaussianSampleLaw d (enlargeBelow α₀ d)
      {x | ∀ i, x i = 0} = 0 :=
    sample_allZero_null hd hn'
  have hμ : gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | ¬HasStrictFit x}
      ≤ gaussianSampleLaw d (enlargeBelow α₀ d) (G d)ᶜ
        + gaussianSampleLaw d (enlargeBelow α₀ d)
          {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
            (center (residual x (Sstar d x)))}
        + gaussianSampleLaw d (enlargeBelow α₀ d) {x | ∀ i, x i = 0} := by
    have h1 : gaussianSampleLaw d (enlargeBelow α₀ d) {x | ¬HasStrictFit x}
        ≤ gaussianSampleLaw d (enlargeBelow α₀ d)
          ((G d)ᶜ ∪ {x : Sample d (enlargeBelow α₀ d) | t ≤ dualMixed η d
            (enlargeBelow α₀ d) (center (residual x (Sstar d x)))}
            ∪ {x : Sample d (enlargeBelow α₀ d) | ∀ i, x i = 0}) :=
      measure_mono hcover
    have h2 : gaussianSampleLaw d (enlargeBelow α₀ d)
          (((G d)ᶜ ∪ {x : Sample d (enlargeBelow α₀ d) | t ≤ dualMixed η d
            (enlargeBelow α₀ d) (center (residual x (Sstar d x)))})
            ∪ {x : Sample d (enlargeBelow α₀ d) | ∀ i, x i = 0})
        ≤ gaussianSampleLaw d (enlargeBelow α₀ d)
            ((G d)ᶜ ∪ {x : Sample d (enlargeBelow α₀ d) | t ≤ dualMixed η d
              (enlargeBelow α₀ d) (center (residual x (Sstar d x)))})
          + gaussianSampleLaw d (enlargeBelow α₀ d)
            {x : Sample d (enlargeBelow α₀ d) | ∀ i, x i = 0} :=
      measure_union_le _ _
    have h3 : gaussianSampleLaw d (enlargeBelow α₀ d)
          ((G d)ᶜ ∪ {x : Sample d (enlargeBelow α₀ d) | t ≤ dualMixed η d
            (enlargeBelow α₀ d) (center (residual x (Sstar d x)))})
        ≤ gaussianSampleLaw d (enlargeBelow α₀ d) (G d)ᶜ
          + gaussianSampleLaw d (enlargeBelow α₀ d)
            {x : Sample d (enlargeBelow α₀ d) | t ≤ dualMixed η d
              (enlargeBelow α₀ d) (center (residual x (Sstar d x)))} :=
      measure_union_le _ _
    calc gaussianSampleLaw d (enlargeBelow α₀ d) {x | ¬HasStrictFit x}
        ≤ gaussianSampleLaw d (enlargeBelow α₀ d)
            ((G d)ᶜ ∪ {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
              (center (residual x (Sstar d x)))}
              ∪ {x | ∀ i, x i = 0}) := h1
      _ ≤ gaussianSampleLaw d (enlargeBelow α₀ d)
            ((G d)ᶜ ∪ {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
              (center (residual x (Sstar d x)))})
          + gaussianSampleLaw d (enlargeBelow α₀ d)
            {x | ∀ i, x i = 0} := h2
      _ ≤ (gaussianSampleLaw d (enlargeBelow α₀ d) (G d)ᶜ
          + gaussianSampleLaw d (enlargeBelow α₀ d)
            {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
              (center (residual x (Sstar d x)))})
          + gaussianSampleLaw d (enlargeBelow α₀ d)
            {x | ∀ i, x i = 0} :=
          add_le_add h3 le_rfl
  have hfinG : gaussianSampleLaw d (enlargeBelow α₀ d) (G d)ᶜ ≠ ⊤ :=
    sampleLaw_ne_top _
  have hfinD : gaussianSampleLaw d (enlargeBelow α₀ d)
      {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
        (center (residual x (Sstar d x)))} ≠ ⊤ :=
    sampleLaw_ne_top _
  have hfinZ : gaussianSampleLaw d (enlargeBelow α₀ d)
      {x | ∀ i, x i = 0} ≠ ⊤ :=
    sampleLaw_ne_top _
  have hPbad : (gaussianSampleLaw d (enlargeBelow α₀ d)
      {x | ¬HasStrictFit x}).toReal < ε := by
    have hle2 := ENNReal.toReal_mono
      ((ENNReal.add_ne_top).mpr
        ⟨(ENNReal.add_ne_top).mpr ⟨hfinG, hfinD⟩, hfinZ⟩) hμ
    rw [ENNReal.toReal_add ((ENNReal.add_ne_top).mpr ⟨hfinG, hfinD⟩) hfinZ,
      ENNReal.toReal_add hfinG hfinD, hazero, ENNReal.toReal_zero,
      add_zero] at hle2
    have hmono : (gaussianSampleLaw d (enlargeBelow α₀ d)
          {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
            (center (residual x (Sstar d x)))}).toReal
        ≤ (gaussianSampleLaw d (enlargeBelow α₀ d)
          {x | t / 2 < dualMixed η d (enlargeBelow α₀ d)
            (center (residual x (Sstar d x)))}).toReal := by
      apply ENNReal.toReal_mono
      · exact sampleLaw_ne_top _
      · exact measure_mono hsub
    have hD : (gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | t ≤ dualMixed η d (enlargeBelow α₀ d)
          (center (residual x (Sstar d x)))}).toReal < ε / 2 :=
      lt_of_le_of_lt hmono hhd
    linarith [hle2, hgd, hD]
  have hunion : ({x : Sample d (enlargeBelow α₀ d) | HasStrictFit x}
      ∪ {x | ¬HasStrictFit x}) = Set.univ := by
    ext x
    constructor
    · intro _; trivial
    · intro _
      by_cases hx : HasStrictFit x
      · exact Or.inl hx
      · exact Or.inr hx
  have h1 : (1 : ℝ) ≤ (gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | HasStrictFit x}).toReal
      + (gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | ¬HasStrictFit x}).toReal := by
    have hleU : gaussianSampleLaw d (enlargeBelow α₀ d) Set.univ
        ≤ gaussianSampleLaw d (enlargeBelow α₀ d)
          {x | HasStrictFit x}
        + gaussianSampleLaw d (enlargeBelow α₀ d) {x | ¬HasStrictFit x} := by
      rw [← hunion]
      exact measure_union_le _ _
    have hu : gaussianSampleLaw d (enlargeBelow α₀ d) Set.univ = 1 :=
      (inferInstance : IsProbabilityMeasure
        (gaussianSampleLaw d (enlargeBelow α₀ d))).measure_univ
    rw [hu] at hleU
    have hfinA : gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | HasStrictFit x} ≠ ⊤ :=
      sampleLaw_ne_top _
    have hfinB : gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | ¬HasStrictFit x} ≠ ⊤ :=
      sampleLaw_ne_top _
    have h2 := ENNReal.toReal_mono
      ((ENNReal.add_ne_top).mpr ⟨hfinA, hfinB⟩) hleU
    rw [ENNReal.toReal_one, ENNReal.toReal_add hfinA hfinB] at h2
    exact h2
  have hP' : (1 : ℝ) - ε
      < (gaussianSampleLaw d (enlargeBelow α₀ d)
        {x | HasStrictFit x}).toReal := by
    linarith [h1, hPbad]
  have hmonoN := ENNReal.toReal_mono
    (sampleLaw_ne_top {x : Sample d (n d) | HasStrictFit x})
    (measure_strictFit_mono hnd)
  have hPn : (1 : ℝ) - ε
      < (gaussianSampleLaw d (n d) {x | HasStrictFit x}).toReal :=
    lt_of_lt_of_le hP' hmonoN
  have hPle1 : (gaussianSampleLaw d (n d) {x | HasStrictFit x}).toReal ≤ 1 := by
    have h2 := ENNReal.toReal_mono ENNReal.one_ne_top
      (prob_le_one (μ := gaussianSampleLaw d (n d))
        (s := {x : Sample d (n d) | HasStrictFit x}))
    rwa [ENNReal.toReal_one] at h2
  show dist (strictFitProbability d (n d)) 1 < ε
  have hdist : dist (strictFitProbability d (n d)) 1
      = 1 - (gaussianSampleLaw d (n d) {x | HasStrictFit x}).toReal := by
    show |strictFitProbability d (n d) - 1| = _
    have hP : strictFitProbability d (n d)
        = (gaussianSampleLaw d (n d) {x | HasStrictFit x}).toReal := rfl
    rw [hP, abs_of_nonpos (sub_nonpos.mpr hPle1)]
    ring
  rw [hdist]
  linarith [hPn]

end GaussianEllipsoid
