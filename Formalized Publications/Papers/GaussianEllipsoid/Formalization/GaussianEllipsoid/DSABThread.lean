/-
DSABCand: (A,B)-generalized twins of the Davidson–Szarek consumers.

The exact (4,4) covariance premise `davidsonSzarekCovariance` (BelowObjects)
is unreachable on the net route, but every downstream consumer is
constant-agnostic. This file proves mechanical (4,4)→(A,B) twins of the
HuberDischarge consumers on top of the generalized premise
`davidsonSzarekCovariance_gen A B` (DSClassical §6, shape `A√(d/n)+B(d/n)`,
budget `2e^{-d/2}`), then instantiates them with the classical constants
(450/97, 900/97) proved from `dsPerCenterTail` alone.

Contents:
1. `covC_gen` — generalized covariance-good threshold.
2. `tendsto_sqrt_mul_covC_gen` — `√d·C_gen(d) → A/√α₀`.
3. `eventually_sqrt_mul_covC_le_gen` — eventual bound `A/√α₀ + 1`.
4. `deletedCovariance_uniform_tail_gen` — uniform deleted-covariance tail.
5. `cov_good_tail_quarter_gen` — covariance good-event tail at `t=1/4, v=2d`.
6. `huberResiduals_theorem_gen` — Section 4 conclusion from the gen premise.
7. `huberResiduals_of_classical` — end-to-end `dsPerCenterTail → HuberResiduals`.
-/

import GaussianEllipsoid.HuberDischarge
import GaussianEllipsoid.DSClassical
import GaussianEllipsoid.DSPerCenter
import GaussianEllipsoid.SelectorMeasurable
import GaussianEllipsoid.HansonWright

noncomputable section

open scoped Matrix Matrix.Norms.Frobenius ENNReal Topology

namespace GaussianEllipsoid

/-! ### (1) Generalized covariance-good threshold -/

/-- Covariance-good threshold `C_gen(d)` from `cov_good_tail_quarter_gen`:
copy of `covC` (HuberDischarge) with `(4·√… + 4·…)` replaced by
`(A·√… + B·…)`. -/
def covC_gen (A B : ℝ) (n : ℕ → ℕ) (d : ℕ) : ℝ :=
  (n d : ℝ) / ((n d : ℝ) - 1)
      * (A * Real.sqrt ((d : ℝ) / (n d : ℝ)) + B * (d : ℝ) / (n d : ℝ))
    + (1 / ((n d : ℝ) - 1)) * (1 + 2 * (d : ℝ))

/-! ### (2) Generalized `√d·C(d)` limit -/

/-- `√d·C_gen(d) → A/√α₀`: main term `√d·(n/(n-1))·A√(d/n)` plus vanishing
pieces. Copy of `tendsto_sqrt_mul_covC` with limit `A / Real.sqrt α₀`.

Re-derivation of the second-order coefficient: the original `6` is the sum of
the linear-term coefficient (`B = 4`, from `√d·(n/(n-1))·B·(d/n)`, i.e.
`B·(n/(n-1))·((d/√n)·√(d/n))`) and the chi-square-part coefficient (`2`, from
`√d·(1/(n-1))·2d = 2·(n/(n-1))·((d/√n)·√(d/n))`). Both are multiples of
`(n/(n-1))·((d/√n)·√(d/n)) → 1·0`, so in general the coefficient is `(B + 2)`.
The final `linear_combination` coefficients are the same shape with the new
scalars `-A` and `-(B+2)`. -/
theorem tendsto_sqrt_mul_covC_gen (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Filter.Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀)) :
    Filter.Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) * covC_gen A B n d)
      Filter.atTop (nhds (A / Real.sqrt α₀)) := by
  have hNdiv := GGlue.tendsto_n_div_pred hα hlim
  have hDsqrt := GGlue.tendsto_div_sqrt hα hn hlim
  have hSsqrt := GGlue.tendsto_sqrt_d_div_n hα hn hlim
  have hDpred := GGlue.tendsto_d_div_pred hα hn hlim
  have hgood := GGlue.eventually_good_index hα hn hlim
  have hAmul : Filter.Tendsto
      (fun d : ℕ => A * ((d : ℝ) / Real.sqrt (n d : ℝ)))
      Filter.atTop (nhds (A * (1 / Real.sqrt α₀))) :=
    Filter.Tendsto.const_mul A hDsqrt
  have hMain : Filter.Tendsto
      (fun d : ℕ => (n d : ℝ) / ((n d : ℝ) - 1)
        * (A * ((d : ℝ) / Real.sqrt (n d : ℝ))))
      Filter.atTop (nhds (A / Real.sqrt α₀)) := by
    have hmul := hNdiv.mul hAmul
    have heq : (1 : ℝ) * (A * (1 / Real.sqrt α₀)) = A / Real.sqrt α₀ := by ring
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
      (fun d : ℕ => (B + 2) * ((n d : ℝ) / ((n d : ℝ) - 1))
        * (((d : ℝ) / Real.sqrt (n d : ℝ))
          * Real.sqrt ((d : ℝ) / (n d : ℝ))))
      Filter.atTop (nhds 0) := by
    have h61 : Filter.Tendsto
        (fun d : ℕ => (B + 2) * ((n d : ℝ) / ((n d : ℝ) - 1)))
        Filter.atTop (nhds ((B + 2) * 1)) :=
      Filter.Tendsto.const_mul (B + 2) hNdiv
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
          * (A * ((d : ℝ) / Real.sqrt (n d : ℝ)))
        + (B + 2) * ((n d : ℝ) / ((n d : ℝ) - 1))
          * (((d : ℝ) / Real.sqrt (n d : ℝ))
            * Real.sqrt ((d : ℝ) / (n d : ℝ)))
        + Real.sqrt (d : ℝ) / ((n d : ℝ) - 1))
      Filter.atTop (nhds (A / Real.sqrt α₀)) := by
    have hadd := (hMain.add hTU).add hV
    have heq : A / Real.sqrt α₀ + 0 + 0 = A / Real.sqrt α₀ := by ring
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
  show (n d : ℝ) / ((n d : ℝ) - 1) * (A * ((d : ℝ) / Real.sqrt (n d : ℝ)))
      + (B + 2) * ((n d : ℝ) / ((n d : ℝ) - 1))
        * (((d : ℝ) / Real.sqrt (n d : ℝ))
          * Real.sqrt ((d : ℝ) / (n d : ℝ)))
      + Real.sqrt (d : ℝ) / ((n d : ℝ) - 1)
    = Real.sqrt (d : ℝ) * covC_gen A B n d
  unfold covC_gen
  rw [hdiv]
  field_simp
  linear_combination (-A * Real.sqrt (n d : ℝ) * (n d : ℝ)) * hsqd2
    + (-(B + 2) * Real.sqrt (d : ℝ) * (d : ℝ)) * hsqn2

/-! ### (3) Generalized eventual boundedness -/

/-- Eventual boundedness: `√d·C_gen(d) ≤ A/√α₀+1`.
Copy of `eventually_sqrt_mul_covC_le`. -/
theorem eventually_sqrt_mul_covC_le_gen (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    {n : ℕ → ℕ} {α₀ : ℝ} (hα : 0 < α₀)
    (hn : ∀ d : ℕ, 0 < n d)
    (hlim : Filter.Tendsto (fun d : ℕ => (n d : ℝ) / (d : ℝ) ^ 2)
      Filter.atTop (nhds α₀)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      Real.sqrt (d : ℝ) * covC_gen A B n d ≤ A / Real.sqrt α₀ + 1 := by
  have hT := tendsto_sqrt_mul_covC_gen A B hA hB hα hn hlim
  exact hT.eventually
    (eventually_le_nhds
      (show (A / Real.sqrt α₀) < A / Real.sqrt α₀ + 1 by linarith))

/-! ### (4) Generalized uniform deleted-covariance tail -/

/-- Uniform tail for the deleted covariance error (paper Section 4:
`C_d = max_j ‖Σ̂_{-j} - I‖_op`), combining the generalized
Davidson–Szarek covariance concentration with the chi-square row-norm
union bound. Copy of `deletedCovariance_uniform_tail` taking
`davidsonSzarekCovariance_gen A B`; only the DS instantiation and the
threshold algebra change. -/
theorem deletedCovariance_uniform_tail_gen (A B : ℝ) {d n : Nat}
    (hd : 0 < d) (hn : 1 < n)
    (hdn : (d : ℝ) ≤ (n : ℝ)) {t v : Real} (ht0 : 0 < t) (ht : t < 1 / 2)
    (hv : 0 ≤ v) (hDSgen : davidsonSzarekCovariance_gen A B) :
    ((gaussianSampleLaw d n)
      {x | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1))
        * (A * Real.sqrt ((d : ℝ) / (n : ℝ)) + B * (d : ℝ) / (n : ℝ))
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
      {x | A * Real.sqrt ((d : ℝ) / (n : ℝ)) + B * (d : ℝ) / (n : ℝ)
        < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2) :=
    hDSgen d n hd hn0 hdn
  have hB' : ((gaussianSampleLaw d n)
      (⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2})).toReal
      ≤ (n : ℝ)
        * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) :=
    rowNormSq_union_tail ht0 ht hv
  set u : Real :=
    A * Real.sqrt ((d : ℝ) / (n : ℝ)) + B * (d : ℝ) / (n : ℝ) with hu_def
  set Aev : Set (Sample d n) :=
    {x | u < matrixOpNorm (sampleCovariance x - 1)} with hA_def
  set Bev : Set (Sample d n) :=
    ⋃ j : Fin n, {x | v < ∑ k, ((x j) k) ^ 2} with hB_def
  have hsub : {x : Sample d n | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1)) * u
        + (1 / ((n : ℝ) - 1)) * (1 + v)
        < matrixOpNorm (deletedCovariance x j - 1)} ⊆ Aev ∪ Bev := by
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
      ≤ (gaussianSampleLaw d n) Aev + (gaussianSampleLaw d n) Bev :=
    le_trans (MeasureTheory.measure_mono hsub)
      (MeasureTheory.measure_union_le Aev Bev)
  have hAfin : (gaussianSampleLaw d n) Aev ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  have hBfin : (gaussianSampleLaw d n) Bev ≠ ∞ :=
    (MeasureTheory.measure_lt_top _ _).ne
  calc ((gaussianSampleLaw d n)
          {x : Sample d n | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1)) * u
            + (1 / ((n : ℝ) - 1)) * (1 + v)
            < matrixOpNorm (deletedCovariance x j - 1)}).toReal
      ≤ ((gaussianSampleLaw d n) Aev + (gaussianSampleLaw d n) Bev).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hAfin, hBfin⟩) hμ
    _ = ((gaussianSampleLaw d n) Aev).toReal
          + ((gaussianSampleLaw d n) Bev).toReal :=
        ENNReal.toReal_add hAfin hBfin
    _ ≤ 2 * Real.exp (-(d : ℝ) / 2)
          + (n : ℝ)
            * (Real.exp (-t * v) * (1 / Real.sqrt (1 - 2 * t)) ^ d) :=
        add_le_add hDS' hB'

/-! ### (5) Generalized covariance good-event tail at `t = 1/4`, `v = 2d` -/

/-- Covariance good-event tail at `t = 1/4`, `v = 2d`: direct instance of
`deletedCovariance_uniform_tail_gen`. The threshold is stated in the
expanded form matching `covC_gen A B` syntactically after unfolding, so
the downstream use at `covC_gen A B n d` holds by defeq (exactly as the
original `cov_good_tail_quarter` matches `covC`). -/
theorem cov_good_tail_quarter_gen (A B : ℝ) {d n : Nat} (hd : 0 < d)
    (hn : 1 < n)
    (hdn : (d : ℝ) ≤ (n : ℝ)) (hDSgen : davidsonSzarekCovariance_gen A B) :
    ((gaussianSampleLaw d n)
      {x | ∃ j : Fin n, ((n : ℝ) / ((n : ℝ) - 1))
        * (A * Real.sqrt ((d : ℝ) / (n : ℝ)) + B * (d : ℝ) / (n : ℝ))
        + (1 / ((n : ℝ) - 1)) * (1 + 2 * (d : ℝ))
        < matrixOpNorm (deletedCovariance x j - 1)}).toReal
      ≤ 2 * Real.exp (-(d : ℝ) / 2)
        + (n : ℝ)
          * (Real.exp (-(1 / 4) * (2 * (d : ℝ)))
            * (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d) := by
  exact deletedCovariance_uniform_tail_gen A B hd hn hdn (t := 1 / 4)
    (v := 2 * (d : ℝ)) (by norm_num) (by norm_num) (by positivity) hDSgen

/-! ### (6) Generalized Section 4 conclusion -/

/-- Section 4 conclusion (main-proposition-3-1) in dual-norm form from the
generalized Davidson–Szarek premise: the dual mixed norm of every Huber
minimizer's centered residuals tends to zero in probability. Copy of
`huberResiduals_theorem` with `covC → covC_gen A B`,
`cov_good_tail_quarter → _gen`, `eventually_sqrt_mul_covC_le → _gen`, and
every `4/√α₀`-derived numeric bound re-derived for `A/√α₀`. Same
conclusion shape (`HuberResiduals`). -/
theorem huberResiduals_theorem_gen (A B : ℝ) (hA : 0 < A) (hB : 0 ≤ B)
    (hDSgen : davidsonSzarekCovariance_gen A B)
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
    set Kbar : ℝ := hi * (A / Real.sqrt α₀ + 1) + (Real.sqrt 2 + 2) + 1
      with hKbar_def
    have hKbar_pos : 0 < Kbar := by
      rw [hKbar_def]
      have h1 : 0 < A / Real.sqrt α₀ + 1 := by
        have hdiv : 0 < A / Real.sqrt α₀ :=
          div_pos hA hsqrt_a0_pos
        linarith
      have h2 : 0 < hi * (A / Real.sqrt α₀ + 1) := mul_pos hhi_pos h1
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
    have h_sqrt_cov := eventually_sqrt_mul_covC_le_gen A B hA hB hα0 hn hconv
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
    have h_sqrt_mul_atTop : Filter.Tendsto
        (fun d : ℕ => (ε * η / 4) * Real.sqrt (d : ℝ))
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
    have hKle : Real.sqrt (d : ℝ) * hi * covC_gen A B n d +
        (Real.sqrt (2 * bmGoodR d (n d) lo hi epsp) +
          2 * bmGoodR d (n d) lo hi epsp) ≤ Kbar := by
      have hsqrt_le : Real.sqrt (d : ℝ) * covC_gen A B n d
          ≤ A / Real.sqrt α₀ + 1 :=
        hd_sqrt
      have hhi_nn : 0 ≤ hi := le_of_lt hhi_pos
      have hmain : Real.sqrt (d : ℝ) * hi * covC_gen A B n d
          ≤ hi * (A / Real.sqrt α₀ + 1) := by
        have heq : Real.sqrt (d : ℝ) * hi * covC_gen A B n d =
            hi * (Real.sqrt (d : ℝ) * covC_gen A B n d) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left hsqrt_le hhi_nn
      have h2R_le : 2 * bmGoodR d (n d) lo hi epsp ≤ 2 := by
        linarith [hR_le1]
      have hsqrt_le2 : Real.sqrt (2 * bmGoodR d (n d) lo hi epsp)
          ≤ Real.sqrt 2 :=
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
          {x | ∃ j : Fin (n d), covC_gen A B n d <
            matrixOpNorm (deletedCovariance x j - 1)}).toReal
        ≤ 2 * Real.exp (-(d : ℝ) / 2) + (n d : ℝ) *
          (Real.exp (-(1 / 4) * (2 * (d : ℝ))) *
            (1 / Real.sqrt (1 - 2 * (1 / 4))) ^ d) :=
      cov_good_tail_quarter_gen A B hd0 hn1 hdn hDSgen
    have hcov_le8 : ((gaussianSampleLaw d (n d))
          {x | ∃ j : Fin (n d), covC_gen A B n d <
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
      {x | ∀ j : Fin (n d), matrixOpNorm (deletedCovariance x j - 1)
        ≤ covC_gen A B n d}
      with hGood_def
    have hC : ∀ x ∈ Good, ∀ j : Fin (n d),
        matrixOpNorm (deletedCovariance x j - 1) ≤ covC_gen A B n d := by
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
          {x | ∃ j : Fin (n d), covC_gen A B n d <
            matrixOpNorm (deletedCovariance x j - 1)}) := by
      intro x hx
      simp only [hGood_def, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_union, Set.mem_ofPred_eq] at hx ⊢
      obtain ⟨_, hxG⟩ := hx
      by_cases hleft : bmMinRisk d (n d) x lo hi 1 < epsp
      · have hnot : ¬∀ j : Fin (n d),
            matrixOpNorm (deletedCovariance x j - 1) ≤ covC_gen A B n d := by
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
        {x | ∃ j : Fin (n d), covC_gen A B n d <
          matrixOpNorm (deletedCovariance x j - 1)})
      hsplit_subset
    have hbad_le := gaussian_union_toReal_le
      ({x : Sample d (n d) | epsp ≤ bmMinRisk d (n d) x lo hi 1})
      ({x : Sample d (n d) | ∃ j : Fin (n d), covC_gen A B n d <
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

/-! ### (7) End-to-end: classical constants from `dsPerCenterTail` -/

/-- End-to-end Section 4 conclusion from the per-center tail alone:
instantiate the generalized theorem with the classical constants
`A = 450/97`, `B = 900/97` via `dsClassicalCovariance_gen`, with
positivity from `dsClassicalAB_pos`. Conclusion matches the original
`huberResiduals_theorem` exactly (`HuberResiduals`). -/
theorem huberResiduals_of_classical (hpc : dsPerCenterTail)
    (hDel : deletedSelectorMeasurable)
    (hHW : hansonWrightChaos) : HuberResiduals := by
  obtain ⟨hA, hB⟩ := dsClassicalAB_pos
  exact huberResiduals_theorem_gen (450 / 97) (900 / 97) hA hB
    (dsClassicalCovariance_gen hpc) hDel hHW

/-- Fully unconditional Section 4 conclusion: the per-center tail
(`dsPerCenterTail_theorem`), the deleted selector
(`deletedSelectorMeasurable_theorem`), and the chaos bound
(`hansonWrightChaos_theorem`) are all proved, so neither
`davidsonSzarekCovariance` nor `hansonWrightChaos` remains as a premise. -/
theorem huberResiduals_unconditional : HuberResiduals :=
  huberResiduals_of_classical dsPerCenterTail_theorem
    deletedSelectorMeasurable_theorem hansonWrightChaos_theorem

end GaussianEllipsoid
