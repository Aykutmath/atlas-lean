/-
Davidson–Szarek per-center tail (Laurent–Massart for one direction).

Proves the source-text `dsPerCenterTail` (DSCovariance.lean:47-51,
restated as `dsPerCenterTailSrc` since the prebuilt olean is stale)
modulo three explicit gaps: Gaussian marginal stability of row inner products
(`dsGap_marginal`, the rotation-invariance consequence), and two
single-variable log inequalities (`dsGap_logLower`, `dsGap_logUpper`).

Route: quadratic(Σ̂−I)w is the average of `((xᵢ⬝ᵥw)²−1)` (proved);
transport along the gap-A joint law to `n` i.i.d. scalars (proved);
sharp 1-D Laurent–Massart via repo MGF values (`mgf_normSq`) plus
`hw_chernoff` in both tails with the exact Laurent–Massart parameters
(proved); union bound assembly (proved).
-/
import Mathlib
import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.Coordinates
import GaussianEllipsoid.Discretize
import GaussianEllipsoid.ExactFit
import GaussianEllipsoid.GaussianProbability
import GaussianEllipsoid.HansonWright
import GaussianEllipsoid.DSCovariance
import GaussianEllipsoid.RotAssemble

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

/-- Row inner products against a fixed direction. -/
def dsInner (d n : ℕ) (w : Vector d) : Sample d n → Fin n → ℝ :=
  fun x i => dotProduct (x i) w

/-- Centered chi-square sum over `n` scalar observations. -/
def dsSumC (n : ℕ) : (Fin n → ℝ) → ℝ :=
  fun y => ∑ i, ((y i) ^ 2 - 1)

/-- Gap A (marginal stability): for unit `w`, the `n` row inner products
are i.i.d. standard Gaussian. Intended route: Householder reflection
sending `w` to `e₁`, `gaussianVectorLaw_rotation_uncond`, row independence. -/
def dsGap_marginal : Prop :=
  ∀ (d n : ℕ) (w : Vector d), euclidNorm w = 1 →
    Measure.map (dsInner d n w) (gaussianSampleLaw d n)
      = Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- Gap B (lower-tail calculus): `log(1+2s) ≥ 2s−2s²` on `[0,1]`.
Paper proof: `g(0)=0` and `g'(s)=8s²/(1+2s) ≥ 0`. -/
def dsGap_logLower : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 2 * s - 2 * s ^ 2 ≤ Real.log (1 + 2 * s)

/-- Gap C (upper-tail calculus): `log(1+2s+2s²) ≤ 2s` on `[0,1]`.
Paper proof: `f(0)=0` and `f'(s)=4s²/(1+2s+2s²) ≥ 0`. -/
def dsGap_logUpper : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ 1 → Real.log (1 + 2 * s + 2 * s ^ 2) ≤ 2 * s

/- `dsPerCenterTailSrc` (helper-local restatement) is repo
`DSCovariance.dsPerCenterTail` (byte-identical statement); the olean is
fresh after main's rebuild, so the repo def is used directly. -/

theorem dsCard_one (n : ℕ) : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem dsCard_neg_one (n : ℕ) : (∑ _i : Fin n, (-1 : ℝ)) = -(n : ℝ) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg,
    mul_one]

theorem dsSumC_sub (n : ℕ) (y : Fin n → ℝ) :
    dsSumC n y = (∑ j, (y j) ^ 2) - (n : ℝ) := by
  show (∑ i, ((y i) ^ 2 - 1)) = (∑ j, (y j) ^ 2) - (n : ℝ)
  rw [Finset.sum_sub_distrib, dsCard_one]

theorem dsSumC_continuous (n : ℕ) : Continuous (dsSumC n) := by
  show Continuous fun y : Fin n → ℝ => ∑ i, ((y i) ^ 2 - 1)
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).pow 2).sub continuous_const)

/-- The per-center quadratic form is the average of centered squared
inner products. -/
theorem dsQuad_avg {d n : ℕ} (x : Sample d n) (w : Vector d)
    (hw : euclidNorm w = 1) (hn : 0 < n) :
    quadratic (sampleCovariance x - 1) w
      = ((n : ℝ))⁻¹ * ∑ i, ((dotProduct (x i) w) ^ 2 - 1) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hww : dotProduct w w = 1 := by
    rw [dotProduct_self_eq_euclidNorm_sq, hw]
    norm_num
  have hGram : sampleCovariance x = ((n : ℝ))⁻¹ • gram x := rfl
  have hsplit : (∑ i, ((dotProduct (x i) w) ^ 2 - 1))
      = (∑ i, (dotProduct (x i) w) ^ 2) - (n : ℝ) := by
    rw [Finset.sum_sub_distrib, dsCard_one]
  calc quadratic (sampleCovariance x - 1) w
      = quadratic (((n : ℝ))⁻¹ • gram x) w - quadratic 1 w := by
        rw [hGram, quadratic_sub]
    _ = ((n : ℝ))⁻¹ * quadratic (gram x) w - dotProduct w w := by
        rw [quadratic_smul, quadratic_one]
    _ = ((n : ℝ))⁻¹ * (∑ i, (dotProduct (x i) w) ^ 2) - 1 := by
        rw [quadratic_gram, hww]
    _ = ((n : ℝ))⁻¹ * ∑ i, ((dotProduct (x i) w) ^ 2 - 1) := by
        rw [hsplit, mul_sub, inv_mul_cancel₀ hn0]

theorem dsInner_measurable {d n : ℕ} (w : Vector d) :
    Measurable (dsInner d n w) := by
  have heq : ∀ i : Fin n, (fun x : Sample d n => dotProduct (x i) w)
      = (fun x => ∑ j, (x i j) * (w j)) := by
    intro i
    funext x
    simp only [dotProduct]
  refine measurable_pi_lambda (dsInner d n w) (fun i => ?_)
  show Measurable (fun x : Sample d n => dotProduct (x i) w)
  rw [heq i]
  exact Finset.measurable_sum _ (fun j _ =>
    Measurable.mul ((measurable_pi_apply j).comp (measurable_pi_apply i))
      measurable_const)

/-- 1-D Laurent–Massart upper tail at `u = 2s+2s²`, `s² = x/n`,
via Chernoff with `λ = u/(2(u+1))`. -/
theorem dsUpper_tail (n : ℕ) (hn : 0 < n) (s u lam x : ℝ)
    (hs0 : 0 < s) (hs2 : s ^ 2 = x / (n : ℝ))
    (hu : u = 2 * s + 2 * s ^ 2) (hlam : lam = u / (2 * (u + 1)))
    (hC : dsGap_logUpper) :
    (gaussianVectorLaw n) {y | (n : ℝ) * u ≤ dsSumC n y}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsn : 0 ≤ s := le_of_lt hs0
  have hu0 : 0 < u := by
    have h1 : (0 : ℝ) < 2 * s := by linarith
    have h2 : (0 : ℝ) ≤ 2 * s ^ 2 := mul_nonneg (by norm_num) (sq_nonneg s)
    rw [hu]
    linarith
  have hu1 : (0 : ℝ) < u + 1 := by linarith
  have h1u0 : (u : ℝ) + 1 ≠ 0 := ne_of_gt hu1
  have h2u0 : (2 : ℝ) * (u + 1) ≠ 0 := mul_ne_zero (by norm_num) h1u0
  have hlam0 : 0 < lam := by
    rw [hlam]
    exact div_pos hu0 (mul_pos (by norm_num) hu1)
  have hlamU : lam * (2 * (u + 1)) = u := by
    rw [hlam]
    exact div_mul_cancel₀ _ h2u0
  have hlamU' : lam * (u + 1) = u / 2 := by linarith [hlamU]
  have hlam05 : lam < 1 / 2 := by
    rw [hlam, div_lt_iff₀ (mul_pos (by norm_num) hu1)]
    linarith
  have h2 : 2 * (lam * (u + 1)) = u := by linarith [hlamU]
  have hP : (1 - 2 * lam) * (u + 1) = 1 := by linarith [h2]
  have h1m2 : (1 : ℝ) - 2 * lam = 1 / (u + 1) := by
    rw [eq_div_iff h1u0]
    exact hP
  have h1m2pos : (0 : ℝ) < 1 - 2 * lam := by
    rw [h1m2]
    exact div_pos one_pos hu1
  have hlog1m2 : Real.log (1 - 2 * lam) = -Real.log (u + 1) := by
    rw [h1m2, one_div, Real.log_inv]
  have hlogcore : Real.log (u + 1) ≤ 2 * s := by
    have e1 : (u : ℝ) + 1 = 1 + 2 * s + 2 * s ^ 2 := by rw [hu]; ring
    rw [e1]
    by_cases hs1 : s ≤ 1
    · exact hC s hsn hs1
    · push_neg at hs1
      have hA0 : (0 : ℝ) < 1 + 2 * s + 2 * s ^ 2 := by
        have g1 : (0 : ℝ) ≤ 2 * s := by linarith [hsn]
        have g2 : (0 : ℝ) ≤ 2 * s ^ 2 := mul_nonneg (by norm_num) (sq_nonneg s)
        linarith
      have hBup : (1 : ℝ) + 2 * s + 2 * s ^ 2 ≤ 5 * s ^ 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ s - 1 by linarith)
          (show (0 : ℝ) ≤ 3 * s + 1 by linarith [hsn])]
      have h5s0 : (0 : ℝ) < 5 * s ^ 2 := mul_pos (by norm_num) (pow_pos hs0 2)
      have hle : Real.log (1 + 2 * s + 2 * s ^ 2) ≤ Real.log (5 * s ^ 2) :=
        Real.log_le_log hA0 hBup
      have hln5s : Real.log (5 * s ^ 2) = Real.log 5 + 2 * Real.log s := by
        rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hs0 2)),
          pow_two, Real.log_mul hs0.ne' hs0.ne']
        ring
      have hlog5 : Real.log 5 ≤ 2 := by
        have h271 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have he2 : (5 : ℝ) < (Real.exp 1) ^ 2 := by
          nlinarith [h271, sq_nonneg (Real.exp 1 - 2.7)]
        have hexp2 : (Real.exp 1) ^ 2 = Real.exp 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          norm_num
        have h5e : (5 : ℝ) ≤ Real.exp 2 := by
          rw [← hexp2]
          linarith [he2]
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 5) h5e
        rw [Real.log_exp] at h
        exact h
      have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
      linarith [hle, hln5s, hlog5, hlogs]
  have hcore : (u - Real.log (u + 1)) / 2 ≥ s ^ 2 := by
    have e2 : u - 2 * s ^ 2 = 2 * s := by rw [hu]; ring
    linarith [hlogcore, e2]
  have hx : x = (n : ℝ) * s ^ 2 := by
    have h := (eq_div_iff hn0).mp hs2
    linarith [h]
  have hmgf_int : (∫ y, Real.exp (lam * (∑ j, (y j) ^ 2)) ∂(gaussianVectorLaw n))
      = (1 / Real.sqrt (1 - 2 * lam)) ^ n :=
    mgf_normSq_gaussianVector (d := n) (t := lam) hlam05
  have hintQ : Integrable (fun y : Vector n => Real.exp (lam * (∑ j, (y j) ^ 2)))
      (gaussianVectorLaw n) :=
    integrable_exp_normSq_gaussianVector (d := n) (t := lam) hlam05
  have hpt : ∀ y : Vector n,
      Real.exp (lam * dsSumC n y)
        = Real.exp (-lam * (n : ℝ)) * Real.exp (lam * (∑ j, (y j) ^ 2)) := by
    intro y
    have hSQ := dsSumC_sub n y
    rw [hSQ]
    have hrw : lam * ((∑ j, (y j) ^ 2) - (n : ℝ))
        = -lam * (n : ℝ) + lam * (∑ j, (y j) ^ 2) := by ring
    rw [hrw, Real.exp_add]
  have hintU : Integrable (fun y : Vector n => Real.exp (lam * dsSumC n y))
      (gaussianVectorLaw n) := by
    have hfun : (fun y : Vector n => Real.exp (lam * dsSumC n y))
        = (fun y => Real.exp (-lam * (n : ℝ))
          * Real.exp (lam * (∑ j, (y j) ^ 2))) :=
      funext hpt
    rw [hfun]
    exact hintQ.const_mul _
  set Bup : ℝ := Real.exp (-lam * (n : ℝ)) * ((1 / Real.sqrt (1 - 2 * lam)) ^ n)
    with hBup
  have hmgfU : (∫ y, Real.exp (lam * dsSumC n y) ∂(gaussianVectorLaw n))
      ≤ Bup := by
    have hEq : (∫ y, Real.exp (lam * dsSumC n y) ∂(gaussianVectorLaw n))
        = Real.exp (-lam * (n : ℝ))
          * (∫ y, Real.exp (lam * (∑ j, (y j) ^ 2)) ∂(gaussianVectorLaw n)) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [hEq, hmgf_int]
  have hU := hw_chernoff (dsSumC_continuous n) (φ := lam) (u := (n : ℝ) * u)
    (B := Bup) hlam0 hintU hmgfU
  have hMvpos : (0 : ℝ) < 1 / Real.sqrt (1 - 2 * lam) :=
    div_pos one_pos (Real.sqrt_pos.mpr h1m2pos)
  have hMvnpos : (0 : ℝ) < (1 / Real.sqrt (1 - 2 * lam)) ^ n :=
    pow_pos hMvpos n
  have hlogpow : Real.log ((1 / Real.sqrt (1 - 2 * lam)) ^ n)
      = (n : ℝ) * Real.log (1 / Real.sqrt (1 - 2 * lam)) := Real.log_pow _ _
  have hpow : ((1 / Real.sqrt (1 - 2 * lam)) ^ n)
      = Real.exp ((n : ℝ) * Real.log (1 / Real.sqrt (1 - 2 * lam))) := by
    rw [← Real.exp_log hMvnpos, hlogpow]
  have hlogMv : Real.log (1 / Real.sqrt (1 - 2 * lam))
      = Real.log (u + 1) / 2 := by
    have hsq : Real.sqrt (1 - 2 * lam) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr h1m2pos)
    rw [Real.log_div one_ne_zero hsq, Real.log_one, Real.log_sqrt h1m2pos.le,
      hlog1m2]
    ring
  have hE : lam * ((n : ℝ) * u) + lam * (n : ℝ) = (n : ℝ) * (u / 2) := by
    have e : lam * ((n : ℝ) * u) + lam * (n : ℝ)
        = (n : ℝ) * (lam * (u + 1)) := by ring
    rw [e, hlamU']
  have hcoreN : (n : ℝ) * s ^ 2 ≤ (n : ℝ) * ((u - Real.log (u + 1)) / 2) :=
    mul_le_mul_of_nonneg_left hcore hnR.le
  have hana : Real.exp (-lam * ((n : ℝ) * u)) * Bup ≤ Real.exp (-x) := by
    have hLHS : Real.exp (-lam * ((n : ℝ) * u)) * Bup
        = Real.exp (-lam * ((n : ℝ) * u) + -lam * (n : ℝ)
          + (n : ℝ) * Real.log (1 / Real.sqrt (1 - 2 * lam))) := by
      rw [hBup, hpow, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hLHS]
    apply Real.exp_le_exp.mpr
    rw [hlogMv]
    linarith [hE, hcoreN, hx]
  calc (gaussianVectorLaw n) {y | (n : ℝ) * u ≤ dsSumC n y}
      ≤ ENNReal.ofReal (Real.exp (-lam * ((n : ℝ) * u)) * Bup) := hU
    _ ≤ ENNReal.ofReal (Real.exp (-x)) := ENNReal.ofReal_le_ofReal hana

/-- 1-D Laurent–Massart lower tail at `2s`, `s² = x/n`,
via Chernoff with `φ = s` (empty event when `s > 1/2`). -/
theorem dsLower_tail (n : ℕ) (hn : 0 < n) (s x : ℝ)
    (hs0 : 0 < s) (hs2 : s ^ 2 = x / (n : ℝ))
    (hB : dsGap_logLower) :
    (gaussianVectorLaw n) {y | (n : ℝ) * (2 * s) ≤ -dsSumC n y}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsn : 0 ≤ s := le_of_lt hs0
  have hx : x = (n : ℝ) * s ^ 2 := by
    have h := (eq_div_iff hn0).mp hs2
    linarith [h]
  by_cases hsbig : 1 / 2 < s
  · have hn2s : (n : ℝ) < (n : ℝ) * (2 * s) :=
      calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
        _ < (n : ℝ) * (2 * s) :=
          mul_lt_mul_of_pos_left (by linarith : (1 : ℝ) < 2 * s) hnR
    have hempty : {y : Vector n | (n : ℝ) * (2 * s) ≤ -dsSumC n y} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => by
        simp only [Set.mem_setOf_eq] at hy
        have hlow : ∀ i : Fin n, (-1 : ℝ) ≤ (y i) ^ 2 - 1 := by
          intro i
          have hsq := sq_nonneg (y i)
          linarith
        have hsum : (∑ _i : Fin n, (-1 : ℝ)) ≤ ∑ i, ((y i) ^ 2 - 1) :=
          Finset.sum_le_sum (fun i _ => hlow i)
        rw [dsCard_neg_one] at hsum
        have hSlow : -(n : ℝ) ≤ dsSumC n y := hsum
        linarith [hy, hSlow, hn2s])
    rw [hempty, measure_empty]
    exact zero_le
  · push_neg at hsbig
    have hts : -s < 1 / 2 := by linarith [hs0]
    have hmgf_int : (∫ y, Real.exp (-s * (∑ j, (y j) ^ 2))
        ∂(gaussianVectorLaw n))
        = (1 / Real.sqrt (1 + 2 * s)) ^ n := by
      have h := mgf_normSq_gaussianVector (d := n) (t := -s) hts
      have h1p2s : (1 : ℝ) - 2 * -s = 1 + 2 * s := by ring
      rw [h1p2s] at h
      exact h
    have hintQ : Integrable
        (fun y : Vector n => Real.exp (-s * (∑ j, (y j) ^ 2)))
        (gaussianVectorLaw n) :=
      integrable_exp_normSq_gaussianVector (d := n) (t := -s) hts
    have hpt : ∀ y : Vector n,
        Real.exp (s * -dsSumC n y)
          = Real.exp (s * (n : ℝ)) * Real.exp (-s * (∑ j, (y j) ^ 2)) := by
      intro y
      have hSQ := dsSumC_sub n y
      rw [hSQ]
      have hrw : s * -((∑ j, (y j) ^ 2) - (n : ℝ))
          = s * (n : ℝ) + -s * (∑ j, (y j) ^ 2) := by ring
      rw [hrw, Real.exp_add]
    have hintL : Integrable (fun y : Vector n => Real.exp (s * -dsSumC n y))
        (gaussianVectorLaw n) := by
      have hfun : (fun y : Vector n => Real.exp (s * -dsSumC n y))
          = (fun y => Real.exp (s * (n : ℝ))
            * Real.exp (-s * (∑ j, (y j) ^ 2))) :=
        funext hpt
      rw [hfun]
      exact hintQ.const_mul _
    set Blow : ℝ := Real.exp (s * (n : ℝ)) * ((1 / Real.sqrt (1 + 2 * s)) ^ n)
      with hBlow
    have hmgfL : (∫ y, Real.exp (s * -dsSumC n y) ∂(gaussianVectorLaw n))
        ≤ Blow := by
      have hEq : (∫ y, Real.exp (s * -dsSumC n y) ∂(gaussianVectorLaw n))
          = Real.exp (s * (n : ℝ))
            * (∫ y, Real.exp (-s * (∑ j, (y j) ^ 2))
              ∂(gaussianVectorLaw n)) := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      rw [hEq, hmgf_int]
    have hL := hw_chernoff ((dsSumC_continuous n).neg) (φ := s)
      (u := (n : ℝ) * (2 * s)) (B := Blow) hs0 hintL hmgfL
    have hMvpos : (0 : ℝ) < 1 / Real.sqrt (1 + 2 * s) :=
      div_pos one_pos
        (Real.sqrt_pos.mpr (by linarith [hsn] : (0 : ℝ) < 1 + 2 * s))
    have hMvnpos : (0 : ℝ) < (1 / Real.sqrt (1 + 2 * s)) ^ n :=
      pow_pos hMvpos n
    have hlogpow : Real.log ((1 / Real.sqrt (1 + 2 * s)) ^ n)
        = (n : ℝ) * Real.log (1 / Real.sqrt (1 + 2 * s)) := Real.log_pow _ _
    have hpow : ((1 / Real.sqrt (1 + 2 * s)) ^ n)
        = Real.exp ((n : ℝ) * Real.log (1 / Real.sqrt (1 + 2 * s))) := by
      rw [← Real.exp_log hMvnpos, hlogpow]
    have hlogMv : Real.log (1 / Real.sqrt (1 + 2 * s))
        = -Real.log (1 + 2 * s) / 2 := by
      have hsq : Real.sqrt (1 + 2 * s) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr (by linarith [hsn] : (0 : ℝ) < 1 + 2 * s))
      rw [Real.log_div one_ne_zero hsq, Real.log_one,
        Real.log_sqrt (by linarith [hsn] : (0 : ℝ) ≤ 1 + 2 * s)]
      ring
    have hBcore : 2 * s - 2 * s ^ 2 ≤ Real.log (1 + 2 * s) :=
      hB s hsn (by linarith : s ≤ 1)
    have hBn : ((n : ℝ) / 2) * (2 * s - 2 * s ^ 2)
        ≤ ((n : ℝ) / 2) * Real.log (1 + 2 * s) :=
      mul_le_mul_of_nonneg_left hBcore (by linarith [hnR.le])
    have hana : Real.exp (-s * ((n : ℝ) * (2 * s))) * Blow ≤ Real.exp (-x) := by
      have hLHS : Real.exp (-s * ((n : ℝ) * (2 * s))) * Blow
          = Real.exp (-s * ((n : ℝ) * (2 * s)) + s * (n : ℝ)
            + (n : ℝ) * Real.log (1 / Real.sqrt (1 + 2 * s))) := by
        rw [hBlow, hpow, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hLHS]
      apply Real.exp_le_exp.mpr
      rw [hlogMv]
      linarith [hBn, hx]
    calc (gaussianVectorLaw n) {y | (n : ℝ) * (2 * s) ≤ -dsSumC n y}
        ≤ ENNReal.ofReal (Real.exp (-s * ((n : ℝ) * (2 * s))) * Blow) := hL
      _ ≤ ENNReal.ofReal (Real.exp (-x)) := ENNReal.ofReal_le_ofReal hana

/-- The per-center tail from the three explicit gaps. -/
theorem dsPerCenterTail_of_gaps (hA : dsGap_marginal) (hB : dsGap_logLower)
    (hC : dsGap_logUpper) : dsPerCenterTail := by
  intro d n w hw hn t x hx ht
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hseteq : {z : Sample d n | t < |quadratic (sampleCovariance z - 1) w|}
      = (dsInner d n w) ⁻¹' {y : Vector n | t < |dsSumC n y / (n : ℝ)|} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have hq := dsQuad_avg z w hw hn
    have h1 : dsSumC n (dsInner d n w z)
        = ∑ i, ((dotProduct (z i) w) ^ 2 - 1) := rfl
    rw [hq]
    have h2 : dsSumC n (dsInner d n w z) / (n : ℝ)
        = ((n : ℝ))⁻¹ * ∑ i, ((dotProduct (z i) w) ^ 2 - 1) := by
      rw [h1]
      ring
    rw [h2]
  have hEmeas : MeasurableSet {y : Vector n | t < |dsSumC n y / (n : ℝ)|} :=
    measurableSet_lt measurable_const
      (((dsSumC_continuous n).measurable.div_const _).abs)
  have htrans : (gaussianSampleLaw d n)
      {z | t < |quadratic (sampleCovariance z - 1) w|}
      = (gaussianVectorLaw n) {y | t < |dsSumC n y / (n : ℝ)|} := by
    rw [hseteq, ← Measure.map_apply (dsInner_measurable w) hEmeas, hA d n w hw]
    rfl
  by_cases hx0 : x = 0
  · subst hx0
    rw [htrans]
    have hle1 : (gaussianVectorLaw n)
        {y : Vector n | t < |dsSumC n y / (n : ℝ)|} ≤ 1 :=
      calc (gaussianVectorLaw n) {y : Vector n | t < |dsSumC n y / (n : ℝ)|}
          ≤ (gaussianVectorLaw n) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have h12 : (1 : ℝ) ≤ 2 * Real.exp (-(0 : ℝ)) := by
      rw [neg_zero, Real.exp_zero]
      norm_num
    calc (gaussianVectorLaw n) {y : Vector n | t < |dsSumC n y / (n : ℝ)|}
        ≤ 1 := hle1
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(0 : ℝ))) :=
          ENNReal.ofReal_le_ofReal h12
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    set s : ℝ := Real.sqrt (x / (n : ℝ)) with hs
    set u : ℝ := 2 * s + 2 * s ^ 2 with hu
    set lam : ℝ := u / (2 * (u + 1)) with hlam
    have hsn : 0 ≤ s := Real.sqrt_nonneg _
    have hs0 : 0 < s := Real.sqrt_pos.mpr (div_pos hxpos hnR)
    have hs2 : s ^ 2 = x / (n : ℝ) :=
      Real.sq_sqrt (div_nonneg hx hnR.le)
    have hu_le : u ≤ t := by
      have h1 : u = 2 * s + 2 * (x / (n : ℝ)) := by rw [hu, hs2]
      have h2 : (2 : ℝ) * s + 2 * (x / (n : ℝ)) = 2 * s + 2 * x / (n : ℝ) := by
        ring
      rw [h1, h2]
      exact ht
    have hsub : {y : Vector n | t < |dsSumC n y / (n : ℝ)|}
        ⊆ {y : Vector n | (n : ℝ) * u ≤ dsSumC n y}
          ∪ {y : Vector n | (n : ℝ) * (2 * s) ≤ -dsSumC n y} := by
      intro y hy
      simp only [Set.mem_setOf_eq] at hy
      have habs : u ≤ |dsSumC n y / (n : ℝ)| := le_trans hu_le (le_of_lt hy)
      rw [le_abs] at habs
      simp only [Set.mem_union, Set.mem_setOf_eq]
      rcases habs with h | h
      · left
        have h2 : u * (n : ℝ) ≤ dsSumC n y := (le_div_iff₀ hnR).mp h
        linarith [h2]
      · right
        have h' : dsSumC n y / (n : ℝ) ≤ -u := by linarith [h]
        have h2 : dsSumC n y ≤ -u * (n : ℝ) := (div_le_iff₀ hnR).mp h'
        have hUn : u * (n : ℝ)
            = (n : ℝ) * (2 * s) + (n : ℝ) * (2 * s ^ 2) := by
          rw [hu]
          ring
        have hn2s2 : (0 : ℝ) ≤ (n : ℝ) * (2 * s ^ 2) :=
          mul_nonneg hnR.le (mul_nonneg (by norm_num) (sq_nonneg s))
        linarith [h2, hUn, hn2s2]
    have hU := dsUpper_tail n hn s u lam x hs0 hs2 hu hlam hC
    have hL := dsLower_tail n hn s x hs0 hs2 hB
    rw [htrans]
    have hfin : (gaussianVectorLaw n)
        {y : Vector n | t < |dsSumC n y / (n : ℝ)|}
        ≤ ENNReal.ofReal (Real.exp (-x)) + ENNReal.ofReal (Real.exp (-x)) :=
      (measure_mono hsub).trans
        ((measure_union_le _ _).trans (add_le_add hU hL))
    have hadd : ENNReal.ofReal (Real.exp (-x)) + ENNReal.ofReal (Real.exp (-x))
        = ENNReal.ofReal (2 * Real.exp (-x)) := by
      rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
      congr 1
      ring
    rw [hadd] at hfin
    exact hfin



/- Log-calculus gaps B+C (from DSLOGCand, exit-0): derivative-sign +
monotonicity on `[0,1]`. Only `dsGap_marginal` (lane 8) remains. -/

/-- Gap C (upper-tail calculus): `log(1+2s+2s²) ≤ 2s` on `[0,1]`.

Paper proof: `f(s) = 2s - log(1+2s+2s²)` has `f(0) = 0` and
`f'(s) = 4s²/(1+2s+2s²) ≥ 0`, so `f` is monotone on `[0,1]`. -/
theorem dsGap_logUpper_proof : dsGap_logUpper := by
  intro s hs0 hs1
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < 1 + 2 * t + 2 * t ^ 2 := by
    intro t ht
    obtain ⟨h0, -⟩ := Set.mem_Icc.mp ht
    have e1 : (0 : ℝ) ≤ 2 * t := by linarith
    have e2 : (0 : ℝ) ≤ 2 * t ^ 2 := by positivity
    linarith
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hpow : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    intro t
    simpa using hasDerivAt_pow 2 t
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (2 : ℝ) * t ^ 2) (4 * t) t := by
    intro t
    have h := (hpow t).const_mul (2 : ℝ)
    have hval : (2 : ℝ) * (2 * t) = 4 * t := by ring
    rw [hval] at h
    exact h
  have hinner : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (1 : ℝ) + 2 * t + 2 * t ^ 2) (2 + 4 * t) t := by
    intro t
    have h := ((hasDerivAt_const t (1 : ℝ)).add (h1 t)).add (h2 t)
    have hval : ((0 : ℝ) + 2) + 4 * t = 2 + 4 * t := by ring
    rw [hval] at h
    exact h
  have hHas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => 2 * t - Real.log (1 + 2 * t + 2 * t ^ 2))
        (4 * t ^ 2 / (1 + 2 * t + 2 * t ^ 2)) t := by
    intro t ht
    have hne : (1 : ℝ) + 2 * t + 2 * t ^ 2 ≠ 0 := ne_of_gt (hmem t ht)
    have h := (h1 t).sub ((hinner t).log hne)
    have hval : (2 : ℝ) - (2 + 4 * t) / (1 + 2 * t + 2 * t ^ 2)
        = 4 * t ^ 2 / (1 + 2 * t + 2 * t ^ 2) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ
        (fun t : ℝ => 2 * t - Real.log (1 + 2 * t + 2 * t ^ 2)) t :=
    fun t ht => (hHas t ht).differentiableAt
  have hnn : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      0 ≤ deriv (fun t : ℝ => 2 * t - Real.log (1 + 2 * t + 2 * t ^ 2)) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hHas t htIcc).deriv]
    have hpos := hmem t htIcc
    positivity
  have hmono : MonotoneOn
      (fun t : ℝ => 2 * t - Real.log (1 + 2 * t + 2 * t ^ 2))
      (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdiff t (interior_subset ht)).differentiableWithinAt)
      hnn
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hle := hmono h0 hs hs0
  have hle' : (0 : ℝ) ≤ 2 * s - Real.log (1 + 2 * s + 2 * s ^ 2) := by
    simpa using hle
  linarith

/-- Gap B (lower-tail calculus): `2s−2s² ≤ log(1+2s)` on `[0,1]`.

Paper proof: `g(s) = log(1+2s) - 2s + 2s²` has `g(0) = 0` and
`g'(s) = 8s²/(1+2s) ≥ 0`, so `g` is monotone on `[0,1]`. -/
theorem dsGap_logLower_proof : dsGap_logLower := by
  intro s hs0 hs1
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < 1 + 2 * t := by
    intro t ht
    obtain ⟨h0, -⟩ := Set.mem_Icc.mp ht
    have e1 : (0 : ℝ) ≤ 2 * t := by linarith
    linarith
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (2 : ℝ) * t) 2 t := by
    intro t
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hpow : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
    intro t
    simpa using hasDerivAt_pow 2 t
  have h2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (2 : ℝ) * t ^ 2) (4 * t) t := by
    intro t
    have h := (hpow t).const_mul (2 : ℝ)
    have hval : (2 : ℝ) * (2 * t) = 4 * t := by ring
    rw [hval] at h
    exact h
  have hinner : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 : ℝ) + 2 * t) 2 t := by
    intro t
    have h := (hasDerivAt_const t (1 : ℝ)).add (h1 t)
    have hval : (0 : ℝ) + 2 = 2 := by ring
    rw [hval] at h
    exact h
  have hHas : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Real.log (1 + 2 * t) - 2 * t + 2 * t ^ 2)
        (8 * t ^ 2 / (1 + 2 * t)) t := by
    intro t ht
    have hne : (1 : ℝ) + 2 * t ≠ 0 := ne_of_gt (hmem t ht)
    have h := (((hinner t).log hne).sub (h1 t)).add (h2 t)
    have hval : (2 / (1 + 2 * t) - 2) + 4 * t = 8 * t ^ 2 / (1 + 2 * t) := by
      field_simp
      ring
    rw [hval] at h
    exact h
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ
        (fun t : ℝ => Real.log (1 + 2 * t) - 2 * t + 2 * t ^ 2) t :=
    fun t ht => (hHas t ht).differentiableAt
  have hnn : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      0 ≤ deriv (fun t : ℝ => Real.log (1 + 2 * t) - 2 * t + 2 * t ^ 2) t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hHas t htIcc).deriv]
    have hpos := hmem t htIcc
    positivity
  have hmono : MonotoneOn
      (fun t : ℝ => Real.log (1 + 2 * t) - 2 * t + 2 * t ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hdiff t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hdiff t (interior_subset ht)).differentiableWithinAt)
      hnn
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0, hs1⟩
  have hle := hmono h0 hs hs0
  have hle' : (0 : ℝ) ≤ Real.log (1 + 2 * s) - 2 * s + 2 * s ^ 2 := by
    simpa using hle
  linarith

/-- Per-center tail from the marginal gap alone (log gaps discharged). -/
theorem dsPerCenterTail_of_marginal (hA : dsGap_marginal) : dsPerCenterTail :=
  dsPerCenterTail_of_gaps hA dsGap_logLower_proof dsGap_logUpper_proof


/- Marginal gap A (from DSMARGCand, exit-0): single-row N(0,1)
marginal via Householder + unconditional rotation invariance, joint
law via row independence. This closes the last per-center gap. -/

/-- Measurability of a single-row inner product against a fixed direction. -/
theorem dsInnerSingle_measurable {d : ℕ} (w : Vector d) :
    Measurable (fun z : Vector d => dotProduct z w) := by
  have heq : (fun z : Vector d => dotProduct z w)
      = (fun z => ∑ j, (z j) * (w j)) := by
    funext z
    simp only [dotProduct]
  rw [heq]
  exact Finset.measurable_sum _ (fun j _ =>
    Measurable.mul (measurable_pi_apply j) measurable_const)

/-- Single-row marginal: for unit `w`, `Z ⬝ᵥ w ~ N(0,1)`.
Via a Householder reflection sending `w` to `e₁` plus the repo's
unconditional rotation invariance (`gaussianVectorLaw_rotation_uncond`). -/
theorem dsSingleRow_marginal (d : ℕ) (w : Vector d) (hw : euclidNorm w = 1) :
    Measure.map (fun z => dotProduct z w) (gaussianVectorLaw d)
      = gaussianReal 0 1 := by
  by_cases hd : d = 0
  · subst hd
    exfalso
    have hsum : (∑ i : Fin 0, (w i) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
    have h0 : euclidNorm w = 0 := by simp only [euclidNorm, hsum, Real.sqrt_zero]
    rw [hw] at h0
    exact one_ne_zero h0
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
    set e₀ : Fin m.succ := ⟨0, Nat.zero_lt_succ m⟩ with he₀
    set e₁ : Vector m.succ := fun j => if j = e₀ then 1 else 0 with he₁
    set v : Vector m.succ := w - e₁ with hv
    set s : ℝ := dotProduct v v with hs
    set c : ℝ := 2 / s with hc
    set o : Matrix (Fin m.succ) (Fin m.succ) ℝ := Matrix.vecMulVec v v with ho
    set H : Matrix (Fin m.succ) (Fin m.succ) ℝ := 1 - c • o with hH
    have hww : dotProduct w w = 1 := by
      rw [dotProduct_self_eq_euclidNorm_sq, hw]
      norm_num
    have he00 : e₁ e₀ = 1 := by simp only [he₁, if_pos rfl]
    have hsum1 : ∀ f : Vector m.succ, dotProduct e₁ f = f e₀ := by
      intro f
      have h0 : ∀ b ∈ (Finset.univ : Finset (Fin m.succ)),
          b ≠ e₀ → e₁ b * f b = 0 := by
        intro j _ hne
        have hj : e₁ j = 0 := by simp only [he₁, if_neg hne]
        rw [hj, zero_mul]
      have h1 : e₀ ∉ (Finset.univ : Finset (Fin m.succ))
          → e₁ e₀ * f e₀ = 0 :=
        fun h => absurd (Finset.mem_univ e₀) h
      have hmain : (∑ j ∈ (Finset.univ : Finset (Fin m.succ)), e₁ j * f j)
          = e₁ e₀ * f e₀ :=
        Finset.sum_eq_single e₀ h0 h1
      simp only [dotProduct]
      rw [hmain, he00, one_mul]
    have hsum2 : ∀ f : Vector m.succ, dotProduct f e₁ = f e₀ := by
      intro f
      have h0 : ∀ b ∈ (Finset.univ : Finset (Fin m.succ)),
          b ≠ e₀ → f b * e₁ b = 0 := by
        intro j _ hne
        have hj : e₁ j = 0 := by simp only [he₁, if_neg hne]
        rw [hj, mul_zero]
      have h1 : e₀ ∉ (Finset.univ : Finset (Fin m.succ))
          → f e₀ * e₁ e₀ = 0 :=
        fun h => absurd (Finset.mem_univ e₀) h
      have hmain : (∑ j ∈ (Finset.univ : Finset (Fin m.succ)), f j * e₁ j)
          = f e₀ * e₁ e₀ :=
        Finset.sum_eq_single e₀ h0 h1
      simp only [dotProduct]
      rw [hmain, he00, mul_one]
    have hee : dotProduct e₁ e₁ = 1 := by
      rw [hsum1 e₁]
      exact he00
    have hs_eq : s = 2 - 2 * w e₀ := by
      rw [hs, hv, sub_dotProduct, dotProduct_sub, dotProduct_sub, hww,
        hsum2 w, hsum1 w, hee]
      ring
    have ht : dotProduct v w = 1 - w e₀ := by
      rw [hv, sub_dotProduct, hww, hsum1 w]
    obtain ⟨Q, hQ, hQw⟩ : ∃ Q : Matrix (Fin m.succ) (Fin m.succ) ℝ,
        Qᵀ * Q = 1 ∧ Q *ᵥ w = e₁ := by
      by_cases hwe₁ : w = e₁
      · refine ⟨1, ?_, ?_⟩
        · rw [Matrix.transpose_one]
          exact mul_one _
        · rw [Matrix.one_mulVec]
          exact hwe₁
      · have hv0 : v ≠ 0 := by
          intro h
          apply hwe₁
          rw [hv] at h
          exact sub_eq_zero.mp h
        have hs0 : s ≠ 0 := by
          intro h
          rw [hs] at h
          exact hv0 (dotProduct_self_eq_zero.mp h)
        have hoo : o * o = s • o := by
          rw [ho, hs, Matrix.vecMulVec_mul, Matrix.vecMul_vecMulVec,
            Matrix.vecMulVec_smul]
        have haa : (c • o) * (c • o) = ((c * c) * s) • o := by
          rw [smul_mul_assoc, mul_smul_comm, hoo, smul_smul, smul_smul]
        have hsq : (c * c) * s = 2 * c := by
          have hcs : c * s = 2 := by
            rw [hc]
            exact div_mul_cancel₀ 2 hs0
          calc (c * c) * s = c * (c * s) := by ring
            _ = c * 2 := by rw [hcs]
            _ = 2 * c := by ring
        have hHH : H * H = 1 := by
          have h2 : (2 * c) • o = c • o + c • o := by
            have hcc : (2 : ℝ) * c = c + c := by ring
            rw [hcc, add_smul]
          simp only [hH, sub_mul, mul_sub, mul_one, one_mul, haa, hsq, h2]
          abel
        have hHT : Hᵀ = H := by
          have hoT : oᵀ = o := by simp only [ho, Matrix.transpose_vecMulVec]
          simp only [hH, Matrix.transpose_sub, Matrix.transpose_one,
            Matrix.transpose_smul, hoT]
        have hQH : Hᵀ * H = 1 := by rw [hHT, hHH]
        have hs2t : s = 2 * dotProduct v w := by rw [hs_eq, ht]; ring
        have hct : c * dotProduct v w = 1 := by
          have ht0 : dotProduct v w ≠ 0 := by
            intro hcon
            apply hs0
            rw [hs2t, hcon, mul_zero]
          calc c * dotProduct v w = 2 * dotProduct v w / s := by
                rw [hc]; ring
            _ = s / s := by rw [hs2t]
            _ = 1 := div_self hs0
        have how : o *ᵥ w = dotProduct v w • v := by
          rw [ho]
          exact rank_one_mulVec v w
        have hHw : H *ᵥ w = e₁ := by
          have h1 : H *ᵥ w = w - (c * dotProduct v w) • v := by
            rw [hH, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
              how, smul_smul]
          rw [h1, hct, one_smul, hv]
          abel
        exact ⟨H, hQH, hHw⟩
    have hfun : (fun z : Vector m.succ => dotProduct z w)
        = (fun y => dotProduct y e₁) ∘ (fun z => Q *ᵥ z) := by
      funext z
      show dotProduct z w
        = ((fun y => dotProduct y e₁) ∘ (fun z => Q *ᵥ z)) z
      simp only [Function.comp_apply]
      rw [← hQw, dotProduct_comm (Q *ᵥ z) (Q *ᵥ w), Matrix.dotProduct_mulVec,
        ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ,
        Matrix.one_mulVec, dotProduct_comm w z]
    have hQmeas : Measurable (fun z : Vector m.succ => Q *ᵥ z) :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    have hgmeas : Measurable (fun y : Vector m.succ => dotProduct y e₁) := by
      have heq : (fun y : Vector m.succ => dotProduct y e₁)
          = (fun y => ∑ j, (y j) * (e₁ j)) := by
        funext y
        simp only [dotProduct]
      rw [heq]
      exact Finset.measurable_sum _ (fun j _ =>
        Measurable.mul (measurable_pi_apply j) measurable_const)
    have hrot := gaussianVectorLaw_rotation_uncond m.succ Q hQ
    calc Measure.map (fun z => dotProduct z w) (gaussianVectorLaw m.succ)
        = Measure.map ((fun y => dotProduct y e₁) ∘ (fun z => Q *ᵥ z))
            (gaussianVectorLaw m.succ) := by rw [hfun]
      _ = Measure.map (fun y => dotProduct y e₁)
            (Measure.map (fun z => Q *ᵥ z) (gaussianVectorLaw m.succ)) :=
          (Measure.map_map hgmeas hQmeas).symm
      _ = Measure.map (fun y => dotProduct y e₁)
            (gaussianVectorLaw m.succ) := by rw [hrot]
      _ = Measure.map (fun y => y e₀) (gaussianVectorLaw m.succ) := by
          have hye : (fun y : Vector m.succ => dotProduct y e₁)
              = (fun y => y e₀) :=
            funext (fun y => hsum2 y)
          rw [hye]
      _ = gaussianReal 0 1 := gaussianCoordinate_map e₀

/-- Joint law: for unit `w`, the `n` row inner products are i.i.d. N(0,1).
Row independence comes from `iIndepFun_pi` on the product sample law. -/
theorem dsGap_marginal_proof : dsGap_marginal := by
  intro d n w hw
  have hfmeas : Measurable (fun z : Vector d => dotProduct z w) :=
    dsInnerSingle_measurable w
  have hcomp : iIndepFun
      (fun i : Fin n => fun x : Sample d n => dotProduct (x i) w)
      (gaussianSampleLaw d n) :=
    iIndepFun_pi
      (X := fun _ : Fin n => (fun z : Vector d => dotProduct z w))
      (fun _ => hfmeas.aemeasurable)
  have hmap : Measure.map (fun x : Sample d n => fun i => dotProduct (x i) w)
      (gaussianSampleLaw d n)
      = Measure.pi (fun i => Measure.map
        (fun x : Sample d n => dotProduct (x i) w) (gaussianSampleLaw d n)) :=
    iIndepFun.map_fun_eq_pi_map
      (fun i => (hfmeas.comp (measurable_pi_apply i)).aemeasurable) hcomp
  have hfac : ∀ i : Fin n, Measure.map
      (fun x : Sample d n => dotProduct (x i) w) (gaussianSampleLaw d n)
      = gaussianReal 0 1 := by
    intro i
    have hfi : (fun x : Sample d n => dotProduct (x i) w)
        = (fun z : Vector d => dotProduct z w)
          ∘ (fun x : Sample d n => x i) := by
      funext x
      rfl
    rw [hfi, ← Measure.map_map hfmeas (measurable_pi_apply i),
      gaussianRow_map i, dsSingleRow_marginal d w hw]
  have hds : dsInner d n w
      = (fun x : Sample d n => fun i => dotProduct (x i) w) := rfl
  rw [hds, hmap]
  simp only [hfac]

/-- Per-center tail, fully unconditional: all three gaps discharged. -/
theorem dsPerCenterTail_theorem : dsPerCenterTail :=
  dsPerCenterTail_of_marginal dsGap_marginal_proof

end GaussianEllipsoid

