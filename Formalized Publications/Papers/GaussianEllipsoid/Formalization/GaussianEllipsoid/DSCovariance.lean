/-
Track B (Davidson–Szarek covariance): candidate assembly file.

- Imports (never re-proves) the net→opnorm transfer
  `opNorm_le_net_max_quadratic` (Discretize.lean) and the union bound
  `prob_iUnion_le_card_smul` (UnionNet.lean).
- `dsNetCard` (eps-net existence + (1+2/eps)^d cardinality),
  `dsPerCenterTail` (per-center Laurent–Massart tail), `dsSqueeze`
  (transfer+net limit, proved as a sketch in DS.md §7), and
  `dsVarUpper`/`dsVarLower` (DS-II.13 variational tails) are explicit
  external premises in the repo's ExternalInputs style; see DS.md for
  proofs, probe evidence, and the constant analysis.
- Proves: per-center in-ball reduction, exp arithmetic, the
  computed-constants net assembly (`dsNetCovarianceComputed`, eps=1/4),
  and the EXACT `davidsonSzarekCovariance` from squeeze + variational
  tails (`davidsonSzarekCovariance_of_variational`).
-/

import Mathlib
import GaussianEllipsoid.BelowObjects
import GaussianEllipsoid.Discretize
import GaussianEllipsoid.UnionNet

noncomputable section

namespace GaussianEllipsoid

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ### External premises (repo-ExternalInputs style) -/

/-- Eps-net existence + cardinality for the Euclidean unit ball.
Provenance: volume comparison (greedy in-ball packing + Lebesgue
scaling); full proof in DS.md §4. -/
def dsNetCard : Prop :=
  ∀ (d : Nat) {eps : ℝ}, 0 < eps →
    ∃ (N : ℕ) (v : Fin N → Vector d),
      (N : ℝ) ≤ Nat.ceil ((1 + 2 / eps) ^ d)
      ∧ (∀ k, euclidNorm (v k) ≤ 1)
      ∧ ∀ u : Vector d, euclidNorm u ≤ 1 → ∃ k, euclidNorm (u - v k) ≤ eps

/-- Per-center Laurent–Massart tail for a unit vector: for fixed unit
`w`, `quadratic (Σ̂ - I) w` averages `n` i.i.d. centered χ²₁ variables.
Needs Gaussian marginal stability (missing in Mathlib, probe-verified);
see DS.md §5. -/
def dsPerCenterTail : Prop :=
  ∀ (d n : Nat) (w : Vector d), euclidNorm w = 1 → 0 < n →
    ∀ (t x : ℝ), 0 ≤ x → 2 * Real.sqrt (x / (n : ℝ)) + 2 * x / (n : ℝ) ≤ t →
      (gaussianSampleLaw d n) {z | t < |quadratic (sampleCovariance z - 1) w|}
        ≤ ENNReal.ofReal (2 * Real.exp (-x))

/-- Variational eigenvalues (no spectral theory needed). -/
def dsBall (d : Nat) : Set (Vector d) := {u | euclidNorm u ≤ 1}

def dsLamMax {d : Nat} (A : Square d) : ℝ := sSup (quadratic A '' dsBall d)

def dsLamMin {d : Nat} (A : Square d) : ℝ := sInf (quadratic A '' dsBall d)

def dsQuadAbsSup {d : Nat} (A : Square d) : ℝ :=
  sSup ((fun u => |quadratic A u|) '' dsBall d)

/-- Squeeze limit: transfer + nets at `eps → 0` give the sharp variational
bound. Proved as a Lean sketch in DS.md §7. -/
def dsSqueeze : Prop :=
  ∀ {d : Nat} (A : Square d), A.IsSymm →
    matrixOpNorm A ≤ max (dsLamMax A) (-dsLamMin A)

/-- DS-II.13 upper content, stated variationally on `Σ̂ - I` at the EXACT
BelowObjects threshold (`s_max(X/√n)² - 1 = lamMax(Σ̂ - I)`; cf. the repo's
`davidsonSzarekMinSingular`). -/
def dsVarUpper : Prop :=
  ∀ (d n : Nat), 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
    (gaussianSampleLaw d n)
        {x | 4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
          < dsLamMax (sampleCovariance x - 1)}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / 2))

/-- DS-II.13 lower content, stated variationally. -/
def dsVarLower : Prop :=
  ∀ (d n : Nat), 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
    (gaussianSampleLaw d n)
        {x | 4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
          < -dsLamMin (sampleCovariance x - 1)}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / 2))

/-- Per-center threshold at `x = 3d` (see DS.md §6). -/
def dsPerCenterT (d n : Nat) : ℝ :=
  2 * Real.sqrt (3 * (d : ℝ) / (n : ℝ)) + 2 * (3 * (d : ℝ)) / (n : ℝ)

/-- Net-route threshold at `eps = 1/4` (transfer factor `16/7`). -/
def dsNetThreshold (d n : Nat) : ℝ := dsPerCenterT d n * (16 / 7)

/-- `(7/16)·T = t_c`: the transfer factor cancels by construction. -/
theorem dsRhoT_eq (d n : Nat) :
    (7 / 16 : ℝ) * dsNetThreshold d n = dsPerCenterT d n := by
  unfold dsNetThreshold
  ring

/-! ### Sample covariance symmetry -/

theorem sampleCovariance_symm_ds {d n : Nat} (x : Sample d n) :
    (sampleCovariance x).IsSymm := by
  unfold sampleCovariance Matrix.IsSymm
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact Matrix.transpose_vecMulVec _ _

theorem sampleCovariance_sub_one_symm_ds {d n : Nat} (x : Sample d n) :
    (sampleCovariance x - 1).IsSymm :=
  (sampleCovariance_symm_ds x).sub Matrix.isSymm_one

/-! ### Per-center reduction: in-ball points from unit vectors -/

theorem dsPerCenter_inball {d n : Nat} (hpc : dsPerCenterTail) (hn : 0 < n)
    {v : Vector d} (hv : euclidNorm v ≤ 1)
    {t x : ℝ} (hx : 0 ≤ x)
    (ht : 2 * Real.sqrt (x / (n : ℝ)) + 2 * x / (n : ℝ) ≤ t) :
    (gaussianSampleLaw d n) {z | t < |quadratic (sampleCovariance z - 1) v|}
      ≤ ENNReal.ofReal (2 * Real.exp (-x)) := by
  have ht0 : (0 : ℝ) ≤ t := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hsq : (0 : ℝ) ≤ Real.sqrt (x / (n : ℝ)) := Real.sqrt_nonneg _
    have hxn : (0 : ℝ) ≤ x / (n : ℝ) := div_nonneg hx hn0
    have heq : (2 : ℝ) * x / (n : ℝ) = 2 * (x / (n : ℝ)) := by ring
    linarith [ht, hsq, hxn, heq]
  by_cases h0 : v = 0
  · subst h0
    calc (gaussianSampleLaw d n)
            {z : Sample d n | t < |quadratic (sampleCovariance z - 1) 0|}
        ≤ (gaussianSampleLaw d n) ∅ := by
          apply measure_mono
          intro z hz
          simp only [Set.mem_ofPred_eq, quadratic_zero_vec, abs_zero] at hz
          exact False.elim (not_lt.mpr ht0 hz)
      _ = 0 := measure_empty
      _ ≤ _ := zero_le
  · -- `w := ‖v‖⁻¹ • v` is a unit vector; `|quad v| ≤ |quad w|`.
    have hne0 : euclidNorm v ≠ 0 := fun h => h0 (euclidNorm_eq_zero_iff.mp h)
    set w : Vector d := (euclidNorm v)⁻¹ • v with hw
    have hwunit : euclidNorm w = 1 := by
      rw [hw, euclidNorm_smul,
        abs_of_nonneg (inv_nonneg.mpr (euclidNorm_nonneg v)),
        inv_mul_cancel₀ hne0]
    have hdecomp : v = euclidNorm v • w := by
      rw [hw, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hne0, one_smul]
    have hsq1 : (euclidNorm v) ^ 2 ≤ 1 := by
      nlinarith [hv, euclidNorm_nonneg v]
    have hpt : ∀ z : Sample d n,
        |quadratic (sampleCovariance z - 1) v|
          ≤ |quadratic (sampleCovariance z - 1) w| := by
      intro z
      have hq : quadratic (sampleCovariance z - 1) v
          = (euclidNorm v) ^ 2 * quadratic (sampleCovariance z - 1) w := by
        conv_lhs => rw [hdecomp]
        exact quadratic_vec_smul _ _ _
      rw [hq, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc (euclidNorm v) ^ 2 * |quadratic (sampleCovariance z - 1) w|
          ≤ 1 * |quadratic (sampleCovariance z - 1) w| :=
            mul_le_mul_of_nonneg_right hsq1 (abs_nonneg _)
        _ = _ := one_mul _
    calc (gaussianSampleLaw d n)
            {z | t < |quadratic (sampleCovariance z - 1) v|}
        ≤ (gaussianSampleLaw d n)
            {z | t < |quadratic (sampleCovariance z - 1) w|} := by
          apply measure_mono
          intro z hz
          exact lt_of_lt_of_le hz (hpt z)
      _ ≤ _ := hpc d n w hwunit hn t x hx ht

/-! ### Exponential arithmetic: `9^d · e^{-3d} ≤ e^{-d/2}` -/

/-- `e^{1/2} ≥ 1.6`, via `(e^{1/2})² = e ≥ 2.71 ≥ 2.56`. -/
theorem dsExpHalf_ge : (1.6 : ℝ) ≤ Real.exp (1 / 2) := by
  have hsq : ((1.6 : ℝ)) ^ 2 ≤ (Real.exp (1 / 2)) ^ 2 := by
    have hexp : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      norm_num
    have h271 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith [hexp, h271]
  have hnn : (0 : ℝ) ≤ Real.exp (1 / 2) := Real.exp_nonneg _
  have habs := abs_le_of_sq_le_sq hsq hnn
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.6)] at habs
  exact habs

/-- `9 ≤ e^{5/2} = e·e·e^{1/2}`. -/
theorem dsNine_le_exp52 : (9 : ℝ) ≤ Real.exp (5 / 2) := by
  have h1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 := dsExpHalf_ge
  have hehnn : (0 : ℝ) ≤ Real.exp (1 / 2) := Real.exp_nonneg _
  have h3 : (2.71 * 2.71 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h1)
      (show (0 : ℝ) ≤ Real.exp 1 + 2.71 by linarith [Real.exp_nonneg (1 : ℝ)])]
  have h4 : (2.71 * 2.71 * 1.6 : ℝ)
      ≤ (Real.exp 1 * Real.exp 1) * Real.exp (1 / 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) hehnn,
      mul_nonneg (show (0 : ℝ) ≤ 2.71 * 2.71 by norm_num) (sub_nonneg.mpr h2)]
  have hex52 : ((5 / 2 : ℝ)) = 1 + 1 + 1 / 2 := by norm_num
  rw [hex52, Real.exp_add, Real.exp_add]
  have hconst : (2.71 * 2.71 * 1.6 : ℝ) = 11.75056 := by norm_num
  rw [hconst] at h4
  linarith

/-- Union-bound endgame: `9^d · 2e^{-3d} ≤ 2e^{-d/2}`, by induction. -/
theorem dsNinePowMulExp (d : ℕ) :
    (9 : ℝ) ^ d * (2 * Real.exp (-(3 * (d : ℝ)))) ≤ 2 * Real.exp (-(d : ℝ) / 2) := by
  induction d with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, mul_zero, neg_zero, zero_div,
        Real.exp_zero, mul_one, one_mul]
      exact le_rfl
  | succ d ih =>
      have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
      have hexp3 : (-(3 * ((d : ℝ) + 1))) = (-(3 * (d : ℝ))) + (-3) := by ring
      have hexpH : (-((d : ℝ) + 1) / 2) = (-(d : ℝ) / 2) + (-(1 / 2)) := by ring
      have hLHS : (9 : ℝ) ^ (d + 1) * (2 * Real.exp (-(3 * ((d : ℝ) + 1))))
          = (9 * Real.exp (-3)) * ((9 : ℝ) ^ d * (2 * Real.exp (-(3 * (d : ℝ))))) := by
        rw [pow_succ, hexp3, Real.exp_add]; ring
      have hRHS : Real.exp (-(1 / 2 : ℝ)) * (2 * Real.exp (-(d : ℝ) / 2))
          = 2 * Real.exp (-((d : ℝ) + 1) / 2) := by
        rw [hexpH, Real.exp_add]; ring
      have h9e : (9 : ℝ) * Real.exp (-3) ≤ Real.exp (-(1 / 2 : ℝ)) := by
        have h52 : ((5 / 2 : ℝ)) + (-3) = -(1 / 2) := by norm_num
        calc (9 : ℝ) * Real.exp (-3)
            ≤ Real.exp (5 / 2) * Real.exp (-3) :=
              mul_le_mul_of_nonneg_right dsNine_le_exp52 (Real.exp_nonneg _)
          _ = Real.exp (-(1 / 2 : ℝ)) := by rw [← Real.exp_add, h52]
      have hnn1 : (0 : ℝ) ≤ 9 * Real.exp (-3) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      have hnn2 : (0 : ℝ) ≤ 2 * Real.exp (-(d : ℝ) / 2) :=
        mul_nonneg (by norm_num) (Real.exp_nonneg _)
      rw [hcast, hLHS]
      calc (9 * Real.exp (-3)) * ((9 : ℝ) ^ d * (2 * Real.exp (-(3 * (d : ℝ)))))
          ≤ (9 * Real.exp (-3)) * (2 * Real.exp (-(d : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left ih hnn1
        _ ≤ Real.exp (-(1 / 2 : ℝ)) * (2 * Real.exp (-(d : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right h9e hnn2
        _ = 2 * Real.exp (-((d : ℝ) + 1) / 2) := hRHS

/-! ### Computed-constants net assembly (eps = 1/4) -/

theorem dsNetCovarianceComputed (hnet : dsNetCard) (hpc : dsPerCenterTail) :
    ∀ (d n : Nat), 0 < d → 0 < n → (d : ℝ) ≤ (n : ℝ) →
      ((gaussianSampleLaw d n)
        {x | dsNetThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
        ≤ 2 * Real.exp (-(d : ℝ) / 2) := by
  intro d n hd hn hdn
  obtain ⟨N, v, hcard, hinball, hnet⟩ :=
    hnet d (show (0 : ℝ) < (1 / 4 : ℝ) by norm_num)
  have h9 : (1 : ℝ) + 2 / (1 / 4 : ℝ) = 9 := by norm_num
  rw [h9] at hcard
  have h9ceil : Nat.ceil ((9 : ℝ) ^ d) = (9 : ℝ) ^ d := by
    have hnat : (9 : ℝ) ^ d = ((9 ^ d : ℕ) : ℝ) := by norm_cast
    rw [hnat, Nat.ceil_natCast]
  rw [h9ceil] at hcard
  have heps0 : (0 : ℝ) ≤ (1 / 4 : ℝ) := by norm_num
  have heps1 : 2 * (1 / 4 : ℝ) + (1 / 4 : ℝ) ^ 2 < 1 := by norm_num
  have hρ : (1 : ℝ) - 2 * (1 / 4 : ℝ) - (1 / 4 : ℝ) ^ 2 = 7 / 16 := by norm_num
  have hper : ∀ k : Fin N,
      (gaussianSampleLaw d n)
          {z | dsPerCenterT d n < |quadratic (sampleCovariance z - 1) (v k)|}
        ≤ ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ)))) := by
    intro k
    exact dsPerCenter_inball hpc hn (hinball k)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by unfold dsPerCenterT; exact le_rfl)
  have hsymm : ∀ x : Sample d n, (sampleCovariance x - 1).IsSymm :=
    fun x => sampleCovariance_sub_one_symm_ds x
  have hsub : {x : Sample d n |
        dsNetThreshold d n < matrixOpNorm (sampleCovariance x - 1)}
      ⊆ ⋃ k : Fin N,
        {z : Sample d n |
          dsPerCenterT d n < |quadratic (sampleCovariance z - 1) (v k)|} := by
    intro x hx
    obtain ⟨k, hk⟩ := opNorm_le_net_max_quadratic (hsymm x) heps0 heps1 hnet
    rw [hρ] at hk
    have hlt : dsNetThreshold d n
        < |quadratic (sampleCovariance x - 1) (v k)| / (7 / 16) :=
      lt_of_lt_of_le hx hk
    have hmul := mul_lt_mul_of_pos_right hlt (by norm_num : (0 : ℝ) < 7 / 16)
    have heq : (|quadratic (sampleCovariance x - 1) (v k)| / (7 / 16 : ℝ)) * (7 / 16)
        = |quadratic (sampleCovariance x - 1) (v k)| := by
      rw [div_eq_mul_inv, mul_assoc,
        inv_mul_cancel₀ (by norm_num : (7 / 16 : ℝ) ≠ 0), mul_one]
    have hρT := dsRhoT_eq d n
    have hmem : dsPerCenterT d n < |quadratic (sampleCovariance x - 1) (v k)| := by
      have hcomm : dsNetThreshold d n * (7 / 16)
          = (7 / 16) * dsNetThreshold d n := mul_comm _ _
      linarith [hmul, heq, hρT, hcomm]
    exact Set.mem_iUnion.mpr ⟨k, hmem⟩
  have hU := prob_iUnion_le_card_smul (gaussianSampleLaw d n)
    (fun k : Fin N => {z : Sample d n |
      dsPerCenterT d n < |quadratic (sampleCovariance z - 1) (v k)|})
    (fun k => hper k)
  have hle : (gaussianSampleLaw d n)
        {x : Sample d n |
          dsNetThreshold d n < matrixOpNorm (sampleCovariance x - 1)}
      ≤ (N : ℕ) • ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ)))) :=
    (measure_mono hsub).trans hU
  have hsum : (∑ _k ∈ (Finset.univ : Finset (Fin N)),
        ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ)))))
      = (N : ℕ) • ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ)))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← hsum] at hle
  have hbdd : (0 : ℝ) ≤ 2 * Real.exp (-(3 * (d : ℝ))) :=
    mul_nonneg (by norm_num) (Real.exp_nonneg _)
  have hfin : (∑ _k ∈ (Finset.univ : Finset (Fin N)),
        ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ))))) ≠ ∞ := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hbdd)]
    exact ENNReal.ofReal_ne_top
  have htoReal : ((gaussianSampleLaw d n)
        {x : Sample d n |
          dsNetThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ (N : ℝ) * (2 * Real.exp (-(3 * (d : ℝ)))) := by
    calc ((gaussianSampleLaw d n)
            {x : Sample d n |
              dsNetThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
        ≤ (∑ _k ∈ (Finset.univ : Finset (Fin N)),
            ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ))))).toReal :=
          ENNReal.toReal_mono hfin hle
      _ = ∑ _k ∈ (Finset.univ : Finset (Fin N)),
          (ENNReal.ofReal (2 * Real.exp (-(3 * (d : ℝ))))).toReal :=
          ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)
      _ = ∑ _k ∈ (Finset.univ : Finset (Fin N)),
          (2 * Real.exp (-(3 * (d : ℝ)))) :=
          Finset.sum_congr rfl fun _ _ => ENNReal.toReal_ofReal hbdd
      _ = (N : ℝ) * (2 * Real.exp (-(3 * (d : ℝ)))) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ((gaussianSampleLaw d n)
          {x : Sample d n |
            dsNetThreshold d n < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ (N : ℝ) * (2 * Real.exp (-(3 * (d : ℝ)))) := htoReal
    _ ≤ (9 : ℝ) ^ d * (2 * Real.exp (-(3 * (d : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcard hbdd
    _ ≤ 2 * Real.exp (-(d : ℝ) / 2) := dsNinePowMulExp d

/-! ### Exact assembly from squeeze + variational tails -/

theorem davidsonSzarekCovariance_of_variational (hsq : dsSqueeze)
    (hU : dsVarUpper) (hL : dsVarLower) : davidsonSzarekCovariance := by
  unfold davidsonSzarekCovariance
  intro d n hd hn hdn
  have hsymm : ∀ x : Sample d n, (sampleCovariance x - 1).IsSymm :=
    fun x => sampleCovariance_sub_one_symm_ds x
  have hU' := hU d n hd hn hdn
  have hL' := hL d n hd hn hdn
  have hsub : {x : Sample d n |
        4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
          < matrixOpNorm (sampleCovariance x - 1)}
      ⊆ {x : Sample d n |
          4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
            < dsLamMax (sampleCovariance x - 1)}
        ∪ {x : Sample d n |
          4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
            < -dsLamMin (sampleCovariance x - 1)} := by
    intro x hx
    have hle := hsq _ (hsymm x)
    have hlt : 4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
        < max (dsLamMax (sampleCovariance x - 1))
          (-dsLamMin (sampleCovariance x - 1)) :=
      lt_of_lt_of_le hx hle
    rcases lt_max_iff.mp hlt with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : (gaussianSampleLaw d n)
        {x : Sample d n |
          4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
            < matrixOpNorm (sampleCovariance x - 1)}
      ≤ ENNReal.ofReal (Real.exp (-(d : ℝ) / 2))
        + ENNReal.ofReal (Real.exp (-(d : ℝ) / 2)) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hU' hL'))
  have hexp : (0 : ℝ) ≤ Real.exp (-(d : ℝ) / 2) := Real.exp_nonneg _
  have hfin : ENNReal.ofReal
      (Real.exp (-(d : ℝ) / 2) + Real.exp (-(d : ℝ) / 2)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have heq : Real.exp (-(d : ℝ) / 2) + Real.exp (-(d : ℝ) / 2)
      = 2 * Real.exp (-(d : ℝ) / 2) := by ring
  calc ((gaussianSampleLaw d n)
          {x : Sample d n |
            4 * Real.sqrt ((d : ℝ) / (n : ℝ)) + 4 * (d : ℝ) / (n : ℝ)
              < matrixOpNorm (sampleCovariance x - 1)}).toReal
      ≤ (ENNReal.ofReal (Real.exp (-(d : ℝ) / 2))
          + ENNReal.ofReal (Real.exp (-(d : ℝ) / 2))).toReal :=
        ENNReal.toReal_mono
          (by rw [← ENNReal.ofReal_add hexp hexp]; exact hfin) hle
    _ = 2 * Real.exp (-(d : ℝ) / 2) := by
        have hnn : (0 : ℝ) ≤ 2 * Real.exp (-(d : ℝ) / 2) :=
          mul_nonneg (by norm_num) (Real.exp_nonneg _)
        rw [← ENNReal.ofReal_add hexp hexp, heq]
        exact ENNReal.toReal_ofReal hnn

#print axioms dsNetCovarianceComputed
#print axioms davidsonSzarekCovariance_of_variational

end GaussianEllipsoid
